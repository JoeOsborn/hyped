(ns player.core
  (:require
    [sablono.core :as sab :include-macros true]
    [ha.intervals :as iv]
    [player.ha-eval :as heval]
    [ha.ha :as ha :refer [make-ha make-state make-edge
                          make-paired-states kw
                          bumping-transitions
                          unsupported-guard non-bumping-guard]]
    [player.ha-rollout :as roll]
    [player.util :as util]
    [clojure.string :as string]
    [devtools.core :as devtools]
    [clojure.set :as sets])
  (:require-macros
    [devcards.core :refer [defcard deftest]]
    [player.macros :refer [soft-assert]]))

(enable-console-print!)

(defonce last-world nil)

(declare reset-world!)
(defn reload! [_]
  (set! last-world nil)
  (reset-world!))

(defn debug-shown-transitions [ha]
  [(first (:required-transitions ha))])

(set! heval/frame-length (/ 1 30))
(set! heval/time-units-per-frame 10000)
(set! heval/time-unit (/ heval/frame-length heval/time-units-per-frame))
(set! heval/precision 0.01)

(defonce world (atom {}))
(defonce last-time nil)

(defn current-config [world]
  (last (:configs world)))

(defn world-append [world config]
  (let [new-configs (if (>= (:entry-time config) (:entry-time (current-config world)))
                      (conj (:configs world) config)
                      (vec (concat (filter (fn [c] (<= (:entry-time c) (:entry-time config)))
                                           (:configs world))
                                   [config])))
        new-seen (roll/see-config (:seen-configs world) config)]
    (assoc world :configs new-configs
                 :seen-configs new-seen
                 :now (:entry-time config))))

(defn make-world []
  (let [ids #{
              :ga :gb :gc :gd :ge
              :m
              }
        walls #{[0 0 256 8]
                [0 8 8 16]
                [96 8 8 16]
                [160 8 8 16]}
        objects [
                 (util/goomba :ga 8 8 16 :right ids walls)
                 (util/goomba :gb 32 8 16 :right ids walls)
                 (util/goomba :gc 12 35 16 :falling-right ids walls)
                 (util/goomba :gd 64 8 16 :left ids walls)
                 (util/goomba :ge 96 32 16 :right ids walls)
                 (util/mario :m {:x 200 :y 8 :v/x 0 :v/y 0} (kw :idle :right) ids walls)
                 ]
        obj-dict (heval/init-has objects)
        init-config {:entry-time 0 :inputs #{} :objects obj-dict}]
    (reduce world-append
            {:now             0
             :playing         false
             :pause-on-change false
             :configs         [init-config]
             :seen-configs    (roll/see-config #{} init-config)
             :walls           walls}
            []
            #_(first (roll/stabilize-config init-config))
            #_(first (roll/fixed-playout init-config
                                         [[:m :jumping-right 0.5]
                                          [:m :moving-right 3.0]
                                          [:m :idle-right 3.75]
                                          [:m :jumping-right 6.0]
                                          #_[:m :moving-right 10.0]])))))

(def key-states (atom {:on       #{}
                       :pressed  #{}
                       :released #{}}))

(def seen-polys (atom {}))

(defn solve-t-xy [v0 flow vt min-t max-t]
  ; issue: what if there are multiple solutions? just take the first valid one.
  ; find t s.t. x0 + xflow(t) = xt and y0 + yflow(t) = yt
  ; must be same t!
  ; and s.t. <= min-t t max-t
  (let [xt (:x vt)
        yt (:y vt)]
    (if (and (= xt (:x v0))
             (= yt (:y v0)))
      min-t
      (let [; at^2+bt+c = x, plus valid ranges
            x-eqns (ha/flow-equations v0 flow :x)
            ; at^2+bt+c = y
            y-eqns (ha/flow-equations v0 flow :y)
            ; at^2+bt+c-xt = 0
            x-solutions (mapcat (fn [[a b c start end]]
                                  (let [c (- c xt)
                                        roots (ha/find-roots a b c)]
                                    (filter #(<= start % end) roots)))
                                x-eqns)
            y-solutions (mapcat (fn [[a b c start end]]
                                  (let [c (- c yt)
                                        roots (ha/find-roots a b c)]
                                    (filter #(<= start % end) roots)))
                                y-eqns)
            ;_ (println "xs" x-solutions "ys" y-solutions)
            x-solutions-working-for-y (filter #(= (:y (ha/extrapolate-flow v0 flow %))
                                                  yt)
                                              x-solutions)
            y-solutions-working-for-x (filter #(= (:x (ha/extrapolate-flow v0 flow %))
                                                  xt)
                                              y-solutions)

            ;_ (println "xs2" x-solutions-working-for-y "ys2" y-solutions-working-for-x)
            first-soln (first (concat x-solutions-working-for-y y-solutions-working-for-x))]
        (if (some? first-soln)
          (ha/floor-time first-soln
                         heval/time-unit)
          :no-solution)))))

(defn shrink-seen-poly [[nid nstate nv0 nflow nd :as np] [id state v0 flow d :as op]]
  (assert (= nid id))
  (cond
    ; incomparable
    (or (not= nflow flow)
        (not= nstate state)) [np]
    ; exactly covered
    (= np op) []
    :else (let [
                ;_ (println "ne" (ha/extrapolate-flow nv0 nflow nd))
                ;_ (println "oe" (ha/extrapolate-flow v0 flow d))
                ; find t < nd s.t. nv0+nflow(t) = v0
                old-start-in-new-terms (solve-t-xy nv0 nflow
                                                   v0
                                                   0 nd)
                ;_ (println "os-in-nt" old-start-in-new-terms)
                ; find t < nd s.t. v0+flow(nd) = nv0+nflow(t)
                old-end-in-new-terms (solve-t-xy nv0 nflow
                                                 (ha/extrapolate-flow v0
                                                                      flow
                                                                      d)
                                                 0 nd)
                ;_ (println "oe-in-nt" old-end-in-new-terms)
                ; find t < d s.t. v0+flow(t) = nv0
                new-start-in-old-terms (solve-t-xy v0 flow
                                                   nv0
                                                   0 d)
                ;_ (println "ns-in-ot" new-start-in-old-terms)
                ; find t < d s.t. nv0+nflow(nd) = v0+flow(t)
                new-end-in-old-terms (solve-t-xy v0 flow
                                                 (ha/extrapolate-flow nv0
                                                                      nflow
                                                                      nd)
                                                 0 d)
                ;_ (println "ne-in-ot" new-end-in-old-terms)
                ; os-in-new?. is oldp's start inside of np?
                os-in-new? (and (not= old-start-in-new-terms :no-solution)
                                (<= 0 old-start-in-new-terms nd))
                ; oe-in-new?. is oldp's end inside of np?
                oe-in-new? (and (not= old-end-in-new-terms :no-solution)
                                (<= 0 old-end-in-new-terms nd))
                ; ns-in-old? is np's start inside of oldp?
                ns-in-old? (and (not= new-start-in-old-terms :no-solution)
                                (<= 0 new-start-in-old-terms d))
                ; ne-in-old?. is np's end inside of oldp?
                ne-in-old? (and (not= new-end-in-old-terms :no-solution)
                                (<= 0 new-end-in-old-terms d))]
            #_(println "shrink" nid [nv0 nd] "\n" flow "\n" "by" [v0 d] "\n" os-in-new? oe-in-new? "\n" ns-in-old? ne-in-old?)
            (cond
              ; exactly covered
              (and ns-in-old? ne-in-old? os-in-new? oe-in-new?) []
              ; subsumed
              (and ns-in-old? ne-in-old?) []
              ; contains old. we have to either drop old or split new into 2.
              ; but it's OK by me if we just keep old around and don't shrink new.
              ; unfortunately, future shrinks could make new exactly the same as old!
              ; so we have to make one or the other choice.
              ; it's easier to add two than to remove one, so we do that.
              (and os-in-new? oe-in-new?) (do
                                            #_(println "split poly")
                                            (assert (not= old-start-in-new-terms :no-solution))
                                            (assert (not= old-end-in-new-terms :no-solution))
                                            [[nid
                                              nstate
                                              nv0
                                              nflow
                                              old-start-in-new-terms]
                                             [nid
                                              nstate
                                              (ha/extrapolate-flow
                                                nv0
                                                nflow
                                                old-end-in-new-terms)
                                              nflow
                                              (- nd old-end-in-new-terms)]])
              ; overlapping (new start outside, new end inside)
              ; shrink new to just new-start...old-start
              (and (not ns-in-old?) ne-in-old? os-in-new?) (do #_(println "shrink end to" old-start-in-new-terms)
                                                             (assert (not= old-start-in-new-terms :no-solutions))
                                                             [[nid
                                                               nstate
                                                               nv0
                                                               nflow
                                                               old-start-in-new-terms]])
              ; overlapping (new start inside, new end outside)
              ; shrink new to just old-end...new-end
              (and ns-in-old? (not ne-in-old?) oe-in-new?) (do
                                                             #_(println "shrink start to" old-end-in-new-terms)
                                                             (assert (not= old-end-in-new-terms :no-solution))
                                                             [[nid
                                                               nstate
                                                               (ha/extrapolate-flow
                                                                 nv0
                                                                 nflow
                                                                 old-end-in-new-terms)
                                                               nflow
                                                               (- nd old-end-in-new-terms)]])
              ; otherwise, no overlap: just yield the new one unchanged
              :else [np]))))

(defn merge-seen-poly [seen-for-ha ha end-time]
  (assert ha/ha? ha)
  (let [rs (reduce (fn [new-ps old-p]
                     (let [rs (mapcat #(shrink-seen-poly % old-p) new-ps)]
                       (if (empty? rs)
                         (reduced [])
                         rs)))
                   [[(:id ha)
                     (:state ha)
                     (ha/valuation ha)
                     (:flows (ha/current-state ha))
                     (- end-time (:entry-time ha))]]
                   ; reverse it because the new poly is probably similar to more recent polys
                   (reverse seen-for-ha))]
    (apply conj seen-for-ha rs)))

(defn successor-states [config]
  ;(println "successors of" (roll/config-brief config) "\n" (string/join "\n" (second (roll/next-transitions config))))
  (let [[reqs opts] (roll/next-transitions config)]
    (cond
      (and (empty? opts) (empty? reqs)) []
      (empty? opts) [(roll/follow-transition config :required (iv/start (:interval (first reqs))))]
      :else (let [choices (mapcat (fn [o]
                                    (if (= Infinity (iv/end (:interval o)))
                                      [[o (iv/start (:interval o))]]
                                      [[o (iv/start (:interval o))]
                                       [o (iv/end (:interval o))]]))
                                  opts)]
              (map (fn [[opt time]] (roll/follow-transition config opt time))
                   choices)))))

(def unroll-limit 3)

(defn option-desc [{objects :objects}
                   {id :id {edge :index target :target} :transition}
                   k]
  (let [ha (get objects id)]
    (assoc (select-keys ha (concat [:id :state] (:variables ha)))
      :edge edge
      :target target
      :key k)))
(defn option-desc->transition [config {id :id edge :edge}]
  (let [opts (roll/optional-transitions-before config Infinity)]
    (roll/find-move-by-edge opts id edge)))

(def explore-roll-limit 3)

;todo: use seen properly to cache states
(defn explore-nearby [seed-playout explored seen]
  (let [seed-playout (concat [nil] seed-playout [(roll/next-config (last seed-playout))])
        ; _ (println "seed length" (count seed-playout))
        [playouts _ _ explored seen]
        (reduce
          (fn [[playouts path prev-opts explored seen] [prev cur]]
            (let [cur-opts (into #{} (map #(option-desc cur % :start) (second (roll/next-transitions cur))))
                  ;_ (println "explore" (get-in cur [:objects :m :state]) cur-opts)
                  next-path (if (some? prev)
                              (conj path prev)
                              path)
                  removed-opts (filter #(not (contains? explored (assoc % :key :end)))
                                       (sets/difference prev-opts cur-opts))
                  explored (sets/union explored (set (map #(assoc % :key :end) removed-opts)))
                  ; _ (println "removed" removed-opts)
                  [remove-explore-playouts seen] (reduce
                                                   (fn [[ps seen] opt]
                                                     (let [trans (option-desc->transition prev opt)
                                                           time (iv/end (:interval trans))
                                                           succ (roll/follow-transition prev trans time)
                                                           rolled (reduce (fn [cs _]
                                                                            (let [here (last cs)
                                                                                  next (roll/next-config here)]
                                                                              (if (= here next)
                                                                                (reduced cs)
                                                                                (conj cs next))))
                                                                          (conj next-path succ)
                                                                          (range 0 explore-roll-limit))]
                                                       [(conj ps rolled) seen]))
                                                   [[] seen]
                                                   removed-opts)
                  ; _ (println "remove-explore-playouts" (count remove-explore-playouts))
                  added-opts (filter #(not (contains? explored %))
                                     (sets/difference cur-opts prev-opts))
                  ;_ (println "added" added-opts)
                  explored (sets/union explored (set added-opts))
                  [add-explore-playouts seen] (reduce
                                                (fn [[ps seen] opt]
                                                  (let [trans (option-desc->transition cur opt)
                                                        time (+ (:entry-time cur) heval/time-unit)
                                                        succ (roll/follow-transition cur trans time)
                                                        rolled (reduce (fn [cs _]
                                                                         (let [here (last cs)
                                                                               next (roll/next-config here)]
                                                                           (if (= here next)
                                                                             (reduced cs)
                                                                             (conj cs next))))
                                                                       (conj next-path cur succ)
                                                                       (range 0 explore-roll-limit))]
                                                    [(conj ps rolled) seen]))
                                                [[] seen]
                                                added-opts)
                  ; _ (println "add-explore-playouts" (count add-explore-playouts))
                  ]
              ;(println "new playout count:" (count (concat playouts remove-explore-playouts add-explore-playouts)))
              [(concat playouts remove-explore-playouts add-explore-playouts)
               next-path
               cur-opts
               explored
               seen]))
          [[] [] #{} explored seen]
          (zipmap (butlast seed-playout)
                  (rest seed-playout)))]
    [(map rest playouts) explored seen]))

(def explore-rolled-out? true)

(defn update-world! [w-atom ufn]
  (swap! w-atom (fn [w]
                  (let [new-w (ufn w)
                        old-configs (or (:configs w) [])
                        new-configs (or (:configs new-w) old-configs)
                        explored (or (:explored new-w) #{})
                        seen-configs (:seen-configs new-w)
                        last-config (last new-configs)
                        focused-objects #{}]
                    (if (or (empty? @seen-polys)
                            (not (roll/seen-config? (:seen-configs w) last-config)))
                      (let [newest (if (and (not (empty? old-configs))
                                            (< (count old-configs) (count new-configs)))
                                     (concat [(last old-configs)]
                                             (subvec new-configs (count old-configs)))
                                     new-configs)
                            _ (println "roll")
                            [rolled-playout _moves seen-configs] (time (roll/inert-playout (last newest) unroll-limit seen-configs))
                            _ (println "explore")
                            [playouts explored seen-configs] (time (explore-nearby (if explore-rolled-out?
                                                                                     rolled-playout
                                                                                     newest)
                                                                                   explored
                                                                                   seen-configs))
                            playouts (conj playouts rolled-playout)
                            _ (println "explore playouts" (count playouts) (map count playouts))]
                        #_(println "newest:" (count newest) (map :entry-time newest) (map :entry-time playout))
                        (swap! seen-polys
                               (fn [seen]
                                 (println "merge-in")
                                 (time
                                   (reduce
                                     (fn [seen playout]
                                       (let [final-config (last playout)]
                                         (reduce
                                           (fn [seen [prev-config next-config]]
                                             #_(println "pc" (get-in prev-config [:objects :m :state])
                                                        "nc" (get-in next-config [:objects :m :state]))
                                             (if (and false (roll/seen-config? seen-configs prev-config)
                                                      (roll/seen-config? seen-configs next-config))
                                               seen
                                               (reduce
                                                 (fn [seen {id         :id
                                                            state      :state
                                                            entry-time :entry-time
                                                            :as        prev-ha}]
                                                   (if (or (empty? focused-objects)
                                                           (contains? focused-objects id))
                                                     (let [{next-state :state :as next-ha} (get-in next-config [:objects id])
                                                           next-time (if (= next-config final-config)
                                                                       (:entry-time next-config)
                                                                       (:entry-time next-ha))]
                                                       (if (or (not= state next-state)
                                                               (not= entry-time next-time))
                                                         (let [seen-for-ha (get seen id #{})
                                                               seen-for-ha' (merge-seen-poly seen-for-ha prev-ha next-time)]
                                                           (assoc seen id seen-for-ha'))
                                                         seen))
                                                     seen))
                                                 seen
                                                 (vals (:objects prev-config)))))
                                           seen
                                           (zipmap (butlast playout)
                                                   (rest playout)))))
                                     seen
                                     playouts))))
                        (assoc new-w :seen-configs seen-configs
                                     :explored explored))
                      new-w)))))

(defn reset-world! []
  (swap! key-states (fn [_] {:on #{} :pressed #{} :released #{}}))
  (swap! seen-polys (fn [_] {}))
  (update-world! world (fn [_] (make-world))))

(def keycode->keyname
  {37 :left
   39 :right
   38 :up
   40 :down
   90 :run
   88 :jump})

(defn key-handler [evt]
  (let [key (keycode->keyname (.-keyCode evt))
        down? (= (.-type evt) "keydown")]
    (when key
      (println "KH" (.-keyCode evt) key down?)
      (.preventDefault evt)
      (.-stopPropagation evt)
      (swap! key-states (fn [{prev-on :on pressed :pressed released :released :as k}]
                          ; need the extra contains? check so key-repeat doesn't confuse things.
                          (let [just-pressed? (and down?
                                                   (not (contains? prev-on key)))]
                            (assoc k :on (if down? (conj prev-on key)
                                                   (disj prev-on key))
                                     :pressed (if just-pressed?
                                                (conj pressed key)
                                                pressed)
                                     :released (if down?
                                                 released
                                                 (conj released key)))))))))

(set! (.-onkeydown js/window) key-handler)
(set! (.-onkeyup js/window) key-handler)

(defn tick-frame [t]
  (when-not last-time (set! last-time t))
  (assert (>= t last-time) "Non-monotonic time?")
  (let [old-last-time last-time]
    (set! last-time t)
    (.requestAnimationFrame js/window tick-frame)
    (when (:playing @world)
      (update-world! world
                     (fn [w] (let [c (current-config w)
                                   new-now (+ (:now w) (/ (- t old-last-time) 1000))
                                   new-c (heval/update-config c
                                                              new-now
                                                              ; assume all keys held now were held since "then"
                                                              [(iv/interval (:now w) new-now) @key-states]
                                                              100
                                                              0)
                                   new-w (if (not= c new-c)
                                           (world-append w new-c)
                                           w)
                                   new-w (assoc new-w :now new-now)]
                               (swap! key-states (fn [ks] (assoc ks :pressed #{} :released #{})))
                               (if (and (:pause-on-change new-w)
                                        (not= c new-c))
                                 (assoc new-w :playing false)
                                 new-w)))))))

(when (= @world {})
  (.requestAnimationFrame js/window tick-frame)
  (reset-world!))

(def show-transition-thresholds false)

(defn clip [a b c]
  (max a (min b c)))

(defn poly-str [h scale [_ha-id _ha-state v0 flow duration]]
  ; poly-spec is an ha ID, an initial valuation, a flow, and a duration
  (let [left (:x v0)
        right (+ left 16)
        bottom (:y v0)
        top (+ bottom 16)
        {left' :x bottom' :y} (ha/extrapolate-flow v0 flow duration)
        {right' :x top' :y} (ha/extrapolate-flow (merge v0 {:x right :y top}) flow duration)
        h (* h scale)
        flip-x? (< left' left)
        flip-y? (< bottom' bottom)
        points (cond
                 (and flip-x? flip-y?) [[left top] [right top] [right bottom] [right' bottom'] [left' bottom'] [left' top']]
                 flip-x? [[left bottom] [right bottom] [right top] [right' top'] [left' top'] [left' bottom']]
                 flip-y? [[left top] [right top] [right' top'] [right' bottom'] [left' bottom'] [left' top']]
                 :else [[left bottom] [right bottom] [right' bottom'] [right' top'] [left' top'] [left top]])]
    (string/join " " (map (fn [[px py]] (str (* (clip -1000 px 1000) scale) ","
                                             (- h (* (clip -1000 py 1000) scale))))
                          points))))

(defn world-widget [world _owner]
  (let [scale 2
        view-w-val 320
        view-h-val 120
        view-w (str (* scale view-w-val) "px")
        view-h (str (* scale view-h-val) "px")
        wld @world
        has (:objects (current-config wld))
        ct (count has)
        polys (apply concat (vals @seen-polys))]
    (sab/html [:div {:style {:backgroundColor "blue"
                             :width           (str (* scale 320) "px")
                             :height          view-h
                             :position        "relative"
                             :overflow        "hidden"}}
               (when show-transition-thresholds
                 (map (fn [{w :w h :h :as ha}]
                        (when (not (empty? (:required-transitions ha)))
                          [:div
                           (map (fn [trans]
                                  (let [s (iv/start (:interval trans))
                                        ha-s (ha/extrapolate ha s)
                                        sx (* scale (:x ha-s))
                                        sy (* scale (:y ha-s))]
                                    [:div {:style {:width           (str (* scale w) "px") :height (str (* scale h) "px")
                                                   :borderRadius    (str (* scale w) "px")
                                                   :backgroundColor "rgba(165,42,42,0.5)"
                                                   :position        "absolute"
                                                   :left            (str sx "px")
                                                   :bottom          (str sy "px")}}]))
                                (debug-shown-transitions ha))]))
                      (vals has)
                      (range 0 ct)))
               (if (empty? polys)
                 nil
                 [:svg {:width view-w :height view-h :style {:position "absolute"}}
                  (map (fn [poly]
                         [:polygon {:key    (str poly)
                                    :points (poly-str view-h-val scale poly)
                                    :style  {:fill   "rgba(200,255,200,0.25)"
                                             :stroke "none"}}])
                       polys)])
               (map (fn [[x y w h]]
                      [:div {:style {:width           (str (* scale w) "px") :height (str (* scale h) "px")
                                     :backgroundColor "white"
                                     :position        "absolute"
                                     :left            (str (* scale x) "px")
                                     :bottom          (str (* scale y) "px")}}])
                    (:walls wld))
               (map (fn [{x :x y :y w :w h :h :as ha}]
                      [:div
                       [:div {:style {:width           (str (* scale w) "px") :height (str (* scale h) "px")
                                      :borderRadius    (str (* scale w) "px")
                                      :backgroundColor "brown"
                                      :position        "absolute"
                                      :color           "lightgray"
                                      :left            (str (* scale x) "px")
                                      :bottom          (str (* scale y) "px")}}
                        [:div {:style {:width "200px"}}
                         (str (:id ha) " " (:state ha))]]])
                    (map #(ha/extrapolate % (:now wld)) (vals has)))
               (when show-transition-thresholds
                 (map (fn [ha]
                        [:div
                         (when (not (empty? (:required-transitions ha)))
                           (map (fn [trans]
                                  (let [[s e] (iv/start-end (:interval trans))
                                        ha-s (ha/extrapolate ha s)
                                        ha-e (ha/extrapolate ha e)
                                        sx (* scale (:x ha-s))
                                        ex (* scale (:x ha-e))
                                        sy (* scale (:y ha-s))
                                        ey (* scale (:y ha-e))]
                                    [:div {:style {:height          (.max js/Math (.abs js/Math (- sy ey)) 8)
                                                   :width           (.max js/Math (.abs js/Math (- sx ex)) 8)
                                                   :bottom          (.min js/Math sy ey)
                                                   :left            (.min js/Math sx ex)
                                                   :position        "absolute"
                                                   :backgroundColor "grey"
                                                   :pointerEvents   "none"}}
                                     [:div {:style {:position        "absolute"
                                                    :width           "200px"
                                                    :backgroundColor "rgba(255,255,255,0.5)"
                                                    :pointerEvents   "none"}}
                                      (str (:id ha) "-" (:target (:transition trans)))]
                                     [:div {:style {:height          "100%"
                                                    :width           "2px"
                                                    :position        "absolute"
                                                    :left            (if (< sx ex) "0%" "100%")
                                                    :backgroundColor "green"
                                                    :pointerEvents   "none"}}]
                                     [:div {:style {:height          "100%"
                                                    :width           "2px"
                                                    :position        "absolute"
                                                    :left            (if (< sx ex) "100%" "0%")
                                                    :backgroundColor "red"
                                                    :pointerEvents   "none"}}]]))
                                (debug-shown-transitions ha)))])
                      (vals has)
                      (range 0 ct)))
               [:div {:style {:position "absolute"}}
                [:button {:onClick #(swap! world (fn [w] (assoc w :playing (not (:playing w)))))}
                 (if (:playing wld) "PAUSE" "PLAY")]
                [:span {:style {:backgroundColor "lightgrey"}} "Pause on state change?"
                 [:input {:type     "checkbox"
                          :checked  (:pause-on-change wld)
                          :onChange #(swap! world (fn [w] (assoc w :pause-on-change (.-checked (.-target %)))))}]]
                [:button {:onClick #(reset-world!)} "RESET"]
                [:button {:onClick  #(swap! world (fn [w] (let [new-configs (subvec (:configs w) 0 (dec (count (:configs w))))
                                                                c (last new-configs)]
                                                            (assoc w :now (:entry-time c)
                                                                     :configs new-configs
                                                                     :playing false))))
                          :disabled (= 1 (count (:configs wld)))}
                 "BACK"]
                [:button {:onClick #(update-world! world (fn [w] (let [[configs moves] (roll/random-playout (current-config w) 1)
                                                                       ; drop the start config and move
                                                                       configs (rest configs)
                                                                       moves (rest moves)
                                                                       m (last moves)]
                                                                   (println "random move:" m)
                                                                   (reduce world-append w configs))))}
                 "RANDOM MOVE"]
                [:span {:style {:backgroundColor "lightgrey"}} (str (:now wld))]]])))

(defn rererender [target]
  (let [w @world]
    (when (or (not= (:entry-time (current-config w))
                    (:entry-time (current-config last-world)))
              (not= @world last-world))
      (set! last-world @world)
      (js/React.render (world-widget world nil) target)))
  (.requestAnimationFrame js/window #(rererender target)))

(defonce has-run nil)

(devtools/enable-feature! :sanity-hints)
(devtools/install!)

(defn main []
  ;; conditionally start the app based on whether the #main-app-area
  ;; node is on the page
  (set! has-run true)
  (if-let [node (.getElementById js/document "main-app-area")]
    (.requestAnimationFrame js/window #(rererender node))))

(when-not has-run
  (main))
