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
    [devtools.core :as devtools])
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
                                   [config])))]
    (assoc world :configs new-configs
                 :now (:entry-time config))))

(defn make-world []
  (let [ids #{;:ga :gb :gc :gd :ge
              :m
              }
        walls #{[0 0 256 8]
                [0 8 8 16]
                [96 8 8 16]
                [160 8 8 16]}
        objects [
                 ;(util/goomba :ga 8 8 16 :right ids walls)
                 ;(util/goomba :gb 32 8 16 :right ids walls)
                 ;(util/goomba :gc 12 35 16 :falling-right ids walls)
                 ;(util/goomba :gd 64 8 16 :left ids walls)
                 ;(util/goomba :ge 96 32 16 :right ids walls)
                 (util/mario :m {:x 200 :y 8 :v/x 0 :v/y 0} (kw :moving :right) ids walls)]
        obj-dict (heval/init-has objects)
        init-config {:entry-time 0 :inputs #{} :objects obj-dict}]
    (reduce world-append
           {:now             0
            :playing         false
            :pause-on-change false
            :configs         [init-config]
            :walls           walls}
           (first (roll/fixed-playout init-config [[:m :moving-left 1.0] [:m :moving-right 2.0]])))))

(def key-states (atom {:on       #{}
                       :pressed  #{}
                       :released #{}}))

(def seen-polys (atom {}))

(defn next-required-transition-time [ha]
  (if-let [r (first (:required-transitions ha))]
    (iv/start-time (:interval r))
    Infinity))

(defn merge-seen-poly [seen-for-ha ha]
  (let [nv0 (ha/valuation ha)
        nflows (:flows (ha/current-state ha))
        nd (- (next-required-transition-time ha) (:entry-time ha))
        dominator (some (fn [[_ v0 flow d]]
                          (and (= v0 nv0)
                               (= nflows flow)
                               [v0 flow d]))
                        seen-for-ha)]
    (println nv0 nflows nd (ha/extrapolate-flow nv0 nflows nd)
             "subsumed by" dominator (when dominator (apply ha/extrapolate-flow (rest dominator))))
    (if dominator
      seen-for-ha
      (conj seen-for-ha
            [(:id ha) nv0 nflows nd]))))

(defn update-world! [w-atom ufn]
  (swap! w-atom (fn [w]
                  (let [new-w (ufn w)
                        old-configs (or (:configs w) [])
                        new-configs (:configs new-w)]
                    (when (or (empty? @seen-polys)
                              (not= old-configs new-configs))
                      (let [newest (if (< (count old-configs) (count new-configs))
                                     (subvec new-configs (count old-configs))
                                     new-configs)]
                        (println "newest:" (count newest))
                        (swap! seen-polys
                               (fn [seen]
                                 (reduce
                                   (fn [seen new-config]
                                     (reduce
                                       (fn [seen ha]
                                         (let [id (:id ha)
                                               seen-for-ha (get seen id [])
                                               seen-for-ha' (merge-seen-poly seen-for-ha ha)]
                                           (assoc seen id seen-for-ha')))
                                       seen
                                       (vals (:objects new-config))))
                                   seen
                                   newest)
                                 ))
                        nil))
                    new-w))))

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
                                                              [[(:now w) new-now] @key-states]
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

(defn poly-str [h scale [_ha-id v0 flow duration]]
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
                                  (let [[s _e] (iv/first-subinterval (:interval trans))
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
                  (map (fn [poly] [:polygon {:key    (str poly)
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
                                  (let [[s e] (iv/first-subinterval (:interval trans))
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
  (when (not= @world last-world)
    (set! last-world @world)
    (js/React.render (world-widget world nil) target))
  (.requestAnimationFrame js/window #(rererender target)))

(defonce has-run nil)

(defn main []
  ;; conditionally start the app based on whether the #main-app-area
  ;; node is on the page
  (set! has-run true)
  (devtools/enable-feature! :sanity-hints)
  (devtools/install!)
  (if-let [node (.getElementById js/document "main-app-area")]
    (.requestAnimationFrame js/window #(rererender node))))

(when-not has-run
  (main))
