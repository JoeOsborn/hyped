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
    [player.seen-viz :as seen-viz]
    [player.key-handler :as keys]
    [clojure.string :as string]
    [devtools.core :as devtools]
    [clojure.set :as sets])
  (:require-macros
    [devcards.core :refer [defcard deftest]]
    [player.macros :refer [soft-assert]]))

(defonce has-run nil)
(declare rererender)

(defn main []
  (enable-console-print!)
  (devtools/enable-feature! :sanity-hints)
  (devtools/install!)
  (keys/install-handlers!)
  (set! has-run true)
  ;; conditionally start the app based on whether the #main-app-area
  ;; node is on the page
  (if-let [node (.getElementById js/document "main-app-area")]
    (do
      (.requestAnimationFrame js/window #(rererender node)))))

(when-not has-run
  (main))

(def default-world-desc
  {:width         320
   :height        240
   :camera-width  320
   :camera-height 120
   :walls         #{{:type :white :x 0 :y 0 :w 256 :h 8}
                    {:type :white :x 0 :y 8 :w 8 :h 16}
                    {:type :white :x 96 :y 8 :w 8 :h 16}
                    {:type :white :x 160 :y 8 :w 8 :h 16}}
   :objects       #{{:id    :ga
                     :type  :goomba
                     :state :right
                     :x     8 :y 8}
                    {:id    :gb
                     :type  :goomba
                     :state :right
                     :x     32 :y 8}
                    {:id    :gc
                     :type  :goomba
                     :state :right
                     :x     12 :y 35}
                    {:id    :gd
                     :type  :goomba
                     :state :right
                     :x     64 :y 8}
                    {:id    :ge
                     :type  :goomba
                     :state :right
                     :x     96 :y 32}
                    {:id    :m
                     :type  :mario
                     :state :idle-right
                     :x     200 :y 8}}})

(set! heval/frame-length (/ 1 30))
(set! heval/time-units-per-frame 10000)
(set! heval/time-unit (/ heval/frame-length heval/time-units-per-frame))
(set! heval/precision 0.01)

(defonce last-world nil)
(defonce world (atom {}))

(def play-on-start false)

(declare reset-world! reset-seen-polys! reset-tr-caches!)

(defn reload!
  ([] (reload! nil))
  ([_]
   (set! last-world nil)
   (keys/clear-keys!)
   (reset-tr-caches!)))

(defn debug-shown-transitions [tr-cache]
  [(first (:required-transitions tr-cache))])

(defonce last-time nil)
(defn current-config [world]
  (last (:configs world)))

(defn world-append [world config]
  (let [new-configs (if (>= (:entry-time config)
                            (:entry-time (current-config world)))
                      (conj (:configs world) config)
                      (vec (concat (filter (fn [c]
                                             (<= (:entry-time c) (:entry-time config)))
                                           (:configs world))
                                   [config])))
        new-seen (roll/see-config (:seen-configs world) config)]
    (assoc world :configs new-configs
                 :seen-configs new-seen
                 :explored #{}
                 :now (:entry-time config))))

(defn reset-world [w]
  (let [world-desc (:desc w)
        defs (:ha-defs w)
        [obj-dict tr-caches] (heval/init-has
                               defs
                               (map (fn [{id :id state :state :as ha-desc}]
                                      (let [v0 (dissoc ha-desc :id :type :state)]
                                        (ha/init-ha (get defs id)
                                                    id
                                                    state
                                                    0
                                                    v0)))
                                    (:objects world-desc))
                               0)
        init-config {:entry-time 0
                     :inputs     #{}
                     :objects    obj-dict
                     :tr-caches  tr-caches}]
    (reduce world-append
            (assoc w :now 0
                     :playing play-on-start
                     :configs [init-config]
                     :seen-configs (roll/see-config (:seen-configs w) init-config))
            [
             #_(roll/next-config defs init-config)
             ]
            #_(first (roll/stabilize-config init-config))
            #_(first (roll/fixed-playout init-config
                                         [[:m :jumping-right 0.5]
                                          [:m :moving-right 3.0]
                                          [:m :idle-right 3.75]
                                          [:m :jumping-right 6.0]
                                          #_[:m :moving-right 10.0]])))))

(defn make-world [world-desc]
  (let [ids (set (map :id (:objects world-desc)))
        walls (set (map (fn [{x :x y :y w :w h :h}]
                          [x y w h])
                        (:walls world-desc)))
        defs (ha/define-has
               (map (fn [{type :type id :id}]
                      (case type
                        :goomba (util/goomba id 16 ids walls)
                        :mario (util/mario id ids walls)
                        :simple-camera (util/goomba id 16 ids walls)))
                    (:objects world-desc)))]
    (reset-world {:desc            world-desc
                  :ha-defs         defs
                  :now             0
                  :playing         play-on-start
                  :pause-on-change false
                  :configs         []
                  :seen-configs    #{}
                  :seen-polys      {}
                  :scroll-x        (:scroll-x world-desc)
                  :scroll-y        (:scroll-y world-desc)
                  :camera-width    (:camera-width world-desc)
                  :camera-height   (:camera-height world-desc)
                  :width           (:width world-desc)
                  :height          (:height world-desc)
                  :walls           walls})))

(defn reset-tr-caches! []
  (swap!
    world
    (fn [wld]
      (let [cfgs (:configs wld)
            last-config (last cfgs)]
        (assoc wld
          :configs (conj (subvec cfgs 0 (dec (count cfgs)))
                         (heval/recache-trs (:ha-defs wld)
                                            last-config)))))))

(defonce key-states (atom {:on       #{}
                           :pressed  #{}
                           :released #{}}))

(defn pair [a b]
  (map (fn [ai bi] [ai bi]) a b))

(defn option-desc [{objects :objects}
                   {id :id {edge :index target :target} :transition}
                   t]
  (let [ha (get objects id)]
    (assoc (select-keys ha (concat [:id :state] (:variables ha)))
      :edge edge
      :target target
      :t t)))
(defn option-desc->transition [config {id :id edge :edge}]
  (let [opts (roll/optional-transitions-before config Infinity)]
    (roll/find-move-by-edge opts id edge)))

(def unroll-limit 5)
(def explore-rolled-out? true)
(def explore-roll-limit 5)

(defn explore-nearby [ha-defs seed-playout explored seen]
  (let [seed-playout (concat [nil]
                             seed-playout
                             [(roll/next-config ha-defs (last seed-playout))])
        ;  _ (println "seed length" (count seed-playout))
        [playouts _ _ explored seen]
        (reduce
          (fn [[playouts path prev-opts explored seen] [prev cur]]
            (let [cur-opts (into #{} (map #(option-desc cur % heval/time-unit) (second (roll/next-transitions cur))))
                  ; _ (println "explore" (get-in cur [:objects :m :state]))
                  next-path (if (some? prev)
                              (conj path prev)
                              path)
                  removed-opts (filter #(not (contains? explored (assoc % :t (- (:entry-time cur) heval/time-unit))))
                                       (sets/difference prev-opts cur-opts))
                  _ (println "removed" removed-opts)
                  [remove-explore-playouts explored seen]
                  (reduce
                    (fn [[ps explored seen] opt]
                      (let [trans (option-desc->transition prev opt)
                            time (max
                                   (+ (:entry-time prev) heval/time-unit)
                                   (min (iv/end (:interval trans))
                                        (:t opt)))
                            _ (assert (= (get-in prev [:objects (:id opt) :state])
                                         (:state opt))
                                      (str "not="
                                           (get-in prev [:objects (:id opt) :state])
                                           (:state opt)
                                           "The state of the object in the previous state should be consistent with the from-state of the option."))
                            succ (roll/follow-transition ha-defs prev trans time)
                            _ (assert (= (get-in succ [:objects (:id opt) :state])
                                         (:target opt))
                                      (str "not="
                                           (get-in succ [:objects (:id opt) :state])
                                           (:target opt)
                                           "The state of the object in the successor state should be consistent with the to-state of the option."))
                            [rolled seen] (roll/inert-playout ha-defs succ explore-roll-limit seen)]
                        [(conj ps (concat (conj next-path succ) rolled))
                         (conj
                           explored
                           (assoc opt
                             :t
                             (- time (get-in cur [:objects (:id opt) :entry-time]))))
                         seen]))
                    [[] explored seen]
                    removed-opts)
                  ; _ (println "remove-explore-playouts" (count remove-explore-playouts))
                  added-opts (filter #(not (contains? explored %))
                                     (sets/difference cur-opts prev-opts))
                  _ (println "added" added-opts)
                  [add-explore-playouts explored seen]
                  (reduce
                    (fn [[ps explored seen] opt]
                      (let [trans (option-desc->transition cur opt)
                            time (+ (:entry-time cur) heval/time-unit)
                            _ (soft-assert (= (get-in cur [:objects (:id opt) :state])
                                              (:state opt))
                                           "not="
                                           (get-in cur [:objects (:id opt) :state])
                                           (:state opt))
                            succ (roll/follow-transition ha-defs cur trans time)
                            _ (soft-assert (= (get-in succ [:objects (:id opt) :state])
                                              (:target opt))
                                           "not="
                                           (get-in succ [:objects (:id opt) :state])
                                           (:target opt))
                            [rolled seen] (roll/inert-playout ha-defs succ explore-roll-limit seen)]
                        ;(println "steps" (count rolled))
                        [(conj ps (concat (conj next-path cur succ) rolled))
                         (conj explored (assoc opt :t heval/time-unit))
                         seen]))
                    [[] explored seen]
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
          (pair (butlast seed-playout) (rest seed-playout)))]
    [(map rest playouts) explored seen]))


(defn update-world! [w-atom ufn]
  (swap!
    w-atom
    (fn [w]
      (let [new-w (ufn w)
            seen (:seen-polys new-w)
            ha-defs (:ha-defs new-w)
            old-configs (or (:configs w) [])
            new-configs (or (:configs new-w) old-configs)
            explored (or (:explored new-w) #{})
            seen-configs (:seen-configs new-w)
            last-config (last new-configs)
            focused-objects #{}]
        (if (or (empty? seen)
                (not (roll/seen-config? (:seen-configs w) last-config)))
          (let [newest (if (and (not (empty? old-configs))
                                (< (count old-configs) (count new-configs))
                                (= (:desc w) (:desc new-w)))
                         (concat [(last old-configs)]
                                 (subvec new-configs (count old-configs)))
                         new-configs)
                _ (println "roll" (count newest) (map :entry-time newest))
                [rolled-playout seen-configs] (time (roll/inert-playout ha-defs (last newest) unroll-limit seen-configs))
                rolled-playout (concat newest rolled-playout)
                _ (println "explore" (count rolled-playout))
                [playouts explored seen-configs] (time (explore-nearby ha-defs
                                                                       (if explore-rolled-out?
                                                                         rolled-playout
                                                                         newest)
                                                                       explored
                                                                       seen-configs))
                playouts (conj playouts rolled-playout)
                _ (println "explore playouts" (count playouts) (map count playouts))
                _ (println "merge-in")
                seen (time
                       (reduce
                         (fn [seen playout]
                           (let [final-config (last playout)]
                             (reduce
                               (fn [seen [prev-config next-config]]
                                 (if (and false (roll/seen-config? seen-configs prev-config)
                                          (roll/seen-config? seen-configs next-config))
                                   seen
                                   (reduce
                                     (fn [seen {id         :id
                                                ha-type    :ha-type
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
                                                   seen-for-ha' (seen-viz/merge-seen-poly seen-for-ha
                                                                                          (get ha-defs ha-type)
                                                                                          prev-ha
                                                                                          next-time)]
                                               (assoc seen id seen-for-ha'))
                                             seen))
                                         seen))
                                     seen
                                     (vals (:objects prev-config)))))
                               seen
                               (pair (butlast playout)
                                     (rest playout)))))
                         seen
                         playouts))]
            (println "newest:" (count newest) (map :entry-time newest))
            (assoc new-w :seen-polys seen
                         :seen-configs seen-configs
                         :explored explored
                         :configs (conj (mapv (fn [c] (assoc c :tr-caches nil))
                                              (butlast new-configs))
                                        (last new-configs))))
          new-w)))))

(defn reset-world! [desc]
  (keys/clear-keys!)
  (if (not= (:desc @world) desc)
    (update-world! world (fn [_] (make-world desc)))
    (update-world! world reset-world)))

; remake ha defs from desc, then translate old valuations into new world def.
; we need to translate all the old configs into the new domain, which will be
; lossy but may be convenient. the seen configs/polys/regions/etc will still be
; wrong, so it's not clear how helpful it is, except for stuff like "try
; something, change the level, go back, try again". which is definitely a useful
; case! so let's do that.

(defn update-object-vals [old-defs new-defs old-vals new-vals t]
  (into {}
        (map
          (fn [[k v]]
            (let [v (assoc v :entry-time t)
                  new-type (.-ha-type v)
                  old-val (get old-vals k)
                  old-type (when old-val
                             (.-ha-type old-val))
                  old-def (when old-val
                            (get old-defs old-type))
                  old-val (when old-val
                            (ha/extrapolate old-def old-val t))
                  old-state (when old-val
                              (.-state old-val))
                  new-def (get new-defs new-type)
                  relevant-vals (when old-val
                                  (select-keys (.-v0 old-val)
                                               (keys (.-v0 v))))]
              [k (cond
                   ; if no old val, leave it alone
                   (nil? old-val)
                   v
                   ; if the old val's state is still valid in the new desc,
                   ; copy over the state and the v0
                   (and (= old-type new-type)
                        (contains? (.-states new-def) old-state))
                   (assoc v :v0 (merge (.-v0 v) relevant-vals)
                            :state old-state)
                   ; if the old val's state is no longer valid or if the
                   ; type has changed, try to copy over the valuation
                   :else
                   (assoc v :v0 (merge (.-v0 v) relevant-vals)))]))
          new-vals)))

(defn reenter-current-config [w]
  (let [now (ha/floor-time (:now w) heval/time-unit)
        defs (:ha-defs w)
        reenter-config (update
                         (assoc (current-config w) :entry-time now)
                         :objects
                         (fn [os]
                           (into
                             {}
                             (map (fn [[k v]]
                                    [k (ha/extrapolate (get defs (.-ha-type v))
                                                       v
                                                       now)])
                                  os))))]
    (if (not= reenter-config (current-config w))
      (world-append w reenter-config)
      w)))

(defn world-update-desc [w desc]
  (let [w (reenter-current-config w)
        old-defs (:ha-defs w)
        new-world (make-world desc)
        new-defs (:ha-defs new-world)
        new-vals (:objects (current-config new-world))
        w (assoc w :ha-defs new-defs
                   :desc desc
                   :walls (:walls new-world)
                   :seen-polys {}
                   :explored #{}
                   :seen-configs #{})
        w (update w
                  :configs
                  (fn [cfgs]
                    (mapv
                      (fn [{old-vals :objects t :entry-time :as cfg}]
                        (assoc cfg :objects (update-object-vals old-defs
                                                                new-defs
                                                                old-vals
                                                                new-vals
                                                                t)
                                   :tr-caches nil))
                      cfgs)))]
    (world-append (update w :configs #(subvec % 0 (dec (count %))))
                  (heval/recache-trs new-defs (current-config w)))))

(defn world-update-desc! [desc]
  (update-world! world
                 (fn [w]
                   (world-update-desc w desc))))

(defn tick-frame [t]
  (when-not last-time (set! last-time t))
  ;(assert (>= t last-time) "Non-monotonic time?")
  (let [old-last-time last-time]
    (set! last-time t)
    (.requestAnimationFrame js/window tick-frame)
    (when (:playing @world)
      (update-world!
        world
        (fn [w]
          (let [ha-defs (:ha-defs w)
                c (current-config w)
                new-now (+ (:now w) (/ (- t old-last-time) 1000))
                new-c (heval/update-config
                        ha-defs
                        c
                        new-now
                        ; assume all keys held now were held since "then"
                        [(iv/interval (:now w) new-now) (keys/key-states)]
                        100
                        0)
                new-w (if (not= c new-c)
                        (world-append w new-c)
                        w)
                new-w (assoc new-w :now new-now)]
            (keys/clear-pressed!)
            (if (and (:pause-on-change new-w)
                     (not= c new-c))
              (assoc new-w :playing false)
              new-w)))))))

(when (= @world {})
  (.requestAnimationFrame js/window tick-frame)
  (reset-world! default-world-desc))

(def show-transition-thresholds false)

(defn button-bar [world]
  (let [wld @world
        ha-defs (:ha-defs wld)]
    (sab/html [:div {:style {:position "fixed"}}
               [:button {:onClick #(swap! world
                                          (fn [w]
                                            (assoc w :playing (not (:playing w)))))}
                (if (:playing wld) "PAUSE" "PLAY")]
               [:span {:style {:backgroundColor "lightgrey"}} "Pause on state change?"
                [:input {:type     "checkbox"
                         :checked  (:pause-on-change wld)
                         :onChange #(swap! world
                                           (fn [w]
                                             (assoc w :pause-on-change (.-checked (.-target %)))))}]]
               [:button {:onClick #(reset-world! (:desc @world))} "RESET"]
               [:button {:onClick  #(swap! world
                                           (fn [w]
                                             (let [new-configs (subvec (:configs w) 0 (dec (count (:configs w))))
                                                   c (last new-configs)]
                                               (assoc w :now (:entry-time c)
                                                        :configs new-configs
                                                        :playing false))))
                         :disabled (= 1 (count (:configs wld)))}
                "BACK"]
               [:button {:onClick #(update-world! world
                                                  (fn [w]
                                                    (let [[configs moves] (roll/random-playout ha-defs (current-config w) 1)
                                                          ; drop the start config and move
                                                          configs (rest configs)
                                                          moves (rest moves)
                                                          m (last moves)]
                                                      (println "random move:" m)
                                                      (reduce world-append w configs))))}
                "RANDOM MOVE"]
               [:span {:style {:backgroundColor "lightgrey"}} (str (:now wld))]])))

(def world-widget
  (let [props (fn [this] (aget (.-props this) "args"))
        rescroll (fn [_ _]
                   (this-as this
                     (let [n (.getDOMNode this)
                           wld @(get (props this) :world)]
                       (set! (.-scrollLeft n) (:scroll-x wld))
                       (set! (.-scrollTop n) (- (:height wld) (:scroll-y wld))))))
        c
        (.createClass js/React
                      #js {:shouldComponentUpdate
                           (fn [next-props next-state]
                             (this-as this
                               (or (not= next-props (props this))
                                   (not= @next-state @(.-state this)))))
                           :render
                           (fn []
                             (this-as this
                               (let [props (props this)
                                     world (get props :world)
                                     container-w (get props :width)
                                     container-h (get props :height)
                                     _ (assert (instance? Atom world) "world should be atom?")
                                     wld @world
                                     world-w (:width wld)
                                     world-h (:height wld)
                                     view-w (:camera-width wld)
                                     view-h (:camera-height wld)
                                     x-scale (/ container-w view-w)
                                     y-scale (/ container-h view-h)
                                     ha-defs (:ha-defs wld)
                                     cfg (current-config wld)
                                     has (:objects cfg)
                                     polys (apply concat (vals (:seen-polys wld)))]
                                 (sab/html [:div {:style    {:backgroundColor "blue"
                                                             :width           container-w
                                                             :height          container-h
                                                             :position        "relative"
                                                             :overflow        "scroll"}
                                                  :onScroll (fn [scroll-evt]
                                                              (let [n (.-target scroll-evt)]
                                                                (update-world! world
                                                                               (fn [w]
                                                                                 (assoc w :scroll-x (.-scrollLeft n)
                                                                                          :scroll-y (- (:height w) (.-scrollTop n)))))))}
                                            [:svg {:width   (* world-w x-scale)
                                                   :height  (* world-h y-scale)
                                                   :style   {:position "absolute"}
                                                   :viewBox (str "0 0 " world-w " " world-h)}
                                             (seen-viz/seen-viz world-h polys)
                                             [:g {}
                                              (map (fn [[x y w h]]
                                                     [:rect {:x     x :y (- world-h h y)
                                                             :width w :height h
                                                             :fill  "white"
                                                             :key   (str x "@" y "," w "@" h)}])
                                                   (:walls wld))]
                                             (map (fn [{{x :x y :y w :w h :h} :v0 id :id :as ha}]
                                                    [:g {:key id}
                                                     [:rect {:x     x :y (- world-h h y)
                                                             :width w :height h
                                                             :fill  "brown"
                                                             :key   "sprite"}]
                                                     [:text {:width    200 :x x :y (- world-h y 5)
                                                             :fontSize 8
                                                             :fill     "lightgrey"
                                                             :key      "name"}
                                                      (str id " " (:state ha))]])
                                                  (map #(ha/extrapolate (get ha-defs (:id %)) % (:now wld))
                                                       (vals has)))]
                                            (button-bar world)]))))
                           :componentDidUpdate
                           rescroll
                           :componentDidMount
                           rescroll})
        f (.createFactory js/React c)]
    f))

(defn rererender [target]
  (let [w @world]
    ; slightly weird checks here instead of equality to improve idle performance/overhead
    (when (or (not last-world)
              (not (identical? last-world w))
              (not= (:entry-time (current-config w))
                    (:entry-time (current-config last-world)))
              (not= (:pause-on-change w)
                    (:pause-on-change last-world))
              (not= (:playing w)
                    (:playing last-world))
              (not= (:now w)
                    (:now last-world)))
      (set! last-world @world)
      (js/React.render (world-widget #js {"args" {:world  world
                                                  :width  640
                                                  :height 240}}) target)))
  (.requestAnimationFrame js/window #(rererender target)))