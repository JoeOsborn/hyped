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
    [devtools.core :as devtools]
    [clojure.set :as sets])
  (:require-macros
    [devcards.core :refer [defcard deftest]]
    [player.macros :refer [soft-assert]]))

(defonce has-run nil)
(declare rererender)

(defn spy [& v]
  (apply println v)
  (last v))

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
   :camera-height 240
   :scroll-x      0
   :scroll-y      0
   :walls         {
                   0 {:type :white :x 0 :y 0 :w 256 :h 8}
                   1 {:type :white :x 0 :y 8 :w 8 :h 16}
                   2 {:type :white :x 96 :y 8 :w 8 :h 16}
                   3 {:type :white :x 160 :y 8 :w 8 :h 16}
                   }
   :objects       {
                   :ga {:type  :goomba
                        :state :right
                        :x     8 :y 8
                        :w     16 :h 16}
                   :gb {:type  :goomba
                        :state :right
                        :x     32 :y 8
                        :w     16 :h 16}
                   :gc {:type  :goomba
                        :state :right
                        :x     12 :y 35
                        :w     16 :h 16}
                   :gd {:type  :goomba
                        :state :right
                        :x     64 :y 8
                        :w     16 :h 16}
                   :ge {:type  :goomba
                        :state :right
                        :x     96 :y 32
                        :w     16 :h 16}
                   :m  {:type  :mario
                        :state :jumping-left
                        :x     200 :y 16
                        :v/y   100
                        :w     16 :h 16}
                   }})

(set! heval/frame-length (/ 1 30))
(set! heval/time-units-per-frame 10000)
(set! heval/time-unit (/ heval/frame-length heval/time-units-per-frame))
(set! heval/precision 0.01)

(defonce last-world nil)
(defonce last-editor nil)
(defonce world (atom {}))
(defonce editor (atom {}))

(def play-on-start true)

(declare reset-world! reset-seen-polys! reset-tr-caches!)

(defn reload!
  ([] (reload! nil))
  ([_]
   (set! last-world nil)
   (keys/clear-keys!)
   (reset-tr-caches!)))

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
                               (map (fn [[id {state :state :as ha-desc}]]
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
                     :tr-caches  tr-caches}
        _ (assert (not (empty? (:required-transitions (:m tr-caches)))))]
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
  (let [ids (set (keys (:objects world-desc)))
        walls (set (map (fn [[_k {x :x y :y w :w h :h}]]
                          [x y w h])
                        (:walls world-desc)))
        defs (ha/define-has
               (map (fn [[id {type :type}]]
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
                  :view-width      640
                  :view-height     480
                  :width           (:width world-desc)
                  :height          (:height world-desc)
                  :walls           walls})))

(defn make-editor []
  ; todo: move editor scrolling info here?
  {:selection #{[:walls 0] [:walls 2]}})

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
            (let [cur-opts (into #{} (map #(option-desc cur % heval/time-unit)
                                          (second (roll/next-transitions cur))))
                  ; _ (println "explore" (get-in cur [:objects :m :state]))
                  next-path (if (some? prev)
                              (conj path prev)
                              path)
                  removed-opts (filter #(not (contains? explored (assoc % :t (- (:entry-time cur) (:entry-time prev)))))
                                       (sets/difference prev-opts cur-opts))
                  _ (println "removed" removed-opts)
                  [remove-explore-playouts explored seen]
                  (reduce
                    (fn [[ps explored seen] opt]
                      (let [trans (option-desc->transition prev opt)
                            time (max
                                   (+ (:entry-time prev) heval/time-unit)
                                   (min (iv/end (:interval trans))
                                        (:entry-time cur)))
                            _ (assert (= (get-in prev [:objects (:id opt) :state])
                                         (:state opt))
                                      (str "not="
                                           (get-in prev [:objects (:id opt) :state])
                                           (:state opt)
                                           "The state of the object in the previous state should be consistent with the from-state of the option."))
                            succ (roll/follow-transition ha-defs prev trans time)
                            _ (soft-assert (= (get-in succ [:objects (:id opt) :state])
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
                             (- (:entry-time succ)
                                (get-in prev [:objects (:id opt) :entry-time]))))
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
                            _ (assert (= (get-in cur [:objects (:id opt) :state])
                                         (:state opt))
                                      (str "not="
                                           (get-in cur [:objects (:id opt) :state])
                                           (:state opt)))
                            succ (roll/follow-transition ha-defs cur trans time)
                            _ (soft-assert (= (get-in succ [:objects (:id opt) :state])
                                              (:target opt))
                                           (str "not="
                                                (get-in succ [:objects (:id opt) :state])
                                                (:target opt)))
                            [rolled seen] (roll/inert-playout ha-defs succ explore-roll-limit seen)]
                        ;(println "steps" (count rolled))
                        [(conj ps (concat (conj next-path cur succ) rolled))
                         (conj explored opt)
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

(def explore-around? false)

(defn update-world! [w-atom ufn]
  (swap!
    w-atom
    (fn [w]
      (let [new-w (ufn w)
            seen (:seen-polys new-w)
            ha-defs (:ha-defs new-w)
            old-configs (or (:configs w) [])
            new-configs (or (:configs new-w) old-configs)
            explored (sets/union #{} (:explored new-w) (:explored w))
            seen-configs (sets/union #{} (:seen-configs new-w) (:seen-configs w))
            focused-objects #{}]
        (if (and
              explore-around?
              (or (empty? seen)
                  (not= (last old-configs) (last new-configs))))
          (let [_ (println "empty-seen?" (empty? seen))
                newest (if (and (not (empty? old-configs))
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
(defn update-object-vals [old-defs new-defs
                          old-init
                          old-vals new-vals
                          t]
  (into {}
        (map
          (fn [[k v]]
            (let [v (assoc v :entry-time t)
                  new-type (.-ha-type v)
                  old-val (get old-vals k)
                  old-init (get old-init k)
                  old-type (when old-val
                             (.-ha-type old-val))
                  old-def (when old-val
                            (get old-defs old-type))
                  old-val (when old-val
                            (ha/extrapolate old-def old-val t))
                  old-at-init? (= (.-v0 old-val)
                                  (.-v0 old-init))
                  ; if the old val was at the initial valuation,
                  ; then moving the initial valuation should update the old val.
                  old-val (if old-at-init?
                            nil
                            old-val)
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
        old-init-vals (:objects (first (:configs w)))
        _ (println "world-update-desc")
        w (assoc w :ha-defs new-defs
                   :desc desc
                   :walls (:walls new-world)
                   :seen-polys {}
                   :explored #{}
                   :seen-configs #{}
                   :width (:width desc)
                   :height (:height desc))
        w (update w
                  :configs
                  (fn [cfgs]
                    (mapv
                      (fn [{old-vals :objects t :entry-time :as cfg}]
                        (assoc cfg :objects (update-object-vals old-defs
                                                                new-defs
                                                                old-init-vals
                                                                old-vals
                                                                new-vals
                                                                t)
                                   :tr-caches nil))
                      cfgs)))]
    (world-append (update w :configs #(subvec % 0 (dec (count %))))
                  (heval/recache-trs new-defs (current-config w)))))

(defn world-update-desc! [world desc]
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
                        10
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

(when (= @editor {})
  (.requestAnimationFrame js/window tick-frame)
  (reset! editor (make-editor)))

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

(defn walls-under [wld wx wy]
  (keep (fn [[id {x :x y :y w :w h :h :as wall}]]
          (when (and (<= x wx (+ x w))
                     (<= y wy (+ y h)))
            [id wall]))
        (:walls (:desc wld))))

(defn ha-starts-under [wld wx wy]
  (keep (fn [[id ha]]
          (when (and (<= (:x ha) wx (+ (:x ha) (:w ha)))
                     (<= (:y ha) wy (+ (:y ha) (:h ha))))
            [id ha]))
        (:objects (:desc wld))))

(defn has-under [wld wx wy]
  (let [ha-defs (:ha-defs wld)
        has (:objects (current-config wld))]
    (filter #(let [ha-val (ha/extrapolate (get ha-defs (:id %)) % (:now wld))
                   v0 (.-v0 ha-val)]
              #_(println "check" wx wy v0)
              (and (<= (:x v0) wx (+ (:x v0) (:w v0)))
                   (<= (:y v0) wy (+ (:y v0) (:h v0)))))
            (vals has))))

(defn things-under [wld x y]
  (concat (map (fn [[id _wall]]
                 [:walls id])
               (walls-under wld x y))
          (map (fn [[id _ha-desc]]
                 [:objects id])
               (ha-starts-under wld x y))
          (map (fn [{id :id}]
                 [:live-objects id])
               (has-under wld x y))))

(def drag-threshold 2)

(defn editor-start-new-thing [ed x y now-x now-y]
  ;todo: HA _or_ wall
  (let [new-id (inc (apply max (map first (:walls (:draft-desc ed)))))
        _ (println "create new wall" new-id x y now-x now-y)
        new-thing-handle [:walls new-id]
        ax x
        ay y
        bx now-x
        by now-y]
    (assoc ed
      :move-mode :resizing
      :selection #{new-thing-handle}
      :draft-desc (assoc-in
                    (:draft-desc ed)
                    new-thing-handle
                    {:x (.min js/Math ax bx)
                     :y (.min js/Math ay by)
                     :w (.abs js/Math (- bx ax))
                     :h (.abs js/Math (- by ay))}))))

(defn editor-move-selection [ed dx dy]
  (println "move selection by" dx dy)
  (assoc ed
    :move-mode :moving
    :draft-desc
    (reduce
      (fn [desc sel-path]
        (update-in desc sel-path (fn [{x :x y :y :as obj}]
                                   (assoc obj :x (+ x dx)
                                              :y (+ y dy)))))
      (:draft-desc ed)
      (:selection ed))))

(defn editor-resize-selection [ed dx dy]
  (println "resize selection"
           (first (:selection ed))
           (get-in (:draft-desc ed)
                   (first (:selection ed)))
           "by" dx dy)
  (let [[sx sy] (:last-loc ed)
        {x :x y :y w :w h :h} (get-in (:draft-desc ed) (first (:selection ed)))
        ; if sx is rightish, adjust width only; else adjust width and x
        [nx nw] (if (> sx (+ x (/ w 2)))
                  [x (+ w dx)]
                  [(+ x dx) (- w dx)])
        ; if sy is toppish, adjust height only; else adjust height and y
        [ny nh] (if (> sy (+ y (/ h 2)))
                  [y (+ h dy)]
                  [(+ y dy) (- h dy)])
        [nx nw] (if (< nw 0)
                  [(+ nx nw) (.abs js/Math nw)]
                  [nx nw])
        [ny nh] (if (< nh 0)
                  [(+ ny nh) (.abs js/Math nh)]
                  [ny nh])]
    (assoc ed :draft-desc (update-in (:draft-desc ed)
                                     (first (:selection ed))
                                     assoc
                                     :x nx :y ny
                                     :w nw :h nh)
              :move-mode :resizing)))

(def resize-threshold 2)

(defn wall-centerish-point? [{x :x y :y w :w h :h} wx wy]
  (and (<= (+ x resize-threshold) wx (- (+ x w) resize-threshold))
       (<= (+ y resize-threshold) wy (- (+ y h) resize-threshold))))

(defn ha->desc [{v0 :v0 state :state ha-type :ha-type}]
  (assoc v0 :state state :type ha-type))

(defn selection-init [ed]
  (assoc ed :selection #{}))
(defn selection-add [ed wld new-sel]
  (if (= (first new-sel) :live-objects)
    (assoc ed
      :selection (conj (:selection ed) new-sel)
      :draft-desc (assoc-in (:draft-desc ed) new-sel (ha->desc (get-in (current-config wld)
                                                                       [:objects (second new-sel)]))))
    (update ed :selection conj new-sel)))
(defn selection-remove [ed new-sel]
  (if (= (first new-sel) :live-objects)
    (assoc ed
      :selection (disj (:selection ed) new-sel)
      :draft-desc (update (:draft-desc ed) :live-objects dissoc (second new-sel)))
    (update ed :selection disj new-sel)))

(defn extrapolate-cfg [wld cfg t]
  (update (assoc cfg :entry-time t)
          :objects
          (fn [os]
            (into {} (map (fn [[id ha]]
                            (let [ha-def (get (:ha-defs wld) (:ha-type ha))]
                              [t (ha/extrapolate ha-def ha t)]))
                          os)))))

(def world-widget
  (let [props (fn [this] (aget (.-props this) "args"))
        ; world -> view: scale up and flip
        world->view (fn [props x y]
                      (let [wld @(get props :world)
                            container-w (:view-width wld)
                            container-h (:view-height wld)
                            view-w (:camera-width wld)
                            view-h (:camera-height wld)
                            x-scale (/ container-w view-w)
                            y-scale (/ container-h view-h)]
                        ; vy = yscale*(wy-y)
                        [(* x x-scale) (* (- (:height wld) y) y-scale)]))
        ; view -> world: flip and scale down
        view->world (fn [props x y]
                      (let [wld @(get props :world)
                            container-w (:view-width wld)
                            container-h (:view-height wld)
                            view-w (:camera-width wld)
                            view-h (:camera-height wld)
                            x-scale (/ container-w view-w)
                            y-scale (/ container-h view-h)]
                        ; vy = wy-(y/yscale)
                        [(/ x x-scale) (- (:height wld) (/ y y-scale))]))

        rescroll (fn [_ _]
                   (this-as this
                     (let [n (.getDOMNode this)
                           props (props this)
                           wld @(get props :world)
                           container-h (:view-height wld)
                           [new-scroll-x new-scroll-y] (world->view props (:scroll-x wld) (:scroll-y wld))]
                       #_(println "rescroll" (:scroll-x wld) (:scroll-y wld) "->" new-scroll-x (- new-scroll-y container-h))
                       (when (not= (.-scrollLeft n) new-scroll-x)
                         (set! (.-scrollLeft n) new-scroll-x))
                       (when (not= (.-scrollTop n) (- new-scroll-y container-h))
                         (set! (.-scrollTop n) (- new-scroll-y container-h))))))
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
                                     wld @world
                                     editor (get props :editor)
                                     ed @editor
                                     desc (or (:draft-desc ed) (:desc wld))
                                     container-w (:view-width wld)
                                     _ (assert (number? container-w))
                                     container-h (:view-height wld)
                                     world-w (:width wld)
                                     world-h (:height wld)
                                     view-w (:camera-width wld)
                                     view-h (:camera-height wld)
                                     x-scale (/ container-w view-w)
                                     y-scale (/ container-h view-h)
                                     ha-defs (:ha-defs wld)
                                     cfg (current-config wld)
                                     has (:objects cfg)
                                     ha-starts (:objects desc)
                                     polys (apply concat (vals (:seen-polys wld)))

                                     sel (:selection ed)]
                                 (sab/html [:div {:style {:backgroundColor "blue"
                                                          :width           (+ container-w 20)
                                                          :height          (+ container-h 20)
                                                          :position        "relative"
                                                          :overflow        "scroll"}
                                                  :onMouseDown
                                                         (fn [evt]
                                                           (let [t (.-currentTarget evt)
                                                                 mx (+ (- (.-pageX evt) (.-offsetLeft t))
                                                                       (.-scrollLeft t))
                                                                 my (+ (- (.-pageY evt) (.-offsetTop t))
                                                                       (.-scrollTop t))
                                                                 [wx wy] (view->world props mx my)
                                                                 found-things (things-under wld wx wy)]
                                                             (println "click at" mx my "->" wx wy)
                                                             (println "found under mouse:" found-things)
                                                             (swap! editor (fn [ed]
                                                                             (let [ed (assoc ed
                                                                                        :draft-desc (assoc (:desc wld)
                                                                                                      :live-objects {})
                                                                                        :mouse-down-loc [wx wy]
                                                                                        :last-loc [wx wy]
                                                                                        :move-mode :clicking)]
                                                                               (if-let [new-sel (first found-things)]
                                                                                 (if (.-shiftKey evt)
                                                                                   (if (contains? sel new-sel)
                                                                                     (selection-remove ed new-sel)
                                                                                     (selection-add ed wld new-sel))
                                                                                   (selection-add (selection-init ed) wld new-sel))
                                                                                 (if (.-shiftKey evt)
                                                                                   ed
                                                                                   (selection-init ed))))))))
                                                  :onMouseMove
                                                         (fn [evt]
                                                           (let [ed @editor
                                                                 [down-x down-y] (or (:mouse-down-loc ed) [nil nil])]
                                                             (when (some? down-x)
                                                               ;drag/extend/etc, update desc in some placeholder spot?
                                                               ; this way can draw overlay of new wall/object/position/size/whatever, while still drawing the old one where it lives.
                                                               (let [t (.-currentTarget evt)
                                                                     mx (+ (- (.-pageX evt) (.-offsetLeft t))
                                                                           (.-scrollLeft t))
                                                                     my (+ (- (.-pageY evt) (.-offsetTop t))
                                                                           (.-scrollTop t))
                                                                     [wx wy] (view->world props mx my)
                                                                     dx (- wx down-x)
                                                                     dy (- wy down-y)
                                                                     [last-x last-y] (:last-loc ed)
                                                                     ddx (- wx last-x)
                                                                     ddy (- wy last-y)
                                                                     sel (:selection ed)
                                                                     mode (:move-mode ed)]
                                                                 (let [new-ed
                                                                       (assoc
                                                                         (cond
                                                                           (= mode :resizing)
                                                                           ; resize selected object
                                                                           (editor-resize-selection ed ddx ddy)
                                                                           (= mode :moving)
                                                                           ; move selected objects
                                                                           (editor-move-selection ed ddx ddy)
                                                                           (>= (.sqrt js/Math (+ (* dx dx) (* dy dy))) drag-threshold)
                                                                           (do
                                                                             (println "start dragging")
                                                                             (cond
                                                                               ; no selection
                                                                               (empty? sel)
                                                                               ;create new object and set sel to it and enter either moving state (for HAs) or resizing state (for walls)
                                                                               ; multi-selection or HA selected or mouse in center
                                                                               (editor-start-new-thing ed down-x down-y wx wy)
                                                                               (or (> 1 (count sel))
                                                                                   (= :objects (ffirst sel))
                                                                                   (= :live-objects (ffirst sel))
                                                                                   (wall-centerish-point? (get-in (:draft-desc ed) (first sel)) wx wy))
                                                                               ; move selected object(s)
                                                                               (editor-move-selection ed dx dy)
                                                                               ;(mouse started at edge of selected thing)
                                                                               :else
                                                                               ; resize selected object if wall
                                                                               (editor-resize-selection ed dx dy)))
                                                                           ; haven't moved enough to drag.
                                                                           ; todo: show resize or move cursor appropriately
                                                                           :else ed)
                                                                         :last-loc [wx wy])]
                                                                   (reset! editor new-ed)))))
                                                           )
                                                  :onMouseUp
                                                         (fn [_evt]
                                                           (let [ed @editor]
                                                             (when (:mouse-down-loc ed)
                                                               ;actually change world to match new desc
                                                               (update-world!
                                                                 world
                                                                 (fn [w]
                                                                   (let [desc (dissoc (:draft-desc ed)
                                                                                      :live-objects)
                                                                         live (:live-objects (:draft-desc ed))]
                                                                     (world-update-desc
                                                                       (update-in (reenter-current-config w)
                                                                                  [:configs
                                                                                   (dec (count (:configs w)))]
                                                                                  (fn [cfg]
                                                                                    (reduce
                                                                                      (fn [cfg [id val]]
                                                                                        (update-in cfg
                                                                                                   [:objects id]
                                                                                                   assoc
                                                                                                   :v0 (dissoc val :type :state)
                                                                                                   :state (:state val)
                                                                                                   :type (:type val)))
                                                                                      cfg
                                                                                      live)))
                                                                       desc))))
                                                               (swap! editor assoc
                                                                      :mouse-down-loc nil
                                                                      :move-mode nil
                                                                      :draft-desc nil))))
                                                  :onScroll
                                                         (fn [scroll-evt]
                                                           (let [n (.-target scroll-evt)]
                                                             (update-world! world
                                                                            (fn [w]
                                                                              (let [[sx sy] (view->world props (.-scrollLeft n) (+ (.-scrollTop n) container-h))]
                                                                                #_(println "update from scroll:"
                                                                                           (.-scrollLeft n) (+ (.-scrollTop n) container-h)
                                                                                           "->" sx sy)
                                                                                (assoc w :scroll-x sx
                                                                                         :scroll-y sy))))))}
                                            [:svg {:width               (* world-w x-scale)
                                                   :height              (* world-h y-scale)
                                                   :style               {:position "absolute"}
                                                   :preserveAspectRatio "none"
                                                   :viewBox             (str "0 0 " world-w " " world-h)}
                                             (seen-viz/seen-viz world-h polys)
                                             [:g {:key "walls"}
                                              (map (fn [[k {x :x y :y w :w h :h}]]
                                                     [:g {:key (str "wall-" k)}
                                                      [:rect {:x     x :y (- world-h h y)
                                                              :width w :height h
                                                              :fill  "white"
                                                              :key   "wall"}]
                                                      (when (contains? sel [:walls k])
                                                        [:rect {:x            x :y (- world-h h y)
                                                                :width        w :height h
                                                                :fill         "url(#diagonal-stripe-1)"
                                                                :opacity      "0.5"
                                                                :stroke       "black"
                                                                :stroke-width 2
                                                                :key          "selected"}])
                                                      ;todo: grab handles
                                                      ])
                                                   (:walls desc))]
                                             [:g {:key "objects"}
                                              (map (fn [{{x :x y :y w :w h :h} :v0 id :id :as ha}]
                                                     (if (and (contains? sel [:live-objects id])
                                                              (some? (:move-mode ed)))
                                                       (let [{new-x :x new-y :y new-w :w new-h :h} (get-in ed [:draft-desc :live-objects id])]
                                                         [:g {:key id}
                                                          [:rect {:x       x :y (- world-h h y)
                                                                  :width   w :height h
                                                                  :fill    "brown"
                                                                  :key     "old-sprite"
                                                                  :opacity "0.2"}]
                                                          [:text {:width    200 :x x :y (- world-h y 5)
                                                                  :fontSize 8
                                                                  :fill     "lightgrey"
                                                                  :key      "old-name"
                                                                  :opacity  "0.2"}
                                                           (str id " " (:state ha))]
                                                          [:rect {:x     new-x :y (- world-h new-h new-y)
                                                                  :width new-w :height new-h
                                                                  :fill  "brown"
                                                                  :key   "new-sprite"}]
                                                          [:text {:width    200 :x new-x :y (- world-h new-y 5)
                                                                  :fontSize 8
                                                                  :fill     "lightgrey"
                                                                  :key      "new-name"}
                                                           (str id " " (:state ha))]
                                                          [:rect {:x            new-x :y (- world-h new-h new-y)
                                                                  :width        new-w :height new-h
                                                                  :fill         "url(#diagonal-stripe-1)"
                                                                  :opacity      "0.5"
                                                                  :stroke       "black"
                                                                  :stroke-width 2
                                                                  :key          "selected"}]])
                                                       [:g {:key id}
                                                        [:rect {:x     x :y (- world-h h y)
                                                                :width w :height h
                                                                :fill  "brown"
                                                                :key   "sprite"}]
                                                        [:text {:width    200 :x x :y (- world-h y 5)
                                                                :fontSize 8
                                                                :fill     "lightgrey"
                                                                :key      "name"}
                                                         (str id " " (:state ha))]
                                                        (when (contains? sel [:live-objects id])
                                                          [:rect {:x            x :y (- world-h h y)
                                                                  :width        w :height h
                                                                  :fill         "url(#diagonal-stripe-1)"
                                                                  :opacity      "0.5"
                                                                  :stroke       "black"
                                                                  :stroke-width 2
                                                                  :key          "selected"}])]))
                                                   (map #(ha/extrapolate (get ha-defs (:id %)) % (:now wld))
                                                        (vals has)))]
                                             [:g {:key "object-starts"}
                                              (map (fn [[id {x :x y :y w :w h :h state :state}]]
                                                     [:g {:key id :opacity "0.25"}
                                                      [:rect {:x     x :y (- world-h h y)
                                                              :width w :height h
                                                              :fill  "brown"
                                                              :key   "sprite"}]
                                                      (when (contains? sel [:objects id])
                                                        [:rect {:x            x :y (- world-h h y)
                                                                :width        w :height h
                                                                :fill         "url(#diagonal-stripe-1)"
                                                                :opacity      "0.5"
                                                                :stroke       "black"
                                                                :stroke-width 2
                                                                :key          "selected"}])
                                                      [:text {:width    200 :x x :y (- world-h y 5)
                                                              :fontSize 8
                                                              :fill     "lightgrey"
                                                              :key      "name"}
                                                       (str id " " state)]])
                                                   ha-starts)]]
                                            (button-bar world)]))))
                           :componentDidUpdate
                           rescroll
                           :componentDidMount
                           rescroll})
        f (.createFactory js/React c)]
    f))

(defn num-changer [world label key update-fn!]
  (sab/html
    [:label {:key (str key "-label")} label]
    [:input {:type     "number"
             :key      (str key "-field")
             :value    (key @world)
             :onChange (fn [evt]
                         (update-fn! world key (.parseInt js/window (.-value (.-target evt)))))}]))

(defn world-update-desc-key! [world key val]
  (world-update-desc! world (assoc (:desc @world)
                              key
                              val)))

(defn world-update-key! [world key val]
  (update-world! world (fn [w] (assoc w key val))))

(defn edit-controls [world editor]
  (sab/html [:div
             (num-changer world "World Width" :width world-update-desc-key!)
             (num-changer world "World Height" :height world-update-desc-key!)
             [:br {:key 0}]
             (num-changer world "Scroll X" :scroll-x world-update-key!)
             (num-changer world "Scroll Y" :scroll-y world-update-key!)
             [:br {:key 1}]
             (num-changer world "Camera Width" :camera-width world-update-key!)
             (num-changer world "Camera Height" :camera-height world-update-key!)
             [:br {:key 2}]
             (num-changer world "View Width" :view-width world-update-key!)
             (num-changer world "View Height" :view-height world-update-key!)
             [:br {:key 3}]

             [:button {:onClick (fn [_evt]
                                  (reset! editor (make-editor)))}
              "Reset editor"]]))

(defn rererender [target]
  (let [w @world
        ed @editor
        quick-check-keys [:now :scroll-x :scroll-y :width :height :camera-width :camera-height :pause-on-change :playing]]
    ; slightly weird checks here instead of equality to improve idle performance/overhead
    (when (or (not last-world)
              (not (identical? last-world w))
              (not last-editor)
              (not= last-editor ed)
              (not= (select-keys last-world quick-check-keys)
                    (select-keys w quick-check-keys))
              (not= (:entry-time (current-config w))
                    (:entry-time (current-config last-world))))
      (set! last-world w)
      (set! last-editor ed)
      (js/React.render (sab/html [:div {}
                                  (world-widget #js {"args" {:world  world
                                                             :editor editor}})
                                  (edit-controls world editor)]) target)))
  (.requestAnimationFrame js/window #(rererender target)))