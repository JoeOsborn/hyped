(ns player.core
  (:require
    [sablono.core :as sab :include-macros true]
    [ha.intervals :as iv]
    [ha.eval :as heval]
    [ha.ha :as ha :refer [make-ha make-state make-edge kw]]
    [ha.rollout :as roll]
    [player.ui :as ui]
    [player.worlds :as worlds]
    [player.editor :as editor]
    [player.seen-viz :as seen-viz]
    [player.seen-viz-ui :as seen-viz-ui]
    [player.key-handler :as keys]
    [devtools.core :as devtools]
    [clojure.set :as sets]
    [player.explore-service :as explore]
    [cognitect.transit :as transit]
    [cljs-http.client :as http]
    [cljs.core.async :as async :refer [<!]])
  (:require-macros
    [devcards.core :refer [defcard deftest]]
    [player.macros :refer [soft-assert]]
    [cljs.core.async.macros :refer [go]]))



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
    (.requestAnimationFrame js/window #(rererender node))))

(when-not has-run
  (main))

(def default-world-desc
  ;simple flappy scenario
  #_{:width 320, :height 240, :camera-width 320, :camera-height 240, :scroll-x 0, :scroll-y 0, :walls {0 {:type :white, :x 0, :y 0, :w 340, :h 8} 1 {:type :white :x 0 :y 232 :w 340 :h 8}}, :objects {:f1 {:type :flappy, :state :flapping, :x 8, :y 64, :w 16, :h 16}}}

  ;mario area, one goomba
  {:scroll-x 0, :scroll-y 0, :camera-width 320, :camera-height 240, :width 320, :height 240, :objects {:mario {:y 8, :v/y 0, :v/x 0, :w 16, :type :mario, :state :idle-right, :jump-timer 0, :h 16, :x 117}, :goomba {:type :goomba, :state :right, :x 30.83407999947667, :y 8, :w 16, :h 16, :v/x 16, :v/y -32}}, :walls {0 {:type :white, :x 0, :y 0, :w 256, :h 8}, 1 {:type :white, :x 0, :y 8, :w 8, :h 16}, 2 {:type :white, :x 96, :y 8, :w 8, :h 16}, 3 {:type :white, :x 160, :y 8, :w 8, :h 16}, 4 {:type :white, :x 0, :y 222, :w 320, :h 8}, 5 {:type :white, :x 145, :y 135, :w 32, :h 96}, 6 {:type :white, :x 204, :y 35, :w 36, :h 13}}}

  ;more complex flappy
  #_{:width         320
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
                     4 {:type :white :x 0 :y 222 :w 320 :h 8}
                     5 {:type :white :x 145 :y 135 :w 32 :h 96}
                     }
     :objects       {
                     ;:ga {:type  :goomba
                     ;     :state :right
                     ;     :x     8 :y 8
                     ;     :w     16 :h 16}
                     ;:gb {:type  :goomba
                     ;     :state :right
                     ;     :x     32 :y 8
                     ;     :w     16 :h 16}
                     ;:gc {:type  :goomba
                     ;     :state :falling-right
                     ;     :x     20 :y (- 35 8)
                     ;     :w     16 :h 16}
                     ;:gd {:type  :goomba
                     ;     :state :right
                     ;     :x     64 :y 8
                     ;     :w     16 :h 16}
                     ;:ge {:type  :goomba
                     ;     :state :right
                     ;     :x     96 :y 32
                     ;     :w     16 :h 16}
                     ;:m  {:type  :mario
                     ;     :state :moving-right
                     ;     :x     0 :y 24
                     ;     :v/x   8 :v/y 0
                     ;     :w     16 :h 16}
                     :f1 {:type  :flappy
                          :state :falling
                          :x     8 :y 64
                          :w     16 :h 16}
                     ;:f2 {:type  :flappy
                     ;     :state :falling
                     ;     :x     16 :y 80
                     ;     :w     16 :h 16}
                     ;:f3 {:type  :flappy
                     ;     :state :falling
                     ;     :x     12 :y 50
                     ;     :w     16 :h 16}
                     ;:f4 {:type  :flappy
                     ;     :state :falling
                     ;     :x     32 :y 68
                     ;     :w     16 :h 16}
                     }})

(set! heval/frame-length (/ 1 30))
(set! heval/time-units-per-frame 1000)
(set! heval/time-unit (/ heval/frame-length heval/time-units-per-frame))
(set! heval/precision 0.01)

(defonce last-world nil)
(defonce last-editor nil)
(defonce last-time nil)
(defonce world (atom {}))
(defonce ed-atom (atom {}))

(def play-on-start false)

(declare reset-world! reset-seen-polys! reset-tr-caches!)

(defn reload!
  ([] (reload! nil))
  ([_]
   (set! last-world nil)
   (keys/clear-keys!)
   (reset-tr-caches!)))

(def default-world-params
  {:playing         play-on-start
   :pause-on-change false})

(defn reset-tr-caches! []
  (swap!
    world
    (fn [wld]
      (update-in wld
                 [:configs (dec (count (:configs wld)))]
                 (fn [cfg]
                   (heval/recache-trs (:ha-defs wld)
                                      cfg))))))


;todo: update-config is recursing too much in weird ways. is it an actual bug or is it a quirk of the exploration? can we give a "stack trace" of the last followed transitions or something?
(def unroll-limit 5)
(def explore-rolled-out? true)
(def explore-around? true)
(def explore-roll-limit 5)

(defn update-world! [w-atom ufn]
  (swap!
    w-atom
    (fn [w]
      (let [new-w (ufn w)
            _ (when (not= (:desc new-w)
                          (:desc w))
                (explore/reboot-services))
            desc (:desc new-w)
            ha-defs (:ha-defs new-w)
            old-configs (or (:configs w) [])
            new-configs (or (:configs new-w) old-configs)
            seen-configs (sets/union #{} (:seen-configs new-w) (:seen-configs w))
            newest (cond
                     (and (= (count old-configs) (count new-configs))
                          (= (:desc w) (:desc new-w)))
                     []
                     (and (not (empty? old-configs))
                          (< (count old-configs) (count new-configs))
                          (= (:desc w) (:desc new-w)))
                     (concat [(last old-configs)]
                             (subvec new-configs (count old-configs)))
                     :else
                     new-configs)
            ;_ (println "init newest" (count newest))
            newest (drop-while #(roll/seen-config? seen-configs %) newest)]
        ;todo: discard results from explorations of old descs, and if possible cancel the dispatch of exploration requests to them!!
        (when (and explore-around?
                   (not (empty? newest)))
          ;todo: cache explored options and don't re-explore them?
          (println "explore" (count newest) (map :entry-time newest))
          #_(doseq [cfg (filter #(not (roll/seen-config? seen-configs %)) newest)
                    :let [focused-objects #{}
                          chan (http/post "/rpc/explore"
                                          {:json-params
                                           {:method    "symx-1"
                                            :arguments (transit/write (ha/transit-writer)
                                                                      [ha-defs (:objects cfg)])}})]]
              (go (let [result (<! chan)
                        body (:body result)
                        _ (println "RESP BODY:" body)
                        opt-times (transit/read (ha/transit-reader) body)
                        _ (println "parsed:" opt-times)
                        playout-pairs (time (doall (map (fn [[_o ts]]
                                                          (for [[witness tmins tmaxes] ts
                                                                :let [moves (map second witness)
                                                                      _ (println moves)
                                                                      min-moves (zipmap tmins moves)
                                                                      max-moves (zipmap tmaxes moves)]
                                                                steps [min-moves max-moves]]
                                                            (roll/fixed-playout
                                                              ha-defs
                                                              cfg
                                                              steps
                                                              (fn [_ _ t] t))))
                                                        opt-times)))
                        seen (seen-viz/see-polys-in-playout-pairs {} ha-defs playout-pairs focused-objects)]
                    (swap! w-atom (fn [w]
                                    (if (not= (:desc w) desc)
                                      w
                                      (assoc w
                                        :seen-polys
                                        (seen-viz/merge-poly-sets (:seen-polys w) seen))))))))
          (explore/worker-explore ha-defs
                                  newest
                                  explore-roll-limit
                                  (fn [new-polys]
                                    (println "new polys" (map count new-polys))
                                    (swap! w-atom
                                           (fn [w]
                                             (if (not= (:desc w) desc)
                                               w
                                               (assoc w
                                                 :seen-polys
                                                 (seen-viz/merge-poly-sets (:seen-polys w) new-polys))))))))
        ;todo: only invalidate configs in newest
        (assoc new-w
          :seen-configs (reduce roll/see-config seen-configs newest)
          :configs (conj (mapv #(assoc % :tr-caches nil)
                               (butlast new-configs))
                         (last new-configs)))))))

(defn reset-world! [desc]
  (keys/clear-keys!)
  (if (not= (:desc @world) desc)
    (update-world! world (fn [_] (worlds/make-world default-world-params desc)))
    (update-world! world (fn [w] (worlds/reset-world default-world-params w)))))

(defn world-update-desc! [world desc]
  (update-world! world
                 (fn [w]
                   (worlds/world-update-desc w desc))))

(defn commit-draft-desc! [ed world]
  (update-world!
    world
    (fn [w]
      (let [desc (or (:draft-desc ed)
                     (:desc @world))
            live (:live-objects desc)
            desc (dissoc desc :live-objects)]
        (assert desc)
        (worlds/world-update-desc
          (update-in (worlds/reenter-current-config w)
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
          desc)))))

(defn world-update-desc-key! [world keyp val]
  (world-update-desc! world (assoc-in (:desc @world)
                                      keyp
                                      val)))

(defn world-update-key! [world keyp val]
  (update-world! world (fn [w] (assoc-in w keyp val))))

(defn inspector-update-key! [target-atom keyp val]
  (case (first keyp)
    (:create-mode :draft-desc) (swap! target-atom
                                      update-in
                                      keyp
                                      (fn [_] val))
    :configs (update-world! target-atom (fn [w] (assoc-in (worlds/reenter-current-config w) keyp val)))
    :desc (world-update-desc-key! target-atom
                                  (rest keyp)
                                  val)))

(defn extrapolated-get-in [world keyp]
  (let [defs (:ha-defs world)
        world' (if (= (first keyp) :configs)
                 ; update [first second third fourth] of keyp in world: an HA
                 ; to update, extrapolate that HA up to world now
                 (update-in world
                            (take 4 keyp)
                            (fn [ha]
                              (ha/extrapolate (get defs (.-ha-type ha))
                                              ha
                                              (:now world))))
                 world)]
    (get-in world' keyp)))

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
                c (worlds/current-config w)
                new-now (+ (:now w) (/ (- t old-last-time) 1000))
                [status new-c] (heval/update-config
                                 ha-defs
                                 c
                                 new-now
                                 ; assume all keys held now were held since "then"
                                 [(iv/interval (:now w) new-now) (keys/key-states)]
                                 ; bailout if we transition more than 60 times per second
                                 (.max js/Math (* 60 (- new-now (:now w))) 5)
                                 [])
                new-w (assoc w :now new-now)
                new-w (cond
                        (= status :timeout) (do
                                              (.warn js/console "Timed out, too many transitions")
                                              (assoc w :playing false))
                        (not= c new-c) (worlds/world-append w new-c)
                        :else new-w)]
            (keys/clear-pressed!)
            (if (and (:pause-on-change new-w)
                     (not= c new-c))
              (assoc new-w :playing false)
              new-w)))))))

(when (= @world {})
  (.requestAnimationFrame js/window tick-frame)
  (reset-world! default-world-desc))

(when (= @ed-atom {})
  (.requestAnimationFrame js/window tick-frame)
  (reset! ed-atom (editor/make-editor)))

(defn button-bar [world]
  (let [wld @world
        ha-defs (:ha-defs wld)]
    (sab/html [:div {:style {:position "fixed" :top 0}}
               [:button {:onClick #(swap! world
                                          (fn [w]
                                            (assoc w :playing (not (:playing w)))))}
                (if (:playing wld)
                  "PAUSE"
                  "PLAY")]
               [:span {:style {:backgroundColor "lightgrey"}} "Pause on state change?"
                [:input {:type     "checkbox"
                         :checked  (:pause-on-change wld)
                         :onChange #(swap! world
                                           (fn [w]
                                             (assoc w :pause-on-change
                                                      (.-checked (.-target %)))))}]]
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
                                                    (let [[configs moves] (roll/random-playout ha-defs (worlds/current-config w) 1)
                                                          ; drop the start config and move
                                                          configs (rest configs)
                                                          moves (rest moves)
                                                          m (last moves)]
                                                      (println "random move:" m)
                                                      (reduce worlds/world-append w configs))))}
                "RANDOM MOVE"]
               [:button {:onClick #(let [cfg (worlds/current-config @world)
                                         xcfg (worlds/extrapolate-config (:ha-defs @world) cfg (:now @world))
                                         target-config
                                         (into [:and]
                                               ;todo: get from some list of focused objects rather than all objects of config, using select-keys
                                               (for [[oid o] (:objects xcfg)]
                                                 (into [:and
                                                        [:in-state oid #{(:state o)}]]
                                                       ;todo: use other keys?
                                                       (for [[vk val] (select-keys (:v0 o) [:x :y])]
                                                         [:and
                                                          [:geq [:var oid vk] (- val heval/precision)]
                                                          [:leq [:var oid vk] (+ val heval/precision)]]))))
                                         chan (http/post "/rpc/check"
                                                         {:json-params
                                                          {:arguments
                                                           (transit/write
                                                             (ha/transit-writer)
                                                             [ha-defs
                                                              (:objects (first (:configs @world)))
                                                              target-config
                                                              ; arbitrary bound
                                                              10])}})]
                                    (go (let [result (<! chan)
                                              body (:body result)
                                              witness (transit/read (ha/transit-reader) body)]
                                          (println "Got:" witness))))}
                "MODEL-CHECK"]
               [:span {:style {:backgroundColor "lightgrey"}} (str (:now wld))]])))

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
                       (when (not= (.-scrollLeft n) new-scroll-x)
                         (set! (.-scrollLeft n) new-scroll-x))
                       (when (not= (.-scrollTop n) (- new-scroll-y container-h))
                         (set! (.-scrollTop n) (- new-scroll-y container-h))))))
        c
        (.createClass js/React
                      #js {:shouldComponentUpdate
                           (fn [_next-props _next-state]
                             true)
                           :render
                           (fn []
                             (this-as this
                               (let [props (props this)
                                     world (get props :world)
                                     wld @world
                                     ed-atom (get props :editor)
                                     ed @ed-atom
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
                                     cfg (worlds/current-config wld)
                                     has (:objects cfg)
                                     ha-starts (:objects desc)

                                     grab-w 4
                                     grab-h 4

                                     sel (:selection ed)]
                                 (sab/html [:div {:style       {:backgroundColor "blue"
                                                                :width           (+ container-w 20)
                                                                :height          (+ container-h 20)
                                                                :position        "relative"
                                                                :overflow        "scroll"}
                                                  :tabIndex    0
                                                  :onKeyDown   (fn [evt]
                                                                 (case (.-keyCode evt)
                                                                   8 (do
                                                                       (.preventDefault evt)
                                                                       (let [ed (editor/selection-delete ed @world)]
                                                                         (commit-draft-desc! ed world)
                                                                         (reset! ed-atom ed)))
                                                                   nil))
                                                  :onMouseDown (fn [evt]
                                                                 (let [t (.-currentTarget evt)
                                                                       mx (+ (- (.-pageX evt) (.-offsetLeft t))
                                                                             (.-scrollLeft t))
                                                                       my (+ (- (.-pageY evt) (.-offsetTop t))
                                                                             (.-scrollTop t))
                                                                       [wx wy] (view->world props mx my)
                                                                       wld @world]
                                                                   (println "click at" mx my "->" wx wy)
                                                                   (reset! ed-atom (editor/mouse-down ed wld wx wy (.-shiftKey evt)))))
                                                  :onMouseMove (fn [evt]
                                                                 (let [ed @ed-atom
                                                                       down-point (or (:mouse-down-loc ed) nil)
                                                                       wld @world]
                                                                   (when (some? down-point)
                                                                     ;drag/extend/etc, update desc in some placeholder spot?
                                                                     ; this way can draw overlay of new wall/object/position/size/whatever, while still drawing the old one where it lives.
                                                                     (let [t (.-currentTarget evt)
                                                                           mx (+ (- (.-pageX evt) (.-offsetLeft t))
                                                                                 (.-scrollLeft t))
                                                                           my (+ (- (.-pageY evt) (.-offsetTop t))
                                                                                 (.-scrollTop t))
                                                                           [wx wy] (view->world props mx my)]
                                                                       (reset! ed-atom (editor/mouse-drag ed wld wx wy))))))
                                                  :onMouseUp   (fn [_evt]
                                                                 (let [ed @ed-atom]
                                                                   (when (:mouse-down-loc ed)
                                                                     ;actually change world to match new desc
                                                                     (commit-draft-desc! ed world))
                                                                   (reset! ed-atom (editor/mouse-up @ed-atom))))
                                                  :onScroll    (fn [scroll-evt]
                                                                 (let [n (.-target scroll-evt)]
                                                                   (update-world! world
                                                                                  (fn [w]
                                                                                    (let [[sx sy] (view->world props
                                                                                                               (.-scrollLeft n)
                                                                                                               (+ (.-scrollTop n) container-h))]
                                                                                      (assoc w :scroll-x sx
                                                                                               :scroll-y sy))))))}
                                            (seen-viz-ui/seen-viz world-w world-h
                                                                  x-scale y-scale
                                                                  (:seen-polys wld))
                                            [:svg {:width               (* world-w x-scale)
                                                   :height              (* world-h y-scale)
                                                   :style               {:position "absolute"}
                                                   :preserveAspectRatio "none"
                                                   :viewBox             (str "0 0 " world-w " " world-h)}
                                             [:g {:key "walls"}
                                              (map (fn [[k {x :x y :y w :w h :h}]]
                                                     [:g {:key (str "wall-" k)}
                                                      [:rect {:x     x :y (- world-h h y)
                                                              :width w :height h
                                                              :fill  "white"
                                                              :key   "wall"}]
                                                      (when (contains? sel [:walls k])
                                                        (seq [[:rect {:x            x :y (- world-h h y)
                                                                      :width        w :height h
                                                                      :fill         "url(#diagonal-stripe-1)"
                                                                      :opacity      "0.5"
                                                                      :stroke       "black"
                                                                      :stroke-width 2
                                                                      :key          "selected"}]
                                                              [:rect {:x     (- x (/ grab-w 2)) :y (- world-h h y (/ grab-h 2))
                                                                      :width grab-w :height grab-h
                                                                      :fill  "black"
                                                                      :key   "handle-bl"}]
                                                              [:rect {:x     (- x (/ grab-w 2)) :y (- world-h (/ grab-h 2) y)
                                                                      :width grab-w :height grab-h
                                                                      :fill  "black"
                                                                      :key   "handle-tl"}]
                                                              [:rect {:x     (+ x w (- (/ grab-w 2))) :y (- world-h (/ grab-h 2) y)
                                                                      :width grab-w :height grab-h
                                                                      :fill  "black"
                                                                      :key   "handle-tr"}]
                                                              [:rect {:x     (+ x w (- (/ grab-w 2))) :y (- world-h h y (/ grab-h 2))
                                                                      :width grab-w :height grab-h
                                                                      :fill  "black"
                                                                      :key   "handle-br"}]]))])
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

(defn edit-controls [world ed-atom]
  (let [sel (:selection @ed-atom)]
    (sab/html [:div
               [:div {:style {:position        "absolute"
                              :top             26 :left (+ (:view-width @world) 32)
                              :width           200 :height 400
                              :backgroundColor "red"
                              :fontSize        "12px"}}
                [:p {:style {:margin 0}} "Toolbox"]
                (ui/segmented-control "Create:"
                                      [{:name      "Wall"
                                        :key       :wall
                                        :type      :wall
                                        :prototype {:type :white
                                                    :x    0 :y 0
                                                    :w    16 :h 16}}
                                       {:name      "Goomba"
                                        :type      :ha
                                        :key       :goomba
                                        :prototype {:type  :goomba
                                                    :state :right
                                                    :x     0 :y 0
                                                    :w     16 :h 16}}
                                       {:name      "Mario"
                                        :type      :ha
                                        :key       :mario
                                        :prototype {:type  :mario
                                                    :state :idle-right
                                                    :x     0 :y 0
                                                    :w     16 :h 16}}
                                       {:name      "Flappy"
                                        :type      :ha
                                        :key       :flappy
                                        :prototype {:type  :flappy
                                                    :state :falling
                                                    :x     0 :y 0
                                                    :w     16 :h 16}}]
                                      (:key (:create-mode @ed-atom))
                                      (fn [new-val]
                                        (swap! ed-atom (fn [e]
                                                         (assoc e :create-mode new-val)))))
                [:p "Inspect:"]
                (let [[target-atom target-path]
                      (cond
                        (or (nil? sel) (empty? sel))
                        [ed-atom [:create-mode :prototype]]
                        (and (= 1 (count sel))
                             (nil? (:move-mode @ed-atom))
                             (not= :live-objects (ffirst sel)))
                        [world (concat [:desc] (first sel))]
                        (and (= 1 (count sel))
                             (nil? (:move-mode @ed-atom)))
                        [world (concat [:configs (dec (count (:configs @world))) :objects (second (first sel))])]
                        (= 1 (count sel))
                        [ed-atom (concat [:draft-desc] (first sel))]
                        :else
                        [nil nil])
                      objectish? (cond
                                   (or (nil? sel) (empty? sel)) (= (get-in @ed-atom [:create-mode :type]) :ha)
                                   :else (every? #(not= (first %) :walls) sel))
                      live? (= (first target-path) :configs)
                      get-fn (if live? extrapolated-get-in get-in)]
                  (seq [#_(ui/text-changer target-atom "ID" (concat target-path [:id]) nil)
                        ; editing
                        (ui/text-changer target-atom "Type" (concat target-path [(if live? :ha-type :type)]) inspector-update-key! get-fn)
                        (when objectish?
                          (ui/text-changer target-atom "State" (concat target-path [:state]) inspector-update-key! get-fn))
                        (ui/num-changer target-atom "X" (concat target-path (if live? [:v0] []) [:x]) inspector-update-key! get-fn)
                        (ui/num-changer target-atom "Y" (concat target-path (if live? [:v0] []) [:y]) inspector-update-key! get-fn)
                        (ui/num-changer target-atom "W" (concat target-path (if live? [:v0] []) [:w]) inspector-update-key! get-fn)
                        (ui/num-changer target-atom "H" (concat target-path (if live? [:v0] []) [:h]) inspector-update-key! get-fn)]))]
               (ui/num-changer world "World Width" :width world-update-desc-key!)
               (ui/num-changer world "World Height" :height world-update-desc-key!)
               [:br {:key 0}]
               (ui/num-changer world "Scroll X" :scroll-x world-update-key!)
               (ui/num-changer world "Scroll Y" :scroll-y world-update-key!)
               [:br {:key 1}]
               (ui/num-changer world "Camera Width" :camera-width world-update-key!)
               (ui/num-changer world "Camera Height" :camera-height world-update-key!)
               [:br {:key 2}]
               (ui/num-changer world "View Width" :view-width world-update-key!)
               (ui/num-changer world "View Height" :view-height world-update-key!)
               [:br {:key 3}]

               [:button {:onClick (fn [_evt]
                                    (reset! ed-atom (editor/make-editor)))}
                "Reset editor"]])))

(defn rererender [target]
  (let [w @world
        ed @ed-atom
        quick-check-keys [:now
                          :scroll-x :scroll-y
                          :width :height
                          :camera-width :camera-height
                          :pause-on-change :playing]]
    #_(println "rerere" (identical? last-world w) (not= (:seen-polys last-world) (:seen-polys w)))
    ; slightly weird checks here instead of equality to improve idle performance/overhead
    (when (or (not last-world)
              (not (identical? last-world w))
              (not= (:seen-polys last-world) (:seen-polys w))
              (not last-editor)
              (not= last-editor ed)
              (not= (select-keys last-world quick-check-keys)
                    (select-keys w quick-check-keys))
              (not= (:entry-time (worlds/current-config w))
                    (:entry-time (worlds/current-config last-world))))
      (set! last-world w)
      (set! last-editor ed)
      (js/React.render (sab/html [:div {}
                                  (world-widget #js {"args" {:world  world
                                                             :editor ed-atom}})
                                  (edit-controls world ed-atom)
                                  [:p
                                   {:style {:width      320
                                            :height     240
                                            :float      "left"
                                            :fontFamily "monospace"
                                            :overflow   "scroll"}}
                                   (str "#_:init " (:desc w))]
                                  [:p
                                   {:style {:width      320
                                            :height     240
                                            :float      "left"
                                            :fontFamily "monospace"
                                            :overflow   "scroll"}}
                                   (str "#_:cur " (worlds/world->desc w))]]) target)))
  (.requestAnimationFrame js/window #(rererender target)))