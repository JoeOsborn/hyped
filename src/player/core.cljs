(ns player.core
  (:require
    #_[om.core :as om :include-macros true]
    [clojure.set :as set]
    [clojure.string :as string]
    [cljs.tools.reader.edn :as reader]
    #_[clojure.walk :as walk]
    [sablono.core :as sab :include-macros true]
    [player.intervals :as iv]
    [player.ha :as ha :refer [make-ha make-state make-edge
                              bumping-transitions
                              unsupported-guard non-bumping-guard]])
  (:require-macros
    [devcards.core :refer [defcard deftest]]
    [player.macros :refer [soft-assert]]))

(enable-console-print!)

(declare reset-scene-a!)
(defn reload! [_]
  (reset-scene-a!))

(set! ha/frame-length (/ 1 30))
(set! ha/time-units-per-frame 100)
(set! ha/time-unit (/ ha/frame-length ha/time-units-per-frame))
(set! ha/precision 0.01)

(defonce scene-a (atom {}))
(defonce last-time nil)

(defn kw [& args]
  (keyword (string/join "-" (map #(if (or (symbol? %1) (keyword? %1) (string? %1))
                                   (name %1)
                                   (str %1))
                                 args))))

(defn make-paired-states [a af b bf func]
  (let [a-states (flatten [(func a b)])
        a-states (map #(update % :flows
                               (fn [flow] (if (empty? af)
                                            flow
                                            (map (fn [[k v]]
                                                   (assoc flow k (* (get flow k 0) v)))
                                                 af))))
                      a-states)
        b-states (flatten [(func b a)])
        b-states (map #(update % :flows
                               (fn [flow] (if (empty? bf)
                                            flow
                                            (map (fn [[k v]]
                                                   (assoc flow k (* (get flow k 0) v)))
                                                 bf))))
                      b-states)]
    (apply vector (concat a-states b-states))))

(defn make-accel-states-single [flow-templates func]
  ; flow-templates is a dict of {var-name [min max step]} tuples
  (let [combinations (reduce
                       (fn [flows [varname [min max step]]]
                         (let [r (range min (inc max) step)]
                           (flatten (map (fn [ri]
                                           (map #(assoc %1 varname ri) flows))
                                         r))))
                       [{}]
                       flow-templates)]
    (println "combinations:" combinations)
    (filter #(not= %1 nil)
            (flatten (map func combinations)))))

(defn make-accel-states [& limit-func-pairs]
  (flatten (map (fn [[limits func]] (make-accel-states-single limits func))
                limit-func-pairs)))

(defn goomba [id x y speed state others walls]
  (let [others (disj others id :m)
        fall-speed 16]
    (make-ha id                                             ;id
             {:x     x :y y                                 ;init
              :w     16 :h 16
              :state state}
             ; ground movement pair
             (make-paired-states
               :left {:x (- 1)}
               :right {:x 1}
               #(make-state
                 %1                                         ;name
                 {:x speed}                                 ;flows
                 ;edges
                 (bumping-transitions id %2 %2 nil walls others)
                 ; If nobody is under my new position, enter falling-right
                 (make-edge
                   (kw :falling %1)
                   (unsupported-guard 16 16 walls others)
                   #{:required})))
             ; air movement pair
             (make-paired-states
               :left {:x (- 1)}
               :right {:x 1}
               #(make-state
                 (kw :falling %1)                           ;name
                 {:x speed :y (- fall-speed)}               ;flows
                 ;edges
                 (bumping-transitions id %2 :top %2 nil walls others)
                 (bumping-transitions id %2 (kw :falling %2) nil walls others)
                 (bumping-transitions id :top %1 nil walls others))))))

(defn clear-timers [ha]
  (assoc ha :acc-timer 0))

;todo: abstract!
(defn mario [id x y others walls]
  (let [stand-others #{} #_(disj others id)
        wall-others #{}
        fall-speed 16
        jump-speed 16
        move-speed 24]
    (make-ha id
             {:x     x :y y
              :w     16 :h 16
              :state (kw :idle :right)}
             ; ground movement and idling pairs
             (make-paired-states
               :left {:x -1}
               :right {}
               (fn [dir opp]
                 (vector
                   (make-state
                     (kw :idle dir)
                     {}
                     ;idle -> moving in dir
                     (make-edge
                       (kw :moving dir 1)
                       (non-bumping-guard opp walls wall-others)
                       #{[:on #{dir}]}
                       clear-timers)
                     ;idle -> moving opposite dir
                     (make-edge
                       (kw :moving opp 1)
                       (non-bumping-guard dir walls wall-others)
                       #{[:on #{opp}]}
                       clear-timers)
                     ;idle -> falling
                     (make-edge
                       (kw :falling dir 0 0)
                       (unsupported-guard 16 16 walls stand-others)
                       #{:required}
                       clear-timers)
                     ;idle -> jumping
                     ;todo
                     )
                   (make-accel-states
                     [{:x [0 move-speed 1]}
                      (fn [{vx :x}]
                        [(make-state
                           (kw :moving dir vx)
                           {:x         (case dir :right vx :left (- vx))
                            :acc-timer 1}
                           ;moving -> stopped
                           (bumping-transitions id opp (kw :idle dir) nil walls wall-others)
                           ;moving vx > 0 opposite button on -> skidding
                           (make-edge
                             (kw :skidding dir vx)
                             nil
                             #{[:off #{dir}] [:on #{opp}]}
                             clear-timers)
                           ;moving vx > 0 button off -> braking
                           (make-edge
                             (kw :braking dir vx)
                             nil
                             #{[:off #{dir opp}]})
                           ;moving -> moving (faster)
                           (when (< vx move-speed)
                             (make-edge
                               (kw :moving dir (inc vx))
                               [:and
                                (non-bumping-guard dir walls wall-others)
                                [:geq :acc-timer 1]]
                               #{:required}
                               clear-timers))
                           ;moving -> jumping
                           ;todo
                           ;moving -> falling
                           (make-edge
                             (kw :falling dir vx 0)
                             (unsupported-guard 16 16 walls stand-others)
                             #{:required}
                             clear-timers))
                         (make-state
                           (kw :braking dir vx)
                           {:x (case dir :right vx :left (- vx))
                            :acc-timer 1}
                           ; braking -> idle when hit wall
                           (bumping-transitions id opp (kw :idle dir) nil walls wall-others)
                           ; braking -> idle by deceleration
                           (if (= vx 0)
                             (make-edge
                               (kw :idle dir)
                               nil
                               #{:required}
                               clear-timers)
                             ; braking -> slower breaking
                             [(make-edge
                                (kw :braking dir (dec vx))
                                [:geq :acc-timer 1]
                                #{:required}
                                clear-timers)
                              ; braking -> skidding
                              (make-edge
                                (kw :skidding dir vx)
                                (non-bumping-guard dir walls wall-others)
                                #{[:on #{opp}]}
                                clear-timers)
                              ; braking -> moving
                              (make-edge
                                (kw :moving dir vx)
                                (non-bumping-guard opp walls wall-others)
                                #{[:on #{dir}]}
                                clear-timers)])
                           ;braking -> jumping
                           ;todo
                           (make-edge
                             (kw :falling dir vx 0)
                             (unsupported-guard 16 16 walls stand-others)
                             #{:required}
                             clear-timers))
                         (make-state
                           (kw :skidding dir vx)
                           {:x (case dir :right vx :left (- vx))
                            :acc-timer 1}
                           ; skidding -> idle when hit wall
                           (bumping-transitions id opp (kw :idle dir) nil walls wall-others)
                           ; skidding -> moving in dir by button
                           (make-edge
                             (kw :moving dir vx)
                             nil
                             #{[:off #{opp}] [:on #{dir}]}
                             clear-timers)
                           ; skidding -> braking by release
                           (make-edge
                             (kw :braking dir vx)
                             nil
                             #{[:off #{opp}]}
                             clear-timers)
                           (if (> vx 0)
                             ; skidding -> skidding slower by deceleration
                             (make-edge
                               (kw :skidding dir (dec vx))
                               [:geq :acc-timer 1]
                               #{:required}
                               clear-timers)
                             ; skidding -> moving opp by deceleration through 0
                             (make-edge
                               (kw :moving opp 1)
                               [:geq :acc-timer 1]
                               #{:required}
                               clear-timers)
                             )
                           ;skidding -> jumping
                           ;todo
                           (make-edge
                             (kw :falling dir vx 0)
                             (unsupported-guard 16 16 walls stand-others)
                             #{:required}
                             clear-timers))
                         ])]
                     [{:x [0 move-speed 1]
                       :y [(- fall-speed) jump-speed 1]}
                      (fn [{vx :x vy :y}]
                        (let [landed-state (if (= vx 0)
                                             (kw :idle dir)
                                             (kw :moving dir vx))
                              turning-state-accelerating (if (= vx 0)
                                                           (kw :falling opp 1 (dec vy))
                                                           (kw :falling dir (dec vx) (dec vy)))
                              turning-state-terminal (if (= vx 0)
                                                       (kw :falling opp 1 vy)
                                                       (kw :falling dir (dec vx) vy))]
                          [(make-state
                             (kw :falling dir vx vy)
                             {:x (case dir :right vx :left (- vx))
                              :y vy :acc-timer 1}
                             ; falling -> landed
                             (bumping-transitions id :top landed-state nil walls others)
                             ; falling -> bumped wall
                             (bumping-transitions id opp :top (kw :falling dir 0 vy) nil walls others)
                             (if (< (- fall-speed) vy)
                               ; accelerating downwards
                               [
                                ; falling on right timer no obstacle -> falling faster and accelerating right
                                (when (< vx move-speed)
                                  (make-edge
                                    (kw :falling dir (inc vx) (dec vy))
                                    [:and
                                     [:geq :acc-timer 1]
                                     (non-bumping-guard opp walls wall-others)]
                                    #{[:on #{dir}] [:off #{opp}]}
                                    clear-timers))
                                ; falling on left timer no obstacle -> falling faster and accelerating left, switch to opposite direction if vx-1 <= 0
                                (make-edge
                                  turning-state-accelerating
                                  [:and
                                   [:geq :acc-timer 1]
                                   (non-bumping-guard dir walls wall-others)]
                                  #{[:on #{opp}] [:off #{dir}]}
                                  clear-timers)
                                ; falling off right left timer -> falling faster and not accelerating
                                (make-edge
                                  (kw :falling dir vx (dec vy))
                                  [:geq :acc-timer 1]
                                  #{:required}
                                  clear-timers)
                                ]
                               ; max speed downwards
                               [
                                ; falling on right timer no obstacle -> accelerating right
                                (when (< vx move-speed)
                                  (make-edge
                                    (kw :falling dir (inc vx) vy)
                                    [:and
                                     [:geq :acc-timer 1]
                                     (non-bumping-guard opp walls wall-others)]
                                    #{[:on #{dir}] [:off #{opp}]}
                                    clear-timers))
                                ; falling on left timer no obstacle -> accelerating left, switch to opposite dir if vx-1 <= 0
                                (make-edge
                                  turning-state-terminal
                                  [:and
                                   [:geq :acc-timer 1]
                                   (non-bumping-guard dir walls wall-others)]
                                  #{[:on #{opp}] [:off #{dir}]}
                                  clear-timers)
                                ]
                               )
                             )
                           ;ascending controlled
                           ;todo
                           ;ascending uncontrolled
                           ;todo
                           ]))])))))))

(defn make-scene-a [] (let [ids #{
                                  ;:ga :gb :gc :gd :ge
                                  :m}
                            walls #{[0 0 256 8]
                                    [0 8 8 16]
                                    [96 8 8 16]
                                    [160 8 8 16]}
                            objects [
                                     ;(goomba :ga 8 8 16 :right ids walls)
                                     ;(goomba :gb 32 8 16 :left ids walls)
                                     ;(goomba :gc 11 25 16 :falling-left ids walls)
                                     ;(goomba :gd 64 8 16 :left ids walls)
                                     ;(goomba :ge 96 32 16 :right ids walls)
                                     (mario :m 200 16 ids walls)]
                            obj-ids (map :id objects)
                            obj-dict (zipmap obj-ids objects)
                            ; got to let every HA enter its current (initial) state to set up state invariants like
                            ; pending required and optional transitions
                            obj-dict (zipmap obj-ids (map #(ha/enter-state obj-dict % (:state %) identity 0) objects))]
                        {:now             0
                         :then            0
                         :playing         false
                         :pause-on-change false
                         :objects         obj-dict
                         :walls           walls}))

(defn ha-states [scene]
  (let [has (sort-by :id (vals (:objects scene)))]
    (map (fn [ha] [(:id ha) (:state ha)]) has)))

(def key-states (atom {:on       #{}
                       :pressed  #{}
                       :released #{}}))

(defn reset-scene-a! []
  (swap! key-states (fn [_] {:on #{} :pressed #{} :released #{}}))
  (swap! scene-a (fn [_]
                   (make-scene-a))))

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
      #_(println "KH" (.-keyCode evt) key down?)
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
    (when (:playing @scene-a)
      (swap! scene-a
             (fn [s] (let [new-now (+ (:now s) (/ (- t old-last-time) 1000))
                           new-s (ha/update-scene s
                                                  new-now
                                                  ; assume all keys held now were held since "then"
                                                  @key-states
                                                  0)]
                       (swap! key-states (fn [ks] (assoc ks :pressed #{} :released #{})))
                       (if (and (:pause-on-change new-s)
                                (not= (ha-states s) (ha-states new-s)))
                         (assoc new-s :playing false)
                         new-s)))))))

(when (= @scene-a {})
  (.requestAnimationFrame js/window tick-frame)
  (reset-scene-a!))

#_(defcard sample-time
           "What are the current values of the variables of object a?"
           (fn [scene _owner]
             [(:now @scene)
              (extrapolate (get-in @scene [:objects :a]) (get-in @scene [:now]))])
           scene-a)

#_(defcard ha-deps
           (fn [scene _owner]
             [(ha-dependencies (get-in @scene [:objects :a])) (ha-dependencies (get-in @scene [:objects :b]))])
           scene-a)

#_(defcard interval-list-ops
           (fn [data-atom _]
             (let [{data :data good :good text :text} @data-atom]
               (sab/html [:div
                          [:input {:type      "text"
                                   :style     {:background-color (if good "inherit" "red")
                                               :width            "100%"}
                                   :value     text
                                   :on-change #(swap! data-atom (fn [d]
                                                                  (let [new-text (.-value (.-target %))
                                                                        d (assoc d :text new-text)
                                                                        new-data (try (reader/read-string new-text)
                                                                                      (catch :default _e nil))]
                                                                    (if new-data
                                                                      (assoc d :data new-data :good true)
                                                                      (assoc d :good false)))))}]
                          [:br]
                          (when good
                            [:div
                             [:label (str "Intersections: " (map (fn [di]
                                                                   (map (fn [dj]
                                                                          (str di "," dj ":" (intersection di dj)))
                                                                        data))
                                                                 data))]
                             [:br]
                             [:label (str "Intersect: " (intersect-all data))]
                             [:br]
                             [:label (str "Union: " (union-all data))]])])))
           {:data [[0 1] [2 3]]
            :text "[[0 1] [2 3]]"
            :good true})


#_(defcard ha-states-card
           (fn [scene _owner]
             (ha-states @scene))
           scene-a)

(def show-transition-thresholds true)

(defn scene-widget [scene _owner]
  (let [scale 2
        view-h (str (* scale 240) "px")
        ct (count (:objects @scene))
        line-h (/ (* scale 240) ct)]
    (sab/html [:div {:style {:backgroundColor "blue"
                             :width           (str (* scale 320) "px")
                             :height          view-h
                             :position        "relative"}}
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
                                [(first (:required-transitions ha))])]))
                      (vals (:objects @scene))
                      (range 0 ct))) (map (fn [[x y w h]]
                                            [:div {:style {:width           (str (* scale w) "px") :height (str (* scale h) "px")
                                                           :backgroundColor "white"
                                                           :position        "absolute"
                                                           :left            (str (* scale x) "px")
                                                           :bottom          (str (* scale y) "px")}}])
                                          (:walls @scene))
               (map (fn [{x :x y :y w :w h :h :as ha}]
                      [:div
                       [:div {:style {:width           (str (* scale w) "px") :height (str (* scale h) "px")
                                      :borderRadius    (str (* scale w) "px")
                                      :backgroundColor "brown"
                                      :position        "absolute"
                                      :color           "lightgray"
                                      :left            (str (* scale x) "px")
                                      :bottom          (str (* scale y) "px")}}
                        (str (:id ha) " " (:state ha))]])
                    (map #(ha/extrapolate % (:now @scene)) (vals (:objects @scene))))
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
                                    [:div {:style {:height          (.min js/Math (.abs js/Math (- sy ey)) 8)
                                                   :width           (.min js/Math (.abs js/Math (- sx ex)) 8)
                                                   :bottom          (.min js/Math sy ey)
                                                   :left            (.min js/Math sx ex)
                                                   :position        "absolute"
                                                   :backgroundColor "grey"
                                                   :pointerEvents   "none"}}
                                     [:div {:style {:position        "absolute"
                                                    :width           "100px"
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
                                [(first (:required-transitions ha))]))])
                      (vals (:objects @scene))
                      (range 0 ct)))
               [:button {:onClick #(swap! scene (fn [s] (assoc s :playing (not (:playing s)))))}
                (if (:playing @scene) "PAUSE" "PLAY")]
               [:span {:style {:backgroundColor "lightgrey"}} "Pause on state change?"
                [:input {:type     "checkbox"
                         :checked  (:pause-on-change @scene)
                         :onChange #(swap! scene (fn [s] (assoc s :pause-on-change (.-checked (.-target %)))))}]]
               [:button {:onClick #(reset-scene-a!)} "RESET"]
               [:span {:style {:backgroundColor "lightgrey"}} (str (:now @scene))]])))

(defcard draw-scene
         scene-widget
         scene-a)

#_(defcard ha-data
           (fn [scene _owner]
             (let [objs (:objects @scene)
                   cleanup (fn [t-int]
                             (update t-int
                                     :transition
                                     (fn [t]
                                       (dissoc t :update :guard))))
                   desc (map (fn [[id ha]]
                               [:div
                                (str id)
                                [:div "Required transitions:" (str (map cleanup
                                                                        (transition-intervals
                                                                          objs
                                                                          ha
                                                                          Infinity
                                                                          (required-transitions ha))))]
                                [:div "Optional transitions:" (str (map cleanup
                                                                        (transition-intervals
                                                                          objs
                                                                          ha
                                                                          Infinity
                                                                          (optional-transitions ha))))]])
                             objs)]
               (sab/html [:div desc])))
           scene-a)

#_(defcard next-transition
           "When and what is the next transition of object a?"
           (fn [scene owner]
             (next-transition-ha (get-in @scene [:objects :a]) (get-in @scene [:then])))
           scene-a)

(defonce last-scene-a nil)

(defn rererender [target]
  (when (not= @scene-a last-scene-a)
    (js/React.render (scene-widget scene-a nil) target))
  (.requestAnimationFrame js/window #(rererender target)))

(defn main []
  ;; conditionally start the app based on whether the #main-app-area
  ;; node is on the page
  (if-let [node (.getElementById js/document "main-app-area")]
    (.requestAnimationFrame js/window #(rererender node))))

(main)
