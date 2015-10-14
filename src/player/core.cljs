(ns player.core
  (:require
    #_[om.core :as om :include-macros true]
    [clojure.set :refer [union]]
    [sablono.core :as sab :include-macros true])
  (:require-macros
    [devcards.core :as dc :refer [defcard deftest]]))

(enable-console-print!)

(defn quantize [v u]
  (* u (.floor js/Math (/ v u))))

(defn floor-time [t d]
  (quantize t d))

(defn ceil-time [t d]
  (* d (.ceil js/Math (/ t d))))

(def frame-length (/ 1 30))
(def time-unit (/ frame-length 4))
(def precision 0.001)

(defn empty-interval? [[start end]]
  (> start end))

(defn intersect-all [intervals]
  (let [[start end] (reduce
                      (fn [[amin amax] [bmin bmax]]
                        [(.max js/Math amin bmin) (.min js/Math amax bmax)])
                      [time-unit Infinity]
                      intervals)
        narrow-start (ceil-time start time-unit)
        narrow-end (floor-time end time-unit)]
    (when (and (< start end) (< narrow-end narrow-start))
      (.warn js/console "This interval is narrower than D!" (str [start end]) (str [narrow-start narrow-end])))
    [(ceil-time start time-unit) (floor-time end time-unit)]))

(defn third [v] (nth v 2))

(defn current-state [ha]
  (get ha (:state ha)))

(defn get-var-and-flow [has ha k]
  (cond
    (nil? k) [0 0]
    (keyword? k) [(quantize (get ha k) precision) (get-in ha [(:state ha) :flows k] 0)]
    (vector? k) (get-var-and-flow has (get-in has [:objects (first k)]) (second k))
    :else (assert (or (nil? k) (keyword? k) (vector? k)) "Unrecognized variable lookup type")))

(defn simple-interval [has ha simple-guard]
  (let [rel (first simple-guard)
        c (last simple-guard)
        v1k (second simple-guard)
        v2k (if (= (count simple-guard) 4) (third simple-guard) nil)
        [v10 v1f] (get-var-and-flow has ha v1k)
        [v20 v2f] (get-var-and-flow has ha v2k)
        ; by algebra: A0+fA*dt-B0-fB*dt-C~0 --> (fA-fB)*dt ~ (-A0 + B0 + C) --> dt ~ (-A0 + B0 + C)/(fA-fB)
        denom (- v1f v2f)
        rhs (/ (+ (- v10) v20 c)
               denom)
        ; flip rel if denom (a constant) < 0
        rel (if (< denom 0)
              (case rel
                :gt :lt
                :geq :leq
                :leq :geq
                :lt :gt)
              rel)
        ; t REL rhs
        entry-time (:entry-time ha)
        min-t (+ entry-time time-unit)
        rhs (+ entry-time rhs)]
    (assert (not (nil? v10))
            "V1 must be a valid variable reference")
    (assert (not (nil? v20))
            "V2 must be a valid variable reference")
    (assert (and (not= rhs -Infinity)
                 (not= rhs Infinity)
                 (not (js/Number.isNaN rhs)))
            "RHS was not a valid number. How?")
    ; if t is bounded from above by a number less than time-unit...
    (if (and (< rhs min-t)
             (#{:lt :leq} rel))
      ;return an interval which will become empty during intersection
      [-Infinity rhs]
      ; being bounded from above by a number less than time-unit is no problem. all intervals are open.
      (case rel
        ;  < : t  < rhs --> guard is true until t exceeds rhs
        :lt [min-t (- rhs (/ time-unit 16))]
        ; <= : t <= rhs --> guard is true until t exceeds or equals rhs
        :leq [min-t rhs]
        ; >= : t >= rhs --> guard becomes true once t exceeds or equals rhs
        :geq [(.max js/Math rhs min-t) Infinity]
        ;  > : t  > rhs --> guard becomes true once t exceeds rhs
        :gt [(.max js/Math (+ rhs (/ time-unit 16)) min-t) Infinity]))))

(defn transition-interval [has ha transition]
  ; TODO: handle cases where transition is also guarded on states
  {:interval   (intersect-all (map #(simple-interval has ha %) (:guard transition)))
   :id         (:id ha)
   :transition transition})

(defn extrapolate [ha now]
  (let [req (:next-required-transition ha)
        _ (assert (or (nil? req) (<= now (first (:interval req)))) "Extrapolating beyond next transition of HA")
        s (:state ha)
        flows (:flows (get ha s))
        delta (- now (:entry-time ha))
        new-vals (map (fn [[variable flow]]
                        [variable (+ (get ha variable) (* flow delta))])
                      flows)]
    (merge ha (into {} new-vals))))

(defn required-transitions [ha]
  (filter #(:required (:label %)) (:edges (current-state ha))))

(defn optional-transitions [ha]
  (filter #(not (:required (:label %))) (:edges (current-state ha))))

(defn compare-transition-start [a b]
  (compare (first (:interval a)) (first (:interval b))))

(defn transition-intervals [has ha before-t transitions]
  (sort compare-transition-start
        (filter #(and (not (empty-interval? (:interval %)))
                      (< (first (:interval %)) before-t))
                (map #(transition-interval has ha %)
                     transitions))))

(defn enter-state [has ha state now]
  (let [now (floor-time now time-unit)
        ; set the current state to this state
        ; set ha's entry-time to the current moment
        ha (assoc (extrapolate ha now) :entry-time now
                                       :state state)
        req (first (transition-intervals has
                                         ha
                                         Infinity
                                         (required-transitions ha)))
        ; calculate intervals when optional guards will be satisfied up to and including the upcoming required guard, if any
        opts (transition-intervals has
                                   ha
                                   (if req (first (:interval req)) Infinity)
                                   (optional-transitions ha))]
    (assoc ha :next-required-transition req
              :optional-transitions opts)))

(defn make-ha [id init & states]
  (merge {:id id :entry-time 0}
         init
         (zipmap (map :id states) states)))

; edge label is a set containing :required | button masks
(defn make-edge [target guard label]
  (assert (every? #(#{:gt :geq :leq :lt} (first %)) guard)
          "Guard must be a list of difference formulae.")
  {:target target :guard guard :label label :update identity})

(defn invert-guard [g]
  (case (first g)
    :gt (assoc g 0 :leq)
    :geq (assoc g 0 :lt)
    :leq (assoc g 0 :gt)
    :lt (assoc g 0 :geq)))

(defn make-state [id flows & edges]
  (let [edge-guards (map :guard (filter #(:required (:label %)) edges))]
    ; invariant is a disjunction of negated guards
    {:id id :flows flows :edges edges :invariant (map #(map invert-guard %) edge-guards)}))

(defn valid-for-inputs [_transition _inputs]
  ;todo
  false)

(defn next-transition [ha then inputs]
  (let [; by definition req is after then, so it doesn't need to be filtered or checked
        req (:next-required-transition ha)
        req-t (first (:interval req))
        ; opts on the other hand must be filtered and sliced into range
        [min-opt-t opts] (reduce (fn [[min-t trs] {[start end] :interval :as trans}]
                                   (if
                                     ; ignore invalid...
                                     (or (not (valid-for-inputs trans inputs))
                                         ; already-past...
                                         (<= end then)
                                         ; and too-far-in-the-future transitions
                                         (> start min-t)) trs
                                                          ; use max(then, start) as transition time
                                                          (let [clipped-start (.max js/Math then start)
                                                                ; clip the interval in the transition as appropriate
                                                                trans (assoc trans :interval [clipped-start end])]
                                                            (if (< clipped-start min-t)
                                                              ; this is a new minimum time
                                                              [clipped-start [trans]]
                                                              ; otherwise must be equal to min-t
                                                              [min-t (conj trs trans)]))))
                                 [Infinity []]
                                 (:optional-transitions ha))]
    (assert (not= req-t min-opt-t) "Ambiguous required vs optional transition")
    (when (> (count opts) 1) (.warn js/console "Ambiguous optional transitions"))
    ; this condition should always pass
    (if (< req-t min-opt-t)
      req
      ; we prioritize the first-defined optional transition. this policy could change later, e.g. to be an error.
      (first opts))))

(defn ha-dependencies [_ha] #{})

(defn follow-transitions [has transitions]
  (let [t (first (:interval (first transitions)))
        _ (assert (every? #(= t (first (:interval %))) transitions) "All transitions must have same start time")
        ; simultaneously transition all the HAs that can transition.
        transitioned-has (map (fn [{id :id {target :target update :update} :transition}]
                                (enter-state has (update (get has id)) target t))
                              transitions)
        transitioned-ids (into #{} (map :id transitioned-has))
        ; merge into HAS. note that their intervals may not be correct right now due to ordering sensitivity!
        has (merge has (zipmap (map :id transitioned-has) transitioned-has))
        ; get dependencies of transitioned HAs.
        ; note that these may include some of the transitioned HAs: given the ordering sensitivity
        ; mentioned above, they might have calculated their new intervals based on stale information.
        ; calculating intervals is idempotent and has no second-order effects so it is fine to do it repeatedly
        ; and it also suffices to do it a single time once all the HAs are updated with new times, values and flows.
        deps (into #{} (filter (fn [k] (some transitioned-ids (ha-dependencies (get has k)))) (keys has)))
        reenter-has (map #(let [ha (get has %)]
                           (enter-state has ha (:state ha) t))
                         deps)]
    (merge has (zipmap (map :id reenter-has) reenter-has))))

(defn update-scene [scene now inputs]
  (let [qthen (floor-time (:now scene) time-unit)
        qnow (floor-time now time-unit)
        has (:objects scene)
        [min-t transitions] (reduce (fn [[min-t transitions] {[start _] :interval :as trans}]
                                      (cond
                                        (< start min-t) [start [trans]]
                                        (= start min-t) [min-t (conj transitions trans)]
                                        :else [min-t transitions]))
                                    [Infinity []]
                                    (map #(next-transition % qthen inputs) (vals has)))]
    (cond
      (> min-t qnow) (assoc scene :now now)
      (= min-t qnow) (assoc scene :now now
                                  :objects (follow-transitions has transitions))
      :else (update-scene (assoc scene :now min-t
                                       :objects (follow-transitions has transitions))
                          now
                          inputs)
      )))

(defonce scene-a (atom {}))
(defonce last-time nil)

(defn goomba [id x y speed]
  (make-ha id                                               ;id
           {:x     x :y y                                   ;init
            :w     16 :h 16
            :state :right}
           (make-state :right                               ;name
                       {:x speed}                           ;flows
                       ;edges
                       ; x < 16 && x + dx*frame >= 16 --> x >= 16 - dx*frame
                       (make-edge :left [[:lt :x 16] [:geq :x (- 16 (* frame-length speed))]] #{:required}))
           (make-state :left                                ;name
                       {:x (- speed)}                       ;flows
                       ;edges
                       ; x > 8 && x + dx*frame <= 8 --> x <= 8 - dx*frame
                       (make-edge :right [[:gt :x 8] [:leq :x (- 8 (* frame-length (- speed)))]] #{:required}))))

(defn make-scene-a [x] (let [objects [(goomba :a x 8 8)]
                             obj-ids (map :id objects)
                             obj-dict (zipmap obj-ids objects)
                             ; got to let every HA enter its current (initial) state to set up state invariants like
                             ; pending required and optional transitions
                             obj-dict (zipmap obj-ids (map #(enter-state obj-dict % (:state %) 0) objects))]
                         {:now     0
                          :then    0
                          :playing false
                          :objects obj-dict}))
(defn reset-scene-a! []
  (swap! scene-a (fn [_]
                   (make-scene-a 8))))

(defn tick-frame [t]
  (when-not last-time (set! last-time t))
  (when (:playing @scene-a)
    (swap! scene-a
           (fn [s] (update-scene s
                                 (+ (:now s) (/ (- t last-time) 1000))
                                 #{[(floor-time (:now s) time-unit) #{}]}))))
  (set! last-time t)
  (.requestAnimationFrame js/window tick-frame))
(when (= @scene-a {})
  (.requestAnimationFrame js/window tick-frame)
  (reset-scene-a!))

(defcard ha-data
         (fn [scene _owner]
           (let [a (get-in @scene [:objects :a])]
             (sab/html [:div
                        [:div "Required transitions:" (str (required-transitions a))]
                        [:div "Next required transition:" (str (:next-required-transition a))]
                        [:div "Optional transitions:" (str (optional-transitions a))]
                        [:div "Intervals:" (str (:optional-transitions a))]])))
         scene-a)

(defcard enter-trans
         (let [a (get-in (make-scene-a 16) [:objects :a])
               a (enter-state {:a a} a :right 0)]
           (:next-required-transition (enter-state {:a a} a :left 0))))

#_(defcard sample-time
           "What are the current values of the variables of object a?"
           (fn [scene _owner]
             [(:now @scene)
              (extrapolate (get-in @scene [:objects :a]) (get-in @scene [:now]))])
           scene-a)

(defcard draw-scene
         (fn [scene _owner]
           (let [scale 2]
             (sab/html [:div {:style {:backgroundColor "blue" :width (str (* scale 320) "px") :height (str (* scale 240) "px") :position "relative"}}
                        (map (fn [{x :x y :y w :w h :h}]
                               [:div {:style {:width           (str (* scale w) "px") :height (str (* scale h) "px") :borderRadius (str (* scale w) "px")
                                              :backgroundColor "brown"
                                              :position        "absolute" :left (str (* scale x) "px") :bottom (str (* scale y) "px")}}])
                             (map #(extrapolate % (:now @scene)) (vals (:objects @scene))))
                        [:button {:onClick #(do (swap! scene (fn [s] (assoc s :playing (not (:playing s))))) true)} (if (:playing @scene) "PAUSE" "PLAY")]
                        [:button {:onClick #(reset-scene-a!)} "RESET"]])))
         scene-a)


#_(defcard next-transition
           "When and what is the next transition of object a?"
           (fn [scene owner]
             (next-transition-ha (get-in @scene [:objects :a]) (get-in @scene [:then])))
           scene-a)

(defn main []
  ;; conditionally start the app based on wether the #main-app-area
  ;; node is on the page
  (if-let [node (.getElementById js/document "main-app-area")]
    (js/React.render (sab/html [:div "This is working"]) node)))

(main)

;; remember to run lein figwheel and then browse to
;; http://localhost:3449/cards.html

