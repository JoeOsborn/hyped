(ns player.core
  (:require
    #_[om.core :as om :include-macros true]
    [clojure.set :refer [union]]
    [clojure.walk :as walk]
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
(def time-units-per-frame 4)
(def time-unit (/ frame-length time-units-per-frame))
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

(defn extrapolate [ha now]
  (let [;req (:next-required-transition ha)
        ;_ (assert (or (nil? req) (<= now (first (:interval req)))) "Extrapolating beyond next transition of HA")
        s (:state ha)
        flows (:flows (get ha s))
        delta (- now (:entry-time ha))
        new-vals (map (fn [[variable flow]]
                        [variable (+ (get ha variable) (* flow delta))])
                      flows)]
    (merge ha (into {} new-vals))))

(defn get-var-and-flow [has ha k]
  (assert has "Must provide has")
  (cond
    (nil? k) [0 0]
    (keyword? k) [(quantize (get ha k) precision) (get-in ha [(:state ha) :flows k] 0)]
    (vector? k) (let [other-ha (get has (first k))
                      other-state (:state other-ha)
                      et (:entry-time ha)
                      other-et (:entry-time other-ha)
                      ex-other-ha (extrapolate other-ha et)
                      [v _f] (get-var-and-flow has other-ha (second k))
                      [exv f] (get-var-and-flow has ex-other-ha (second k))
                      ]
                  #_(println "remote var and flow" k "from" (keys has) "in state" other-state "=" [v f]
                             "extrapolated from" other-et "to" et "=" [exv f])
                  [exv f])
    :else (assert (or (nil? k) (keyword? k) (vector? k)) "Unrecognized variable lookup type")))

(defn constant-from-expr [has ha c]
  (cond
    (number? c) c
    (and (vector? c) (= (first c) :d)) (* frame-length (second (apply get-var-and-flow has ha (rest c))))
    (vector? c) (first (get-var-and-flow has ha c))
    (seqable? c) (apply ({'+ + '- - '* * '/ /} (first c))
                        (map #(constant-from-expr has ha %) (rest c)))))

(defn guard-satisfied? [rel v10 v20 c]
  (let [diff (- v10 v20)]
    (case rel
      :gt (> diff c)
      :geq (>= diff c)
      :leq (<= diff c)
      :lt (< diff c))))

(defn simple-interval [has ha simple-guard]
  (let [rel (first simple-guard)
        c (constant-from-expr has ha (last simple-guard))
        ;_ (println "Constant" (last simple-guard) "is" c)
        ;_ (println ":d :x is" (constant-from-expr has ha [:d :x]))
        v1k (second simple-guard)
        v2k (if (= (count simple-guard) 4) (third simple-guard) nil)
        [v10 v1f] (get-var-and-flow has ha v1k)
        [v20 v2f] (get-var-and-flow has ha v2k)
        ; _ (println (str "(" v10 " + " v1f "t) - (" v20 " + " v2f "t) " (case rel :gt ">" :geq ">=" :leq "<=" :lt "<") " " c))
        ; by algebra: A0+fA*dt-B0-fB*dt-C~0 --> (fA-fB)*dt ~ (-A0 + B0 + C) --> dt ~ (-A0 + B0 + C)/(fA-fB)
        denom (- v1f v2f)
        rhs (/ (+ (- v10) v20 c)
               denom)
        ; since we are dividing by denom, flip rel if denom (a constant) < 0
        rel (if (< denom 0)
              (case rel
                :gt :lt
                :geq :leq
                :leq :geq
                :lt :gt)
              rel)
        ; t REL rhs
        entry-time (:entry-time ha)
        ; _ (println (:id ha) simple-guard "et" entry-time "push up" time-unit rhs "to" (+ entry-time time-unit) (+ entry-time rhs))
        min-t (+ entry-time time-unit)
        rhs (+ entry-time rhs)]
    (assert (not (nil? v10))
            "V1 must be a valid variable reference")
    (assert (not (nil? v20))
            "V2 must be a valid variable reference")
    (cond
      ;if RHS is +-infinity, then the guard will never flip truth value
      (or (= rhs Infinity) (= rhs -Infinity)) (if (guard-satisfied? rel v10 v20 c)
                                                [-Infinity Infinity]
                                                [Infinity Infinity])
      ; if t is bounded from above by a number less than time-unit, return an interval which will become empty during intersection
      (and (< rhs min-t) (#{:lt :leq} rel)) [-Infinity rhs]
      ; being bounded from below by a number less than time-unit is no problem. all intervals are open.
      :else (case rel
              ;  < : t  < rhs --> guard is true until t exceeds rhs
              :lt [min-t (- rhs (/ time-unit 16))]
              ; <= : t <= rhs --> guard is true until t exceeds or equals rhs
              :leq [min-t rhs]
              ; >= : t >= rhs --> guard becomes true once t exceeds or equals rhs
              :geq [(.max js/Math rhs min-t) Infinity]
              ;  > : t  > rhs --> guard becomes true once t exceeds rhs
              :gt [(.max js/Math (+ rhs (/ time-unit 16)) min-t) Infinity])
      )))

(defn transition-interval [has ha transition]
  ;(println "Transition" (:id ha) (:x ha) (:target transition) (:guard transition))
  (let [intervals (map #(simple-interval has ha %) (:guard transition))
        interval (intersect-all intervals)]
    ; (println "interval:" intervals "->" interval)
    ; TODO: handle cases where transition is also guarded on states
    {:interval   interval
     :id         (:id ha)
     :transition transition}))

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
  (println "enter state" (keys has) (:id ha) state now)
  (let [now (floor-time now time-unit)
        _ (assert (>= now (:entry-time ha)) "Time must be monotonic")
        ; set the current state to this state
        ; set ha's entry-time to the current moment
        ha (assoc (extrapolate ha now) :entry-time now
                                       :state state)
        req (first (transition-intervals has
                                         ha
                                         Infinity
                                         (required-transitions ha)))
        #_(println "New required transitions" (transition-intervals has
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
  (println "guard:" guard)
  {:target target :guard guard :label label :update identity})

(defn invert-guard [g]
  (case (first g)
    :gt (assoc g 0 :leq)
    :geq (assoc g 0 :lt)
    :leq (assoc g 0 :gt)
    :lt (assoc g 0 :geq)))

(defn make-state [id flows & edges]
  (let [edges (flatten [edges])
        edge-guards (map :guard (filter #(:required (:label %)) edges))]
    ; invariant is a disjunction of negated guards
    (println "es" edges "eguards" edge-guards)
    {:id id :flows flows :edges edges :invariant (map #(map invert-guard %) edge-guards)}))

(defn valid-for-inputs [_transition _inputs]
  ;todo
  false)

(defn next-transition [has ha then inputs]
  (let [; by definition req is after then, so it doesn't need to be filtered or checked
        req (:next-required-transition ha)
        ;non-cached version:
        ; req (first (transition-intervals has ha then (required-transitions ha)))
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

(defn term-dependencies [guard-term]
  (cond
    ; catch [:d ID v]
    (and (vector? guard-term) (= (first guard-term) :d) (= 3 (count guard-term))) [(second guard-term)]
    ; catch [ID v]
    (and (vector? guard-term) (not= (first guard-term) :d) (= 2 (count guard-term))) [(first guard-term)]
    ; must be (+-*/ ...)
    (and (not (vector? guard-term)) (seqable? guard-term)) (mapcat term-dependencies (rest guard-term))
    :else []))

(defn ha-dependencies [ha]
  (let [all-guards (mapcat :guard (:edges (current-state ha)))
        all-ha-refs (mapcat (fn [g] (mapcat term-dependencies (rest g)))
                            all-guards)
        ;_ (println all-ha-refs)
        ]
    (into #{} all-ha-refs)))

(declare scene-a)
(defn follow-transitions [has transitions]
  (let [t (first (:interval (first transitions)))
        _ (assert (every? #(= t (first (:interval %))) transitions) "All transitions must have same start time")
        ;_ (println "Transitioning" transitions)
        ; simultaneously transition all the HAs that can transition.
        transitioned-has (map (fn [{id :id {target :target update :update} :transition}]
                                ;(println "transitioning state-change" id (:entry-time (get has id)) "->" t)
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
    #_(println "next transitions" #_reenter-has (transition-intervals has
                                                                      (second reenter-has)
                                                                      Infinity
                                                                      (required-transitions (second reenter-has))))
    (merge has (zipmap (map :id reenter-has) reenter-has))))

(defn update-scene [scene now inputs]
  (let [qthen (floor-time (:now scene) time-unit)
        qnow (floor-time now time-unit)
        has (:objects scene)
        [min-t transitions] (reduce (fn [[min-t transitions] {[start _] :interval :as trans}]
                                      (cond
                                        (nil? trans) [min-t transitions]
                                        (< start min-t) [start [trans]]
                                        (= start min-t) [min-t (conj transitions trans)]
                                        :else [min-t transitions]))
                                    [Infinity []]
                                    (map #(next-transition has % qthen inputs) (vals has)))]
    (cond
      (> min-t qnow) (assoc scene :now now)
      (= min-t qnow) (do #_(println "clean border") (assoc scene :now now
                                                                 :objects (follow-transitions has transitions)))
      :else (do #_(println "messy border overflow" (- now min-t)) (update-scene (assoc scene :now min-t
                                                                                             :objects (follow-transitions has transitions))
                                                                                now
                                                                                inputs))
      )))

(defonce scene-a (atom {}))
(defonce last-time nil)

(defn goomba [id x y speed state others]
  (make-ha id                                               ;id
           {:x     x :y y                                   ;init
            :w     16 :h 16
            :state state}
           (make-state
             :right                                         ;name
             {:x speed}                                     ;flows
             ;edges
             ; x + 16 < 64 --> x < 64 - 16 && x + 16 + dx*frame >= 64 --> x >= 48 - dx*frame
             (make-edge :left [[:lt :x 48] [:geq :x '(- 48 [:d :x])]] #{:required})
             ; x + 16 < x2 && x + dx*frame + 16 >= x2 + dx2*frame
             ; x - x2 < -16 && x - x2 >= dx2*frame - dx*frame - 16
             (map #(make-edge :left [[:lt :x [% :x] -16]
                                     [:geq :x [% :x] (list '- [:d % :x] [:d :x] 16)]]
                              #{:required}) others))
           (make-state
             :left                                          ;name
             {:x (- speed)}                                 ;flows
             ;edges
             ; x > 8 && x + dx*frame <= 8 --> x <= 8 - dx*frame
             (make-edge :right [[:gt :x 8] [:leq :x '(- 8 [:d :x])]] #{:required})
             ; x > x2 + 16 && x + dx*frame <= x2 + dx2*frame + 16 --> x - x2 > 16 + dx2 && x - x2 <= dx2*frame + 16 - dx*frame
             ; x - x2 > 16
             (map #(make-edge :right [[:gt :x [% :x] 16]
                                      [:leq :x [% :x] (list '+ [:d % :x] 16 (list '- [:d :x]))]]
                              #{:required}) others))))

(defn make-scene-a [x] (let [objects [(goomba :a x 8 8 :right #{:b}) (goomba :b (+ x 18) 8 8 :left #{:a})]
                             obj-ids (map :id objects)
                             obj-dict (zipmap obj-ids objects)
                             ; got to let every HA enter its current (initial) state to set up state invariants like
                             ; pending required and optional transitions
                             obj-dict (zipmap obj-ids (map #(enter-state obj-dict % (:state %) 0) objects))]
                         {:now           0
                          :then          0
                          :playing       false
                          :pause-on-play false
                          :objects       obj-dict}))
(defn reset-scene-a! []
  (swap! scene-a (fn [_]
                   (make-scene-a 8))))

(defn ha-states [scene]
  (let [has (sort-by :id (vals (:objects scene)))]
    (map (fn [ha] [(:id ha) (:state ha)]) has)))

(defn tick-frame [t]
  (when-not last-time (set! last-time t))
  (when (:playing @scene-a)
    (swap! scene-a
           (fn [s] (let [new-s (update-scene s
                                             (+ (:now s) (/ (- t last-time) 1000))
                                             #{[(floor-time (:now s) time-unit) #{}]})]
                     (if (and (:pause-on-play new-s)
                              (not= (ha-states s) (ha-states new-s)))
                       (assoc new-s :playing false)
                       new-s)))))
  (set! last-time t)
  (.requestAnimationFrame js/window tick-frame))
(when (= @scene-a {})
  (.requestAnimationFrame js/window tick-frame)
  (reset-scene-a!))

#_(defcard ha-data
           (fn [scene _owner]
             (let [a (get-in @scene [:objects :a])
                   b (get-in @scene [:objects :b])
                   desc (fn [ha]
                          [[:div "Required transitions:" (str (required-transitions ha))]
                           [:div "Next required transition:" (str (:next-required-transition ha))]
                           [:div "Optional transitions:" (str (optional-transitions ha))]
                           [:div "Intervals:" (str (:optional-transitions ha))]])]
               (sab/html [:div
                          (concat
                            (desc a)
                            (desc b))])))
           scene-a)

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

(defcard ha-states-card
         (fn [scene _owner]
           (ha-states @scene))
         scene-a)

(defn scene-widget [scene owner]
  (let [scale 2
        view-h (str (* scale 240) "px")
        ct (count (:objects @scene))
        line-h (/ (* scale 240) ct)]
    (sab/html [:div {:style {:backgroundColor "blue" :width (str (* scale 320) "px") :height view-h :position "relative"}}
               (map (fn [{x :x y :y w :w h :h :as ha} i]
                      (let [trans-count (count (required-transitions ha))
                            trans-h (/ line-h trans-count)]
                        [:div
                         (map (fn [trans j]
                                (let [[s e] (:interval trans)
                                      sx (* scale (:x (extrapolate ha s)))
                                      ex (* scale (:x (extrapolate ha e)))
                                      line-top (+ (* i line-h) (* j trans-h))]
                                  [:div {:style {:height   trans-h :width (.abs js/Math (- sx ex))
                                                 :top      line-top :left (.min js/Math sx ex)
                                                 :position :absolute :backgroundColor "grey"}}
                                   [:div {:style {:position :absolute :top "64px" :width "200px"}} (str (:id ha) "-" (:target (:transition trans)))]
                                   [:div {:style {:height "100%" :width (* scale 2) :position :absolute :left (if (< sx ex) "0%" "100%") :backgroundColor "green"}}]
                                   [:div {:style {:height "100%" :width (* scale 2) :position :absolute :left (if (< sx ex) "100%" "0%") :backgroundColor "red"}}]]))
                              (transition-intervals (:objects @scene)
                                                    ha
                                                    Infinity
                                                    (required-transitions ha))
                              (range 0 trans-count))]))
                    (map #(extrapolate % (:now @scene)) (vals (:objects @scene)))
                    (range 0 ct))
               (map (fn [{x :x y :y w :w h :h :as ha}]
                      [:div
                       [:div {:style {:width           (str (* scale w) "px") :height (str (* scale h) "px") :borderRadius (str (* scale w) "px")
                                      :backgroundColor "brown"
                                      :position        "absolute" :left (str (* scale x) "px") :bottom (str (* scale y) "px")}}
                        (str (:id ha))]])
                    (map #(extrapolate % (:now @scene)) (vals (:objects @scene))))
               [:button {:onClick #(swap! scene (fn [s] (assoc s :playing (not (:playing s)))))} (if (:playing @scene) "PAUSE" "PLAY")]
               [:span {:style {:backgroundColor "lightgrey"}} "Pause on state change?"
                [:input {:type     "checkbox"
                         :checked  (:pause-on-play @scene)
                         :onChange #(swap! scene (fn [s] (assoc s :pause-on-play (.-checked (.-target %)))))}]]
               [:button {:onClick #(reset-scene-a!)} "RESET"]])))

(defcard draw-scene
         scene-widget
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
  ;; conditionally start the app based on wether the #main-app-area
  ;; node is on the page
  (if-let [node (.getElementById js/document "main-app-area")]
    (.requestAnimationFrame js/window #(rererender node))))

(main)

;; remember to run lein figwheel and then browse to
;; http://localhost:3449/cards.html

