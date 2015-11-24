(ns player.core
  (:require
    #_[om.core :as om :include-macros true]
    [clojure.set :refer [union]]
    [cljs.tools.reader.edn :as reader]
    #_[clojure.walk :as walk]
    [sablono.core :as sab :include-macros true])
  (:require-macros
    [devcards.core :refer [defcard deftest]]))

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

(defn simple? [i]
  (if-let [[imin imax] i]
    (and (number? imin) (number? imax))
    false))

(defn empty-interval? [i]
  (if (simple? i)
    (> (first i) (second i))
    (every? empty-interval? i)))

(declare merge-overlapping)

(defn intersection [a b]
  (cond
    (or (empty-interval? a) (empty-interval? b)) [Infinity Infinity]
    (and (simple? a) (simple? b)) (let [[amin amax] a
                                        [bmin bmax] b]
                                    (cond
                                      (< bmin amin) (intersection b a)
                                      (< amax bmin) nil
                                      :else [(.max js/Math amin bmin) (.min js/Math amax bmax)]))
    ; b (resp. a) is a disjunction of simple intervals; intersect each with a (resp. b)
    (simple? a) (merge-overlapping (mapv #(intersection a %) b))
    (simple? b) (merge-overlapping (mapv #(intersection b %) a))
    ; both are disjunctions of simple intervals. union of intersections
    ; (a1 u a2 u a3) ^ (b1 u b2 u b3) == (a1 ^ b1 u a1 ^ b2 u a1 ^ b3) u ...
    :else (merge-overlapping (vec
                               ; union of unions of pairwise intersections
                               (mapcat (fn [ai]
                                         ; union of pairwise intersections
                                         (mapv (fn [bi]
                                                 (intersection ai bi))
                                               b))
                                       a)))))

(defn sort-intervals [intervals]
  (sort (fn [a b]
          (cond
            (and (simple? a) (simple? b)) (compare (first a) (first b))
            (simple? a) (compare (first a) (ffirst b))
            (simple? b) (compare (ffirst a) (first b))
            :else (compare (ffirst a) (ffirst b))))
        intervals))

(defn flatten-intervals [intervals]
  (reduce (fn [sofar interval]
            (if (simple? interval)
              (conj sofar interval)
              (into sofar (flatten-intervals interval))))
          []
          intervals))

(defn merge-overlapping [intervals]
  (let [intervals (flatten-intervals intervals)
        intervals (sort-intervals intervals)
        [last-i merged] (reduce (fn [[[amin amax :as a] merged] [bmin bmax :as b]]
                                  (if (intersection a b)
                                    [[amin (.max js/Math amax bmax)] merged]
                                    [[bmin bmax] (conj merged a)]))
                                [(first intervals) []]
                                (rest intervals))]
    (if (empty? intervals)
      []
      (conj merged last-i))))

(defn constrain-times [interval]
  (if (simple? interval)
    [(ceil-time (first interval) time-unit) (floor-time (second interval) time-unit)]
    (mapv constrain-times interval)))

(defn intersect-all [intervals]
  (constrain-times
    (reduce (fn [a b]
              (if-let [intr (intersection a b)]
                intr
                [Infinity Infinity]))
            [time-unit Infinity]
            intervals)))

(defn union-all [intervals]
  (merge-overlapping intervals))

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
                      _other-state (:state other-ha)
                      et (:entry-time ha)
                      _other-et (:entry-time other-ha)
                      ex-other-ha (extrapolate other-ha et)
                      [v _f] (get-var-and-flow has other-ha (second k))
                      [exv f] (get-var-and-flow has ex-other-ha (second k))
                      ]
                  #_(println "remote var and flow" k "from" (keys has) "in state" _other-state "=" [v f]
                             "extrapolated from" _other-et "to" et "=" [exv f])
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
        sat (guard-satisfied? rel v10 v20 c)
        #_(println (str "(" v10 " + " v1f "t) - (" v20 " + " v2f "t) "
                        (case rel :gt ">" :geq ">=" :leq "<=" :lt "<") " " c))
        ; by algebra: A0+fA*dt-B0-fB*dt-C~0 --> (fA-fB)*dt ~ (-A0 + B0 + C) --> dt ~ (-A0 + B0 + C)/(fA-fB)
        denom (- v1f v2f)
        rhs (if (= denom 0)
              Infinity
              (/ (+ (- v10) v20 c)
                 denom))
        ; since we are dividing by denom, flip rel if denom (a constant) < 0
        rel (if (> denom 0)
              rel
              (case rel
                :gt :lt
                :geq :leq
                :leq :geq
                :lt :gt))
        ; t REL rhs
        entry-time (:entry-time ha)
        #_(println (:id ha) simple-guard "et" entry-time "push up" time-unit rhs "to" (+ entry-time time-unit) (+ entry-time rhs) "sat?" sat)
        min-t (+ entry-time time-unit)
        rhs (+ entry-time rhs)]
    (assert (not (nil? v10))
            "V1 must be a valid variable reference")
    (assert (not (nil? v20))
            "V2 must be a valid variable reference")
    (cond
      ;if RHS is +-infinity, then the guard will never flip truth value.
      ;that said, we need to set the minimum actuation time to be min-t.
      (or (= rhs Infinity)
          (= rhs -Infinity)) (if sat
                               [min-t Infinity]
                               [Infinity Infinity])
      ; if t is bounded from above by a number less than time-unit, return an interval which will become empty during intersection
      (and (< rhs min-t)
           (#{:lt :leq} rel)) [-Infinity rhs]
      ; being bounded from below by a number less than time-unit is no problem. all intervals are open.
      :else (case rel
              ;  < : t  < rhs --> guard is true until t exceeds rhs
              :lt [min-t (- rhs (/ time-unit 16))]
              ; <= : t <= rhs --> guard is true until t exceeds or equals rhs
              :leq [min-t rhs]
              ; >= : t >= rhs --> guard becomes true once t exceeds or equals rhs
              :geq [(.max js/Math rhs min-t) Infinity]
              ;  > : t  > rhs --> guard becomes true once t exceeds rhs
              :gt [(.max js/Math (+ rhs (/ time-unit 16)) min-t) Infinity]))))

(defn transition-interval [has ha transition]
  #_(println "Transition" (:id ha) "et" (:entry-time ha) (:target transition) (:guard transition))
  (let [intervals (map #(simple-interval has ha %) (:guard transition))
        interval (intersect-all intervals)]
    #_(println "interval:" intervals "->" interval)
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
  #_(println "enter state" (keys has) (:id ha) state now)
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
        _ (println "New required transitions" (transition-intervals has
                                                                    ha
                                                                    Infinity
                                                                    (required-transitions ha)))
        _ (assert (>= (first (:interval req)) now) "Can't transition until later than entry time")

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
                                         (> start min-t))
                                     trs
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
        deps (into #{} (filter (fn [k]
                                 (some transitioned-ids (ha-dependencies (get has k))))
                               (keys has)))
        reenter-has (map #(let [ha (get has %)]
                           (enter-state has ha (:state ha) t))
                         deps)]
    #_(println "next transitions" #_reenter-has (transition-intervals has
                                                                      (second reenter-has)
                                                                      Infinity
                                                                      (required-transitions (second reenter-has))))
    (merge has (zipmap (map :id reenter-has) reenter-has))))

(defn update-scene [scene now inputs bailout]
  (assert (<= bailout 100) "Recursed too deeply in update-scene")
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
      (= min-t qnow) (do #_(println "clean border")
                       (assoc scene :now now
                                    :objects (follow-transitions has transitions)))
      :else (do #_(println "messy border overflow" (- now min-t))
              (update-scene (assoc scene :now min-t
                                         :objects (follow-transitions has transitions))
                            now
                            inputs
                            (inc bailout)))
      )))

(defonce scene-a (atom {}))
(defonce last-time nil)

(defn moving-inc-c [vbl width limit]
  [[:lt vbl (- limit width)]
   [:geq vbl (list '- limit width [:d vbl])]])

(defn moving-dec-c [vbl limit]
  [[:gt vbl limit]
   [:leq vbl (list '- limit [:d vbl])]])

(defn moving-inc [vbl width other-ha]
  [[:lt vbl [other-ha vbl] (- width)]
   [:geq vbl [other-ha vbl] (list '- [:d other-ha vbl] [:d vbl] width)]])

(defn moving-dec [vbl width other-ha]
  [[:gt vbl [other-ha vbl] width]
   [:leq vbl [other-ha vbl] (list '+ [:d other-ha vbl] width (list '- [:d vbl]))]])

(defn between-c [vbl min max]
  [[:geq vbl min]
   [:lt vbl max]])

(defn goomba [id x y speed state others walls]
  (let [others (disj others id)]
    (make-ha id                                             ;id
             {:x     x :y y                                 ;init
              :w     16 :h 16
              :state state}
             (make-state
               :right                                       ;name
               {:x speed}                                   ;flows
               ;edges
               ; x + 16 < 96 --> x < 96 - 16 && x + 16 + dx*frame >= 80 --> x >= 80 - dx*frame
               (mapcat (fn [[x y w h]]
                         ; left-transition means bumping into left side of wall
                         [(make-edge :left
                                     (concat (moving-inc-c :x 16 x)
                                             (between-c :y 0 100 #_(- y 16) #_(+ y h)))
                                     #{:required [:this id] [:other [:wall x y w h]]})])
                       walls)
               ; x + 16 < x2 && x + dx*frame + 16 >= x2 + dx2*frame
               ; x - x2 < -16 && x - x2 >= dx2*frame - dx*frame - 16
               (map #(make-edge :left (moving-inc :x 16 %) #{:required [:this id] [:other %]}) others))
             (make-state
               :left                                        ;name
               {:x (- speed)}                               ;flows
               ;edges
               ; x > 8 && x + dx*frame <= 8 --> x <= 8 - dx*frame
               (mapcat (fn [[x y w h]]
                         ; right-transition means bumping into right side of wall
                         [(make-edge :right
                                     (concat (moving-dec-c :x (+ x w))
                                             (between-c :y (- y 16) (+ y h)))
                                     #{:required [:this id] [:other [:wall x y w h]]})])
                       walls)
               ; x > x2 + 16 && x + dx*frame <= x2 + dx2*frame + 16 -->
               ;   x - x2 > 16 + dx2 && x - x2 <= dx2*frame + 16 - dx*frame
               ; x - x2 > 16
               (map #(make-edge :right (moving-dec :x 16 %) #{:required [:this id] [:other %]}) others)))))

(defn make-scene-a [x] (let [ids #{:ga :gb :gc :gd}
                             walls #{[0 0 104 8]
                                     [0 8 8 16]
                                     [96 8 8 16]
                                     ;todo: a "waterfall staircase" for goomba fall testing.
                                     }
                             objects [(goomba :ga x 8 16 :right ids walls)
                                      (goomba :gb (+ x 18) 8 16 :left ids walls)
                                      (goomba :gc (+ x 38) 8 16 :right ids walls)
                                      (goomba :gd (+ x 58) 8 16 :left ids walls)
                                      ; TODO: goomba falling off of platforms. add a "staircase" to the right.
                                      ; TODO: mario jumper
                                      ]
                             obj-ids (map :id objects)
                             obj-dict (zipmap obj-ids objects)
                             ; got to let every HA enter its current (initial) state to set up state invariants like
                             ; pending required and optional transitions
                             obj-dict (zipmap obj-ids (map #(enter-state obj-dict % (:state %) 0) objects))]
                         {:now           0
                          :then          0
                          :playing       false
                          :pause-on-play false
                          :objects       obj-dict
                          :walls         walls}))
(defn reset-scene-a! []
  (swap! scene-a (fn [_]
                   (make-scene-a 8))))

(defn ha-states [scene]
  (let [has (sort-by :id (vals (:objects scene)))]
    (map (fn [ha] [(:id ha) (:state ha)]) has)))

(defn tick-frame [t]
  (when-not last-time (set! last-time t))
  (assert (>= t last-time) "Non-monotonic time?")
  (let [old-last-time last-time]
    (set! last-time t)
    (.requestAnimationFrame js/window tick-frame)
    (when (:playing @scene-a)
      (swap! scene-a
             (fn [s] (let [new-s (update-scene s
                                               (+ (:now s) (/ (- t old-last-time) 1000))
                                               #{[(floor-time (:now s) time-unit) #{}]}
                                               0)]
                       (if (and (:pause-on-play new-s)
                                (not= (ha-states s) (ha-states new-s)))
                         (assoc new-s :playing false)
                         new-s)))))))

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

(defcard interval-list-ops
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


(defcard ha-states-card
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
                 (map (fn [ha i]
                        (let [trans-count (count (required-transitions ha))
                              trans-h (/ line-h trans-count)]
                          [:div
                           (map (fn [trans j]
                                  (let [[s e] (:interval trans)
                                        sx (* scale (:x (extrapolate ha s)))
                                        ex (* scale (:x (extrapolate ha e)))
                                        line-top (+ (* i line-h) (* j trans-h))]
                                    [:div {:style {:height        trans-h :width (.abs js/Math (- sx ex))
                                                   :top           line-top :left (.min js/Math sx ex)
                                                   :position      "absolute" :backgroundColor "grey"
                                                   :pointerEvents "none"}}
                                     [:div {:style {:position        "absolute"
                                                    :width           "100px"
                                                    :backgroundColor "rgba(255,255,255,0.5)"
                                                    :pointerEvents   "none"}}
                                      (str (:id ha) "-" (:target (:transition trans)))]
                                     [:div {:style {:height          "100%" :width "2px"
                                                    :position        "absolute" :left (if (< sx ex) "0%" "100%")
                                                    :backgroundColor "green"
                                                    :pointerEvents   "none"}}]
                                     [:div {:style {:height          "100%" :width "2px"
                                                    :position        "absolute" :left (if (< sx ex) "100%" "0%")
                                                    :backgroundColor "red"
                                                    :pointerEvents   "none"}}]]))
                                (transition-intervals (:objects @scene)
                                                      ha
                                                      Infinity
                                                      (required-transitions ha))
                                (range 0 trans-count))]))
                      (map #(extrapolate % (:now @scene)) (vals (:objects @scene)))
                      (range 0 ct)))
               (map (fn [[x y w h]]
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
                                      :color           "white"
                                      :left            (str (* scale x) "px")
                                      :bottom          (str (* scale y) "px")}}
                        (str (:id ha) " " (:state ha))]])
                    (map #(extrapolate % (:now @scene)) (vals (:objects @scene))))
               [:button {:onClick #(swap! scene (fn [s] (assoc s :playing (not (:playing s)))))}
                (if (:playing @scene) "PAUSE" "PLAY")]
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
  ;; conditionally start the app based on whether the #main-app-area
  ;; node is on the page
  (if-let [node (.getElementById js/document "main-app-area")]
    (.requestAnimationFrame js/window #(rererender node))))

(main)
