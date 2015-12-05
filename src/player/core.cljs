(ns player.core
  (:require
    #_[om.core :as om :include-macros true]
    [clojure.set :refer [union]]
    [cljs.tools.reader.edn :as reader]
    #_[clojure.walk :as walk]
    [sablono.core :as sab :include-macros true]
    [player.intervals :as iv])
  (:require-macros
    [devcards.core :refer [defcard deftest]]
    [player.macros :refer [soft-assert]]))

(enable-console-print!)

(declare reset-scene-a!)
(defn reload! [_]
  (reset-scene-a!))

(def frame-length (/ 1 30))
(def time-units-per-frame 1000)
(def time-unit (/ frame-length time-units-per-frame))
(def precision 0.001)

(defn quantize [v u]
  (* u (.round js/Math (/ v u))))

(defn floor-time [t d]
  (* d (.floor js/Math (/ (+ t (/ d 10.0)) d))))

(defn ceil-time [t d]
  (* d (.ceil js/Math (/ (- t (/ time-unit 10.0)) d))))

(defn constrain-times [interval]
  (iv/map-simple-intervals (fn [s e]
                             [(ceil-time s time-unit) (floor-time e time-unit)])
                           interval))

(defn intersect-all [intervals]
  (if (iv/simple? intervals)
    intervals
    (reduce (fn [a b]
              (if-let [intr (iv/intersection a b)]
                intr
                [Infinity Infinity]))
            [time-unit Infinity]
            intervals)))

(defn union-all [intervals]
  (iv/merge-overlapping intervals))

(defn third [v] (nth v 2))

(defn current-state [ha]
  (get ha (:state ha)))

(defn extrapolate [ha now]
  (let [s (:state ha)
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
    (keyword? k) [(get ha k) (get-in ha [(:state ha) :flows k] 0)]
    (vector? k) (let [other-ha (get has (first k))
                      _other-state (:state other-ha)
                      et (:entry-time ha)
                      _other-et (:entry-time other-ha)
                      ex-other-ha (extrapolate other-ha et)
                      [_v _f] (get-var-and-flow has other-ha (second k))
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

(defn simple-guard-satisfied? [rel v10 v20 c]
  (let [diff (- v10 v20)]
    (case rel
      :gt (> diff c)
      :geq (>= diff c)
      :leq (<= diff c)
      :lt (< diff c))))

;TODO: if the other HA would transition _before_ rhs, then this interval must be empty.
(defn simple-interval [has ha simple-guard]
  (let [rel (first simple-guard)
        c (constant-from-expr has ha (last simple-guard))
        ;_ (println "Constant" (last simple-guard) "is" c)
        v1k (second simple-guard)
        v2k (if (= (count simple-guard) 4) (third simple-guard) nil)
        [v10 v1f] (get-var-and-flow has ha v1k)
        [v20 v2f] (get-var-and-flow has ha v2k)
        sat (simple-guard-satisfied? rel v10 v20 c)
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
    (constrain-times
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
                :lt [min-t (- rhs time-unit)]
                ; <= : t <= rhs --> guard is true until t exceeds or equals rhs
                :leq [min-t rhs]
                ; >= : t >= rhs --> guard becomes true once t exceeds or equals rhs
                :geq [(.max js/Math rhs min-t) Infinity]
                ;  > : t  > rhs --> guard becomes true once t exceeds rhs
                :gt [(.max js/Math (+ rhs time-unit) min-t) Infinity])))))

(defn guard-interval [has ha g]
  (if (not g)
    [(:entry-time ha) Infinity]
    (case (first g)
      :and (let [intervals (map #(guard-interval has ha %) (rest g))
                 interval (intersect-all intervals)]
             #_(println "AND" g intervals "->" interval)
             interval)
      :or (let [intervals (map #(guard-interval has ha %) (rest g))
                interval (union-all intervals)]
            #_(println "OR" g intervals "->" interval)
            interval)
      (simple-interval has ha g))))

(defn transition-interval [has ha transition]
  #_(println "Transition" (:id ha) "et" (:entry-time ha) (:target transition) (:guard transition))
  (let [interval (iv/merge-overlapping (guard-interval has ha (:guard transition)))]
    (assert (not= interval []) "Really empty interval!")
    #_(println "interval:" interval)
    ; TODO: handle cases where transition is also guarded on states
    {:interval   interval
     :id         (:id ha)
     :transition transition}))

(defn required-transitions [ha]
  (filter #(contains? (:label %) :required) (:edges (current-state ha))))

(defn optional-transitions [ha]
  (filter #(not (contains? (:label %) :required)) (:edges (current-state ha))))

(defn compare-transition-start [a b]
  (or (iv/compare-intervals (:interval a) (:interval b))
      (compare (:index a) (:index b))))

(defn transition-intervals [has ha before-t transitions]
  (sort compare-transition-start
        (filter #(not (iv/empty-interval? (:interval %)))
                (map #(let [transition-data (transition-interval has ha %)]
                       (update transition-data
                               :interval
                               (fn [i]
                                 (iv/intersection i [-Infinity before-t]))))
                     transitions))))

(defn recalculate-edge [has ha index t]
  (let [edge (nth (:edges (current-state ha)) index)
        ;todo: Does this suffice? Should the transition be intersected with "the future" in any other places, eg update-scene or next-transition?
        transition (update (transition-interval has ha edge)
                           :interval (fn [intvl]
                                       (iv/intersection intvl [t Infinity])))
        ha (assoc-in ha [:upcoming-transitions index] transition)]
    #_(println "recalc" (:id ha) index)
    #_(println "REQS" (:id ha) (:entry-time ha) #_transition
               (sort compare-transition-start
                     (filter #(and
                               (contains? (get-in % [:transition :label]) :required)
                               (not (iv/empty-interval? (:interval %))))
                             (:upcoming-transitions ha))))
    (if (contains? (get-in transition [:transition :label]) :required)
      (assoc ha :required-transitions (sort compare-transition-start
                                            (filter #(and
                                                      (contains? (get-in % [:transition :label]) :required)
                                                      (not (iv/empty-interval? (:interval %))))
                                                    (:upcoming-transitions ha))))
      (assoc ha :optional-transitions (sort compare-transition-start
                                            (filter #(and
                                                      (not (contains? (get-in % [:transition :label]) :required))
                                                      (not (iv/empty-interval? (:interval %))))
                                                    (:upcoming-transitions ha)))))))

(defn enter-state [has ha state now]
  (println "enter state" (:id ha) [(:x ha) (:y ha)] (:state ha) "->" state now)
  (let [now (floor-time now time-unit)
        _ (assert (>= now (:entry-time ha)) "Time must be monotonic")
        ; set the current state to this state
        ; set ha's entry-time to the current moment
        ha (assoc (extrapolate ha now) :entry-time now
                                       :state state
                                       :upcoming-transitions []
                                       :required-transitions []
                                       :optional-transitions [])
        ha (update ha :x #(quantize % precision))
        ha (update ha :y #(quantize % precision))
        _ (println "enter state posns" [(:x ha) (:y ha)])
        ha (reduce (fn [ha ei] (recalculate-edge has ha ei now))
                   ha
                   (range (count (:edges (current-state ha)))))
        reqs (:required-transitions ha)
        simultaneous-reqs (filter #(= (iv/start-time (:interval %)) (iv/start-time (:interval (first reqs))))
                                  reqs)]
    #_(println "RC:" (count reqs) "SRC:" (count simultaneous-reqs))
    (soft-assert (<= (count simultaneous-reqs) 1)
                 "More than one required transition is available!" simultaneous-reqs)
    #_(println "New required transitions" (transition-intervals has
                                                                ha
                                                                Infinity
                                                                (required-transitions ha)))
    (assert (or (nil? (first reqs)) (>= (iv/start-time (:interval (first reqs))) now))
            "Can't transition until later than entry time")
    ha))


(defn make-ha [id init & states]
  (merge {:id id :entry-time 0 :upcoming-transitions []}
         init
         (zipmap (map :id states) states)))

(defn guard? [g]
  (or (nil? g)
      (and (vector? g)
           (case (first g)
             (:gt :geq :leq :lt) (or (= (count g) 3) (= (count g) 4))
             (:and :or) (every? guard? (rest g))))))

; edge label is a set containing :required | button masks
(defn make-edge [target guard label]
  (assert (guard? guard) "Guard must be a boolean combination of difference formulae.")
  {:target target :guard guard :label label :update identity})

(defn make-state [id flows & edges]
  (let [edges (cond
                (nil? edges) []
                (seqable? edges) (flatten edges)
                :else [edges])
        edges (map (fn [e i]
                     (assoc e :index i))
                   edges
                   (range (count edges)))
        edge-guards (map :guard (filter #(contains? (:label %) :required) edges))]
    ; invariant is a disjunction of negated guards
    {:id id :flows flows :edges edges}))

(defn intersect-input-intervals [transition inputs]
  (let [label (get-in transition [:transition :label])
        interval (:interval transition)
        ; for each button, intersect its interval with the transition to find the intervals during which each
        ; button is pressed. The result is an interval during which any of the given buttons is pressed.
        ; then take the intersection of those per-button intervals to find the intervals during which
        ; all the indicated buttons are pressed.
        on (intersect-all (map #(iv/intersection (get inputs %) interval) (some #(= (first %) :on) label)))
        ; for off, we want no buttons from off to be active during on. so we don't do the final intersection!
        off (map #(iv/intersection (get inputs %) on) (some #(= (first %) :off) label))]
    (if (iv/empty-interval? off)
      (assoc transition :interval on)
      [Infinity Infinity])))

(defn next-transition [_has ha then inputs]
  (let [reqs (:required-transitions ha)
        _ (doseq [r reqs]
            (let [target (get-in r [:transition :target])
                  cur-state (current-state ha)
                  out-states (into #{} (map :target (:edges cur-state)))]
              (assert (contains? out-states target)
                      (str "Bad target" target "from" cur-state))))
        req (first reqs)
        req-t (iv/start-time (:interval req))
        ; opts on the other hand must be filtered and sliced into range
        ; todo: simplify
        [min-opt-t opts] (reduce (fn [[min-t trs] {intvl :interval :as trans}]
                                   (let [intvl (iv/intersection (:interval trans) [then Infinity])
                                         trans (intersect-input-intervals (assoc trans :interval intvl) inputs)
                                         intvl (:interval trans)
                                         [start end] (iv/first-subinterval intvl)]
                                     ; ignore impossible...
                                     (if (or (iv/empty-interval? intvl)
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
                                           [min-t (conj trs trans)])))))
                                 [Infinity []]
                                 (:optional-transitions ha))]
    (assert (or (= Infinity req-t)
                (not= req-t min-opt-t))
            "Ambiguous required vs optional transition")
    (soft-assert (<= (count opts) 1) "Ambiguous optional transitions")
    (if (and req (< req-t min-opt-t))
      req
      (first opts))))

(defn term-dependencies [guard-term]
  (cond
    ; catch guards
    (and (vector? guard-term)
         (#{:gt :geq :leq :lt :and :or} (first guard-term))) (mapcat term-dependencies (rest guard-term))
    ; catch [ID v]
    (and (vector? guard-term)
         (= 2 (count guard-term))) [(first guard-term)]
    ; must be (+-*/ ...)
    (and (not (vector? guard-term))
         (seqable? guard-term)) (mapcat term-dependencies (rest guard-term))
    :else []))

(defn ha-dependencies [ha]
  (into #{} (map (fn [e] [(:id ha) (:index e) (term-dependencies (:guard e))])
                 (:edges (current-state ha)))))

(declare scene-a)
(defn follow-transitions [has transitions]
  (let [t (iv/start-time (:interval (first transitions)))
        _ (assert (every? #(= t (iv/start-time (:interval %))) transitions) "All transitions must have same start time")
        ;_ (println "Transitioning" transitions)
        ; simultaneously transition all the HAs that can transition.
        transitioned-has (map (fn [{id :id {target :target update :update} :transition}]
                                #_(println "transitioning state-change" id (:entry-time (get has id)) "->" t (:state (get has id)) "->" target)
                                (enter-state has (update (get has id)) target t))
                              transitions)
        transitioned-ids (into #{} (map :id transitioned-has))
        ;_ (println "changed" transitioned-ids)
        ; merge into HAS. note that their intervals may not be correct right now due to ordering sensitivity!
        has (merge has (zipmap (map :id transitioned-has) transitioned-has))
        ; get dependencies of transitioned HAs.
        ; note that these may include some of the transitioned HAs: given the ordering sensitivity
        ; mentioned above, they might have calculated their new intervals based on stale information.
        ; calculating intervals is idempotent and has no second-order effects so it is fine to do it repeatedly
        ; and it also suffices to do it a single time once all the HAs are updated with new times, values and flows.
        ; todo: cache these?
        deps (filter (fn [[_id _idx deps]]
                       #_(println "accept?" [_id _idx deps] "of" transitioned-ids ":" (some transitioned-ids deps))
                       (some transitioned-ids deps))
                     (mapcat #(let [ha-deps (ha-dependencies %)]
                               #_(println "accept? ha-deps" % ha-deps)
                               ha-deps)
                             (vals has)))
        ;_ (println "deps" deps)
        ; No need to worry about ordering effects here, recalculating edges will not change any behaviors
        ; or entry times so there's no problem with doing it in any order.
        has (reduce (fn [has [id idx _deps]]
                      (let [ha (get has id)]
                        #_(println "T recalc" id)
                        (assoc has id (recalculate-edge has ha idx t))))
                    has
                    deps)]
    #_(println "next transitions" #_reenter-has (transition-intervals has
                                                                      (second reenter-has)
                                                                      Infinity
                                                                      (required-transitions (second reenter-has))))
    has))

(defn update-scene [scene now inputs bailout]
  (assert (<= bailout 100) "Recursed too deeply in update-scene")
  (let [qthen (floor-time (:now scene) time-unit)
        qnow (floor-time now time-unit)
        has (:objects scene)
        [min-t transitions] (reduce (fn [[min-t transitions] {intvl :interval :as trans}]
                                      (let [intvl (iv/intersection intvl [qthen now])
                                            start (iv/start-time intvl)]
                                        (cond
                                          (iv/empty-interval? intvl) [min-t transitions]
                                          (nil? trans) [min-t transitions]
                                          (< start min-t) [start [trans]]
                                          (= start min-t) [min-t (conj transitions trans)]
                                          :else [min-t transitions])))
                                    [Infinity []]
                                    (map #(next-transition has % qthen inputs) (vals has)))]
    (println "recur" bailout "now" now qnow "then" qthen "mt" min-t "tr" transitions)
    (cond
      ; this also handles the min-t=Infinity case
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
  [:and
   [:lt vbl (- limit (/ width 4))]
   [:geq vbl (- limit width)]])

(defn moving-dec-c [vbl limit]
  [:and
   [:gt vbl (- limit (/ 16 4))]
   [:leq vbl limit]])

(defn moving-inc [vbl width other-ha]
  [:and
   [:lt vbl [other-ha vbl] (+ (- width) (/ 16 4))]
   [:geq vbl [other-ha vbl] (- width)]])

(defn moving-dec [vbl width other-ha]
  [:and
   ; vbl > o.vbl
   ; vbl - o.vbl > 0
   [:gt vbl [other-ha vbl] (/ width 4)]
   ; vbl <= o.vbl + ow
   ; vbl - o.vbl <= ow
   [:leq vbl [other-ha vbl] width]])

(defn between-c [vbl min max]
  [:and
   ; vbl >= min --> vbl >= min
   [:gt vbl min]
   ; vbl <= max --> vbl <= max
   [:lt vbl max]])

(defn between [vbl dim other-ha other-dim]
  ; vbl  >= other-ha.vbl - dim && vbl < other-ha.vbl + other-dim
  ; vbl - other-ha.vbl >= - dim && vbl - other-ha.vbl < other-dim
  [:and
   [:gt vbl [other-ha vbl] (list '- dim)]
   [:lt vbl [other-ha vbl] other-dim]])

(defn bumping-guard [dir other]
  (let [main-vbl (case dir (:left :right) :x (:top :bottom) :y)
        sub-vbl (case main-vbl :x :y :y :x)
        increasing? (case dir (:left :bottom) true (:right :top) false)
        const? (not (keyword? other))
        width 16
        height 16
        [ox oy ow oh] (if const? other [[other :x] [other :y] width height])
        dim (case main-vbl :x width :y height)
        omain (case main-vbl :x ox :y oy)
        osub (case sub-vbl :x ox :y oy)
        odim (case main-vbl :x ow :y oh)
        sub-dim (case sub-vbl :x width :y height)
        sub-odim (case sub-vbl :x ow :y oh)]
    (cond
      (and const? increasing?)
      [:and (moving-inc-c main-vbl dim omain) (between-c sub-vbl (- osub sub-dim) (+ osub sub-odim))]
      increasing?
      [:and (moving-inc main-vbl dim other) (between sub-vbl sub-dim other sub-odim)]
      const?
      [:and (moving-dec-c main-vbl (+ omain odim)) (between-c sub-vbl (- osub sub-dim) (+ osub sub-odim))]
      :else
      [:and (moving-dec main-vbl dim other) (between sub-vbl sub-dim other sub-odim)])))

(defn bumping-transitions
  ([id dir next-state extra-guard walls other-has]
   (map (fn [other]
          (let [bump-guard (bumping-guard dir other)
                guard (if extra-guard
                        [:and bump-guard extra-guard]
                        bump-guard)]
            (make-edge next-state guard #{:required [:this id] [:other other]})))
        (concat walls other-has)))
  ([id dir1 dir2 next-state extra-guard walls other-has]
   (mapcat (fn [o1 o2]
             (if (= o1 o2)
               []
               (let [b1 (bumping-guard dir1 o1)
                     b2 (bumping-guard dir2 o2)
                     guard (if extra-guard
                             [:and b1 b2 extra-guard]
                             [:and b1 b2])]
                 [(make-edge next-state guard #{:required [:this id] [:other o1] [:other o2]})])))
           (concat walls other-has)
           (concat walls other-has))))

(defn unsupported-guard [w h walls others]
  (apply vector :and
         (concat
           ; currently unsupported
           (map (fn [other]
                  (if (keyword? other)
                    (let [ow w
                          oh h]
                      [:or
                       ; position.x + width < other.x
                       ; i.e. x+w < ox i.e. x - ox < - w
                       [:leq :x [other :x] (- w)]
                       ; position.x is > other.x + other.w
                       ; i.e. x > ox+ow i.e. x - ox > ow
                       [:geq :x [other :x] ow]
                       ; position.y + height is < other.y
                       [:leq :y [other :y] (- h)]
                       ; position.y is > other.y + other.h
                       [:gt :y [other :y] oh]])
                    (let [[ox oy ow oh] other]
                      [:or
                       ; position.x + width < other.x
                       ; i.e. x+w < ox i.e. x < ox - w
                       [:leq :x (- ox w)]
                       ; position.x is > other.x + other.w
                       ; i.e. x > ox+ow i.e. x > ox+ow
                       [:geq :x (+ ox ow)]
                       ; position.y + height is < other.y --> position.y < other.y - h
                       [:leq :y (- oy h)]
                       ; position.y is > other.y + other.h
                       [:gt :y (+ oy oh)]])))
                (concat walls others)))))

(defn negate-guard [g]
  (case (first g)
    :and (apply vector :or (map negate-guard (rest g)))
    :or (apply vector :and (map negate-guard (rest g)))
    :gt (apply vector :leq (rest g))
    :geq (apply vector :lt (rest g))
    :leq (apply vector :gt (rest g))
    :lt (apply vector :geq (rest g))))

(defn non-bumping-guard [dir walls others]
  (negate-guard
    (apply vector :or (map (fn [o] (bumping-guard dir o))
                           (concat walls others)))))

(defn goomba [id x y speed state others walls]
  (let [others (disj others id)
        fall-speed 16]
    (make-ha id                                             ;id
             {:x     x :y y                                 ;init
              :w     16 :h 16
              :state state}
             (make-state
               :right                                       ;name
               {:x speed}                                   ;flows
               ;edges
               (bumping-transitions id :left :left nil walls others)
               ; If nobody is under my new position, enter falling-right
               (make-edge
                 :falling-right
                 (unsupported-guard 16 16 walls others)
                 #{:required [:this id]}))
             (make-state
               :left                                        ;name
               {:x (- speed)}                               ;flows
               ;edges
               (bumping-transitions id :right :right nil walls others)
               (make-edge
                 :falling-left
                 (unsupported-guard 16 16 walls others)
                 #{:required [:this id]}))
             (make-state
               :falling-right
               {:x speed :y (- fall-speed)}
               (bumping-transitions id :left :top :left nil walls others)
               (bumping-transitions id :left :falling-left nil walls others)
               (bumping-transitions id :top :right nil walls others))
             (make-state
               :falling-left
               {:x (- speed) :y (- fall-speed)}
               (bumping-transitions id :right :top :right nil walls others)
               (bumping-transitions id :right :falling-right nil walls others)
               (bumping-transitions id :top :left nil walls others)))))

(defn mario [id x y others walls]
  (let [others (disj others id)
        fall-speed 16
        move-speed 24]
    (make-ha id
             {:x     x :y y
              :w     16 :h 16
              :state :idle-right}
             (make-state
               :idle-right
               {}
               (make-edge
                 :moving-right
                 (non-bumping-guard :left walls others)
                 #{[:on #{:right}]})
               (make-edge
                 :moving-left
                 (non-bumping-guard :right walls others)
                 #{[:on #{:left}]}))
             (make-state
               :idle-left
               {}
               (make-edge
                 :moving-right
                 (non-bumping-guard :left walls others)
                 #{[:on #{:right}]})
               (make-edge
                 :moving-left
                 (non-bumping-guard :right walls others)
                 #{[:on #{:left}]}))
             (make-state
               :moving-right
               {:x move-speed}
               (make-edge
                 :idle-right
                 nil
                 #{[:off #{:right}]}))
             (make-state
               :moving-left
               {:x (- move-speed)}
               (make-edge
                 :idle-left
                 nil
                 #{[:off #{:left}]})))))

(defn make-scene-a [] (let [ids #{:ga :gb :gc :gd :ge :m}
                            walls #{[0 0 256 8]
                                    [0 8 8 16]
                                    [96 8 8 16]
                                    [160 8 8 16]}
                            objects [(goomba :ga 8 8 16 :right ids walls)
                                     (goomba :gb 32 8 16 :left ids walls)
                                     (goomba :gc 11 25 16 :falling-left ids walls)
                                     (goomba :gd 64 8 16 :left ids walls)
                                     (goomba :ge 96 32 16 :right ids walls)
                                     (mario :m 200 8 ids walls)]
                            obj-ids (map :id objects)
                            obj-dict (zipmap obj-ids objects)
                            ; got to let every HA enter its current (initial) state to set up state invariants like
                            ; pending required and optional transitions
                            obj-dict (zipmap obj-ids (map #(enter-state obj-dict % (:state %) 0) objects))]
                        {:now             0
                         :then            0
                         :playing         false
                         :pause-on-change false
                         :objects         obj-dict
                         :walls           walls}))

(defn ha-states [scene]
  (let [has (sort-by :id (vals (:objects scene)))]
    (map (fn [ha] [(:id ha) (:state ha)]) has)))

(def key-history (atom [{:time     0
                         :on       #{}
                         :pressed  #{}
                         :released #{}}]))

(def key-intervals (atom {}))

(defn reset-scene-a! []
  (swap! key-history (fn [_] [{:time 0 :on #{} :pressed #{} :released #{}}]))
  (swap! key-intervals (fn [_] {}))
  (swap! scene-a (fn [_]
                   (make-scene-a))))

(def keycode->keyname
  {37 :left
   39 :right
   38 :up
   40 :down
   90 :run
   88 :jump})

#_(defn binary-search-posn-by [coll key val l r depth]
    (assert (<= depth 1000))
    (let [len (- r l)]
      (if (= len 0)
        l
        (let [mid (+ l (.floor js/Math (/ len 2)))
              mid-val (key (get coll mid))]
          (cond
            (= val mid-val) mid
            (< val mid-val) (binary-search-posn-by coll key val l mid (inc depth))
            (> val mid-val) (binary-search-posn-by coll key val (inc mid) r (inc depth))
            :else (assert false))))))

#_(defn key-status-at [history t]
    (let [found-index (binary-search-posn-by history :time t 0 (dec (count history)) 0)
          found (nth history found-index nil)]
      (cond
        (nil? found) (last history)
        (> (:time found) t) nil
        :else found)))

(defn key-handler [evt]
  (.preventDefault evt)
  (.-stopPropagation evt)
  (let [now (floor-time (:now @scene-a) time-unit)
        key (keycode->keyname (.-keyCode evt))
        down? (= (.-type evt) "keydown")]
    #_(println "KH" (.-keyCode evt) key down?)
    (swap! key-history (fn [ks]
                         ; todo: clear the history sometimes?
                         (let [prev-on (:on (last ks))
                               prev-time (:time (last ks))
                               ; add a new entry if necessary
                               ks (if (> now prev-time)
                                    (conj ks {:time now :on prev-on :pressed #{} :released #{}})
                                    ks)]
                           (assert (>= now prev-time))
                           (update ks (dec (count ks))
                                   (fn [{prev-on :on pressed :pressed released :released :as k}]
                                     ; need the extra contains? check so key-repeat doesn't confuse things.
                                     (let [just-pressed? (and down?
                                                              (not (contains? prev-on key)))]
                                       (when (or just-pressed?
                                                 (not down?))
                                         (swap! key-intervals update key
                                                (if down?
                                                  (fn [old-kis]
                                                    (conj old-kis [now Infinity]))
                                                  (fn [old-kis]
                                                    (update-in old-kis [(dec (count old-kis)) 1]
                                                               (fn [_] now))))))
                                       (assoc k :on (if down? (conj prev-on key)
                                                              (disj prev-on key))
                                                :pressed (if just-pressed?
                                                           (conj pressed key)
                                                           pressed)
                                                :released (if down? released (conj released key)))))))))))

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
                           new-s (update-scene s
                                               new-now
                                               key-intervals
                                               0)]
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
                                        ha-s (extrapolate ha s)
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
                    (map #(extrapolate % (:now @scene)) (vals (:objects @scene))))
               (when show-transition-thresholds
                 (map (fn [ha]
                        [:div
                         (when (not (empty? (:required-transitions ha)))
                           (map (fn [trans]
                                  (let [[s e] (iv/first-subinterval (:interval trans))
                                        ha-s (extrapolate ha s)
                                        ha-e (extrapolate ha e)
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
