(ns player.ha
  (:require
    [clojure.set :as set]
    [player.intervals :as iv])
  (:require-macros
    [player.macros :refer [soft-assert]]))

(def frame-length (/ 1 30))
(def time-units-per-frame 100)
(def time-unit (/ frame-length time-units-per-frame))
(def precision 0.01)

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
  (if (nil? g)
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
        ;todo: Does this suffice? Should the transition be intersected with "the future" in any other places, eg update-scene or next-transition? Does that explain the weird interval calculated for :m in the initial setup?
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
  (let [states (flatten states)]
    (merge {:id id :entry-time 0 :upcoming-transitions []}
           init
           (zipmap (map :id states) states))))

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
                   (range (count edges)))]
    ; invariant is a disjunction of negated guards
    {:id id :flows flows :edges edges}))

(defn propset-get [ps key]
  (let [entry (first (filter #(or (= % key)
                                  (= (first %) key))
                             ps))]
    (if (= entry key)
      true
      (second entry))))

(defn valid-for-inputs [{{label :label target :target} :transition} inputs]
  (let [on-inputs (propset-get label :on)
        off-inputs (propset-get label :off)
        pressed-inputs (propset-get label :pressed)
        released-inputs (propset-get label :released)]
   #_ (when (and
            (not (empty? off-inputs))
            (or (= target :falling-left)
                (= target :falling-right)))
      (println "TGT:" target
               "OFF:" off-inputs
               "INS:" (:on inputs)
               "INT:" (set/intersection off-inputs (:on inputs))
               "OK?:" (empty? (set/intersection off-inputs (:on inputs)))
               "ALL:" (and (set/subset? on-inputs (:on inputs))
                           (set/subset? pressed-inputs (:pressed inputs))
                           (set/subset? released-inputs (:released inputs))
                           (empty? (set/intersection off-inputs (:on inputs))))))
    (and (set/subset? on-inputs (:on inputs))
         (set/subset? pressed-inputs (:pressed inputs))
         (set/subset? released-inputs (:released inputs))
         (empty? (set/intersection off-inputs (:on inputs))))))

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
        [min-opt-t opts] (reduce (fn [[min-t trs] trans]
                                   (let [intvl (iv/intersection (:interval trans) [then Infinity])
                                         [start end] (iv/first-subinterval intvl)]
                                     ; ignore impossible...
                                     (if (or (iv/empty-interval? intvl)
                                             (not (valid-for-inputs trans inputs))
                                             ; already-past...
                                             (<= end then)
                                             ; and too-far-in-the-future transitions
                                             (> start min-t))
                                       [min-t trs]
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
    (soft-assert (<= (count opts) 1) "Ambiguous optional transitions")
    (soft-assert (or (= Infinity req-t)
                     (not= req-t min-opt-t))
                 "Ambiguous required vs optional transition")
    #_(when (and (= (:id ha) :m)
               (or (= (:state ha) :falling-left)
                   (= (:state ha) :falling-right)
                   (= (:state ha) :falling-idle-left)
                   (= (:state ha) :falling-idle-right)))
      (println "m opts" (:state ha) opts))
    ; pick whichever has lower index between req and (first opts)
    (if (and req
             (<= req-t min-opt-t)
             (or (empty? opts)
                 (< (get-in req [:transition :index]) (get-in (first opts) [:transition :index]))))
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
    #_(println "recur" bailout "now" now qnow "then" qthen "mt" min-t "tr" transitions)
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
                            ; clear pressed and released instant stuff
                            (assoc inputs :pressed #{} :released #{})
                            (inc bailout)))
      )))

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

