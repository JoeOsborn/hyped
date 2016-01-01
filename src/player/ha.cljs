(ns player.ha
  (:require
    [clojure.set :as set]
    [player.intervals :as iv])
  (:require-macros
    [player.macros :refer [soft-assert]]))

(def frame-length (/ 1 30))
(def time-units-per-frame 10000)
(def time-unit (/ frame-length time-units-per-frame))
(def precision 0.1)

(def dbg-intervals? false)

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

(defn deriv-var? [kw]
  (and (keyword? kw)
       (= (namespace kw) "v")))

(defn extrapolate [ha now]
  (assert (not (.isNaN js/Number now)))
  (if (= 0 (- now (:entry-time ha)))
    ha
    (let [s (:state ha)
          _ (assert (not (nil? s)))
          flows (:flows (get ha s))
          _ (assert (not (nil? flows)))
          delta (- now (:entry-time ha))
          ;_ (println (str "Delta" now "-" (:entry-time ha)))
          _ (assert (not (.isNaN js/Number delta)))
          _ (assert (associative? flows))
          new-vals (map
                     (fn [[variable flow]]
                       #_(println "extrapolate" variable "given" flow)
                       (let [x0 (get ha variable)
                             _ (assert (not (.isNaN js/Number x0)))
                             x-now (if (deriv-var? variable)
                                     ;var is velocity and...
                                     (cond
                                       ;1. Flow is 0
                                       (= flow 0) x0
                                       ;2. The velocity var is already at the limit
                                       (and (vector? flow) (= x0 (second flow))) x0
                                       ;3. The velocity var is not yet at the limit
                                       (vector? flow) (let [[acc limit] flow
                                                            ; if acc is negative, limit should be below x0
                                                            _ (soft-assert (or (> acc 0)
                                                                               (<= limit x0))
                                                                           "Negative acceleration but limit is higher than cur")
                                                            cur (+ x0 (if (= acc 0)
                                                                        x0
                                                                        (* acc delta)))]
                                                        #_(println "c" cur "l" limit)
                                                        (if (< acc 0)
                                                          (.max js/Math cur limit)
                                                          (.min js/Math cur limit)))
                                       :else (assert false))
                                     ; var is regular and...
                                     (cond
                                       ;4. Flow is a constant
                                       (number? flow)
                                       (if (and (= delta Infinity) (= 0 flow))
                                         x0
                                         (+ x0 (* flow delta)))
                                       ;flow is a velocity var and...
                                       (deriv-var? flow)
                                       (let [acc-flow (get flows flow 0)
                                             v0 (get ha flow 0)]
                                         ;(println "2 af" x0 acc-flow v0 delta)
                                         (cond
                                           ;5. Acc is 0
                                           (= acc-flow 0)
                                           (+ x0 (if (= v0 0)
                                                   0
                                                   (* v0 delta)))
                                           ;6. Velocity var's flow is [acc limit] but v0 = limit (slow part = 0)
                                           (and (vector? acc-flow) (= v0 (second acc-flow)))
                                           (if (and (= delta Infinity)
                                                    (= 0 v0))
                                             x0
                                             (+ x0 (if (= v0 0)
                                                     0
                                                     (* v0 delta))))
                                           ;7. Velocity var's flow is [acc limit] and v0 != limit
                                           (vector? acc-flow)
                                           (let [[acc limit] acc-flow
                                                 _ (soft-assert (or (> acc 0)
                                                                    (<= limit v0))
                                                                "Negative acceleration but limit is higher than v0")
                                                 cur (if (= acc 0)
                                                       v0
                                                       (+ v0 (* acc delta)))
                                                 cur (if (< acc 0)
                                                       (.max js/Math cur limit)
                                                       (.min js/Math cur limit))
                                                 _ (assert (not= 0 (* acc delta)))
                                                 _ (assert (not (.isNaN js/Number cur)))
                                                 slow-part (cond
                                                             (= Infinity delta) 0
                                                             (not= cur limit) 1
                                                             :else (.abs js/Math (/ (- limit v0) (* acc delta))))
                                                 avg (+ (* (/ (+ v0 cur) 2) slow-part)
                                                        (* limit (- 1 slow-part)))]
                                             (+ x0 (if (= 0 avg)
                                                     0
                                                     (* avg delta))))
                                           :else (assert false)))
                                       :else (assert false)))]
                         (when (.isNaN js/Number x-now)
                           (println variable "v0:" x0 "vNow:" x-now))
                         (assert (not (.isNaN js/Number x-now)))
                         [variable x-now]))
                     flows)]
      (merge ha (into {} new-vals)))))

(defn constant-from-expr [c]
  (cond
    (number? c) c
    (seqable? c) (apply ({'+ + '- - '* * '/ /} (first c))
                        (map #(constant-from-expr %) (rest c)))))

(defn simple-guard-satisfied? [rel v10 v20 c]
  (let [diff (- v10 v20)]
    (case rel
      :gt (> diff c)
      :geq (>= diff c)
      :leq (<= diff c)
      :lt (< diff c))))

(defn ha-ref [default term]
  (cond
    (nil? term) nil
    (keyword? term) [(:id default) term]
    (vector? term) term
    :else (assert false)))

(defn flow-equations [ha xv]
  (if (nil? ha)
    [[[0 0 0] 0 Infinity]]
    (let [x0 (get ha xv 0)
          flows (:flows (current-state ha))
          vx (get flows xv 0)]
      (cond
        ;if x is a deriv var, it is constant if it is not accelerating or if it has reached its limit
        (and (deriv-var? xv)
             (or (= 0 vx)
                 (and (vector? vx)
                      (or (= 0 (first vx))
                          (= x0 (second vx)))))) [[[0 0 x0] 0 Infinity]]
        ;if x is a deriv var, it is linear and then constant if it has not reached its limit
        (and (deriv-var? xv)
             (vector? vx)
             (not= (first vx) 0)
             (not= x0 (second vx)))
        (let [[acc limit] vx
              remaining (- limit x0)
              switch-time (.abs js/Math (/ remaining acc))]
          [[[0 acc x0] 0 switch-time]
           [[0 0 limit] switch-time Infinity]])
        ;x is a regular var:
        ;x constant if vx is 0
        (or (= vx 0)
            ; or vx is a velocity variable which is stuck at 0
            (and (deriv-var? vx)
                 (let [xvel (get ha vx 0)
                       xacc (get flows vx 0)]
                   (and (= xvel 0)
                        (or (= xacc 0)
                            (= xacc [0 0])))))) [[[0 0 x0] 0 Infinity]]
        ;x linear if vx is non-zero constant
        (or (and (number? vx) (not= vx 0))
            ; or vx is a velocity variable which is stuck at its limit or not accelerating
            (and (deriv-var? vx)
                 (let [xvel (get ha vx 0)
                       xacc (get flows vx 0)]
                   (or (= xacc 0)
                       (and (vector? xacc)
                            (or (= (first xacc) 0)
                                (= xvel (second xacc)))))))) [[[0 (if (deriv-var? vx)
                                                                    (get ha vx 0)
                                                                    vx) x0] 0 Infinity]]
        ;x nonlinear if vx is a velocity variable which is accelerating
        ; note that this ignores the limits, so we must consider alternatives
        (and (deriv-var? vx)
             (let [xvel (get ha vx 0)
                   xacc (get flows vx)]
               (and (vector? xacc)
                    (not= (first xacc) 0)
                    (not= xvel (second xacc)))))
        (let [[acc limit] (get flows vx)
              xvel (get ha vx 0)
              remaining (- limit xvel)
              delta (- xvel limit)
              switch-time (.abs js/Math (/ remaining acc))
              switch-intercept (+ (* 0.5 acc switch-time switch-time) (* delta switch-time))]
          [[[(* 0.5 acc) xvel x0] 0 switch-time]
           ; accelerate as above until switch-time then accelerate at a constant rate
           ; the weird formula here makes it so that the line's y0 satisfies y0 = quadratic(Tswitch) = linear(Tswitch)
           ; .5acc t^2 + xv0 t + x0 = limit t + x0 + c
           ; .5acc t^2 + (xv0 - limit) t - c = 0
           ; .5acc tswitch^2 + (xv0 - limit) tswitch = c
           ; either the quadratic part or the linear part of the movement would have reached y0 at time Tswitch
           [[0 limit (+ x0 switch-intercept)] switch-time Infinity]])
        :else (assert false)))))

(defn simple-guard-interval [has this-ha guard]
  (let [[ha1-id xv] (ha-ref this-ha (second guard))
        [ha2-id yv] (if (= (count guard) 4)
                      (ha-ref this-ha (third guard))
                      [nil nil])
        dbg? false #_(or (= guard [:lt :y 8]) (= guard [:gt :y 6]))
        _ (when dbg? (println guard))
        rel (first guard)
        is-eq? (or (= rel :gt) (= rel :lt))
        ha1 (get has ha1-id)
        ha2 (when ha2-id (get has ha2-id))
        ;todo: if the new t0 is > the next required transition time of either ha, return the empty interval
        t0 (:entry-time ha1)
        t0 (if (nil? ha2)
             t0
             (.max js/Math t0 (:entry-time ha2)))
        tshift (+ (:entry-time this-ha) time-unit)
        ha1 (if (> t0 (:entry-time ha1))
              (extrapolate ha1 t0)
              ha1)
        ha2 (when ha2
              (if (> t0 (:entry-time ha2))
                (extrapolate ha2 t0)
                ha2))
        c (constant-from-expr (last guard))

        ; xeqns is a vec of [coefficients tmin tmax] triples
        ; we take all combinations of the xeqns and yeqns, find roots, and clip them to the given range
        xeqns (flow-equations ha1 xv)
        yeqns (flow-equations ha2 yv)
        _ (when dbg? (println "check v1:" xeqns "v2:" yeqns "c:" c "f" (:state ha1) (:flows (current-state ha1))
                              (get (:flows (current-state ha1)) :y)
                              (get (:flows (current-state ha1)) :v/y)
                              ))
        ; each equation comes with an interval for which it's valid, and any solution intervals learned from an equation
        ; must be intersected with that overall interval.
        intervals (apply concat
                         (for [[[xa xb xc] xstart xend] xeqns
                               [[ya yb yc] ystart yend] yeqns
                               :let [[a b c] [(- xa ya) (- xb yb) (- xc yc c)]
                                     start (+ tshift (.max js/Math xstart ystart 0) (if is-eq? 0 time-unit))
                                     end (+ tshift (.min js/Math xend yend) (if is-eq? 0 (- time-unit)))]]
                           (do
                             (assert (not (.isNaN js/Number start)))
                             (assert (not (.isNaN js/Number end)))
                             (cond
                               ; quadratic: three intervals. at^2 + bt + c = 0
                               (not= a 0) (let [det (- (* b b) (* 4 a c))]
                                            (when dbg?
                                              (println "tcheck a b c determinant" a b c det)
                                              (println "tcheck intervals" xstart xend ystart yend start end)
                                              (println "tcheck tshift" tshift))
                                            (if (< det 0)
                                              ; no change. constant within range
                                              [[start end]]
                                              (let [root (.sqrt js/Math det)
                                                    soln-plus (/ (+ (- b) root) (* 2 a))
                                                    soln-minus (/ (- (- b) root) (* 2 a))
                                                    [first-soln second-soln] (if (< soln-plus soln-minus)
                                                                               [soln-plus soln-minus]
                                                                               [soln-minus soln-plus])]
                                                (when dbg?
                                                  (println "check" root soln-plus soln-minus)
                                                  (println "tget" (mapv iv/intersection
                                                                        [[-Infinity (+ tshift first-soln (if is-eq? 0 (- time-unit)))]
                                                                         [(+ tshift first-soln (if is-eq? 0 time-unit)) (+ tshift second-soln (if is-eq? 0 (- time-unit)))]
                                                                         [(+ tshift second-soln (if is-eq? 0 time-unit)) Infinity]]
                                                                        (repeat [start end]))))
                                                (assert (not (.isNaN js/Number first-soln)))
                                                (assert (not (.isNaN js/Number second-soln)))
                                                (mapv iv/intersection
                                                      [[-Infinity (+ tshift first-soln (if is-eq? 0 (- time-unit)))]
                                                       [(+ tshift first-soln (if is-eq? 0 time-unit)) (+ tshift second-soln (if is-eq? 0 (- time-unit)))]
                                                       [(+ tshift second-soln (if is-eq? 0 time-unit)) Infinity]]
                                                      (repeat [start end])))))
                               ; linear: two intervals. bt + c = 0 --> t = -c / b
                               (and (= a 0) (not= b 0)) (let [soln (/ (- c) b)]
                                                          (assert (not (.isNaN js/Number soln)))
                                                          (when dbg? (println "tget2"
                                                                              b c tshift
                                                                              start end
                                                                              soln
                                                                              (mapv iv/intersection
                                                                                    [[-Infinity (+ tshift soln (if is-eq? 0 (- time-unit)))]
                                                                                     [(+ tshift soln (if is-eq? 0 time-unit)) Infinity]]
                                                                                    (repeat [start end]))))
                                                          (mapv iv/intersection
                                                                [[-Infinity (+ tshift soln (if is-eq? 0 (- time-unit)))]
                                                                 [(+ tshift soln (if is-eq? 0 time-unit)) Infinity]]
                                                                (repeat [start end])))
                               ; constant: one interval
                               (and (= a 0) (= b 0)) [[start end]]
                               :else (assert false)))))
        intervals (filter (fn [iv] (not (iv/empty-interval? iv)))
                          intervals)
        ; filter to just the intervals where the guard is true
        _ (when dbg? (println "Drop unmet" intervals))
        intervals (filter
                    (fn [[start end]]
                      (let [mid (cond
                                  (= end Infinity) (+ start time-unit)
                                  :else (+ start (/ (- end start) 2)))
                            _ (assert (not (.isNaN js/Number mid)))
                            ha1 (when ha1 (extrapolate ha1 mid))
                            ha2 (when ha2 (extrapolate ha2 mid))]
                        (when dbg? (println "check" [start end] mid (map :id [ha1 ha2]) [xv yv] (first guard) (if ha1 (get ha1 xv 0) 0) (if ha2 (get ha2 yv 0) 0) c (simple-guard-satisfied? (first guard) (if ha1 (get ha1 xv 0) 0) (if ha2 (get ha2 yv 0) 0) c)))
                        (simple-guard-satisfied? (first guard) (if ha1 (get ha1 xv 0) 0) (if ha2 (get ha2 yv 0) 0) c)))
                    intervals)]
    (when dbg? (println "constrain" intervals (iv/merge-overlapping intervals) (constrain-times (iv/merge-overlapping intervals))))
    (constrain-times (iv/merge-overlapping intervals))))

(defn guard-interval [has ha g]
  (if (nil? g)
    [(:entry-time ha) Infinity]
    (case (first g)
      :and (let [intervals (map #(guard-interval has ha %) (rest g))
                 interval (intersect-all intervals)]
             (when dbg-intervals? (println "AND" g intervals "->" interval))
             interval)
      :or (let [intervals (map #(guard-interval has ha %) (rest g))
                interval (union-all intervals)]
            (when dbg-intervals? (println "OR" g intervals "->" interval))
            interval)
      (simple-guard-interval has ha g))))

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

(defn enter-state [has ha state update-dict now]
  (println "enter state" (:id ha) [(:x ha) (:y ha) (:v/x ha) (:v/y ha)] (:state ha) "->" state now)
  (let [now (floor-time now time-unit)
        _ (assert (>= now (:entry-time ha)) "Time must be monotonic")
        ; extrapolate ha up to now
        ha (extrapolate ha now)
        _ (println "enter state pre-update posns" (:x ha) (:y ha) (:v/x ha) (:v/y ha))
        ; then merge the result with the update-dict and the state-entry-dict
        ha (merge ha (or update-dict {}) (get-in ha [state :enter-update] {}))
        _ (println "enter state pre-quantized posns" (:x ha) (:y ha) (:v/x ha) (:v/y ha))
        ; set ha's entry-time to the current moment
        ; set the current state to this state
        _ (assert state)
        _ (assert (not (.isNaN js/Number now)))
        ha (assoc ha :entry-time now
                     :state state
                     :upcoming-transitions []
                     :required-transitions []
                     :optional-transitions [])
        ha (update ha :x #(quantize % precision))
        ha (update ha :y #(quantize % precision))
        ha (update ha :v/x #(quantize % precision))
        ha (update ha :v/y #(quantize % precision))
        ; todo: jump timers, etc... should quantize every var!
        has (assoc has (:id ha) ha)
        _ (println "enter state posns" [(:x ha) (:y ha) (:v/x ha) (:v/y ha)])
        ha (reduce (fn [ha ei] (recalculate-edge has ha ei now))
                   ha
                   (range (count (:edges (current-state ha)))))
        reqs (:required-transitions ha)
        simultaneous-reqs (filter #(= (iv/start-time (:interval %)) (iv/start-time (:interval (first reqs))))
                                  reqs)]
    #_(println "RC:" (count reqs) "SRC:" (count simultaneous-reqs))
    (soft-assert (<= (count simultaneous-reqs) 1)
                 "More than one required transition is available!" simultaneous-reqs)
    (println "New required transitions" (transition-intervals has
                                                              ha
                                                              Infinity
                                                              (required-transitions ha)))
    (println "New optional transitions" (transition-intervals has
                                                              ha
                                                              Infinity
                                                              (optional-transitions ha)))
    (assert (or (nil? (first reqs)) (>= (iv/start-time (:interval (first reqs))) now))
            "Can't transition until later than entry time")
    ha))


(defn make-ha [id init & states]
  (let [states (flatten states)]
    (println "ha" id "#states" (count states))
    (merge {:id id :entry-time 0 :upcoming-transitions []}
           init
           (zipmap (map :id states) states))))

(defn init-has [ha-seq]
  (let [obj-ids (map :id ha-seq)
        obj-dict (zipmap obj-ids ha-seq)]
    ; got to let every HA enter its current (initial) state to set up state invariants like
    ; pending required and optional transitions
    (into {} (map (fn [[k ha]]
                    [k (enter-state obj-dict ha (:state ha) nil 0)])
                  obj-dict))))

(defn guard? [g]
  (or (nil? g)
      (and (vector? g)
           (case (first g)
             (:gt :geq :leq :lt) (or (= (count g) 3) (= (count g) 4))
             (:and :or) (every? guard? (rest g))))))

; edge label is a set containing :required | button masks
(defn make-edge
  ([target guard label] (make-edge target guard label nil))
  ([target guard label update-dict]
   (assert (not (nil? target)) "Target must be non-nil!")
   (assert (guard? guard) "Guard must be a boolean combination of difference formulae.")
   {:target target :guard guard :label label :update update-dict}))

(defn make-state [id on-enter flows & edges]
  (let [edges (cond
                (nil? edges) []
                (seqable? edges) (flatten edges)
                :else [edges])
        edges (filter #(not (nil? %)) edges)
        edges (map (fn [e i]
                     (assoc e :index i))
                   edges
                   (range (count edges)))]
    (assert (associative? flows))
    (assert (or (nil? on-enter) (associative? on-enter)))
    ;assert every var has either constant or deriv-var flow, and every deriv-var has either 0 or [acc limit] flow
    (doseq [[v f] flows]
      (if (deriv-var? v)
        (assert (or (= f 0) (and (vector? f) (= 2 (count f)) (every? number? f))))
        (assert (or (number? f) (deriv-var? f)))))
    {:id id :enter-update on-enter :flows flows :edges edges}))

(defn propset-get [ps key]
  (let [entry (first (filter #(or (= % key)
                                  (and (seqable? %) (= (first %) key)))
                             ps))]
    (if (= entry key)
      true
      (second entry))))

(defn valid-for-inputs [{{label :label target :target} :transition} inputs]
  (let [on-inputs (propset-get label :on)
        off-inputs (propset-get label :off)
        pressed-inputs (propset-get label :pressed)
        released-inputs (propset-get label :released)]
    #_(when (and
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
        transitioned-has (map (fn [{id :id {target :target update-dict :update} :transition}]
                                #_(println "transitioning state-change" id (:entry-time (get has id)) "->" t (:state (get has id)) "->" target)
                                (enter-state has (get has id) target update-dict t))
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

(defn moving-inc [vbl width other-ha]
  [:and
   [:lt vbl [other-ha vbl] (+ (- width) (/ 16 4))]
   [:gt vbl [other-ha vbl] (- width)]])

(defn moving-dec [vbl width other-ha]
  [:and
   ; vbl > o.vbl
   ; vbl - o.vbl > 0
   [:gt vbl [other-ha vbl] (/ width 4)]
   ; vbl <= o.vbl + ow
   ; vbl - o.vbl <= ow
   [:lt vbl [other-ha vbl] width]])

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
      [:and (between-c main-vbl (- omain dim) (- omain (* dim 0.75))) (between-c sub-vbl (- osub sub-dim) (+ osub sub-odim))]
      increasing?
      [:and (moving-inc main-vbl width other) (between sub-vbl sub-dim other sub-odim)]
      const?
      [:and (between-c main-vbl (+ omain (* odim 0.75)) (+ omain odim)) (between-c sub-vbl (- osub sub-dim) (+ osub sub-odim))]
      :else
      [:and (moving-dec main-vbl width other) (between sub-vbl sub-dim other sub-odim)])))

(defn bumping-transitions
  ([id dir next-state extra-guard walls other-has]
   (map (fn [other]
          (let [bump-guard (bumping-guard dir other)
                guard (if extra-guard
                        [:and bump-guard extra-guard]
                        bump-guard)]
            (make-edge next-state guard
                       #{:required [:this id] [:other other]}
                       {(case dir (:left :right) :v/x (:top :bottom) :v/y) 0})))
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
                 [(make-edge next-state guard
                             #{:required [:this id] [:other o1] [:other o2]}
                             {:v/x 0 :v/y 0})])))
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

