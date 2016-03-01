(ns ha.ha
  (:require
    [clojure.set :as set]
    [ha.intervals :as iv]
    [clojure.string :as string]
    [clojure.walk :as walk]
    ))

(def debug-intervals? false)

#?(:clj (def Infinity Double/POSITIVE_INFINITY))
#?(:clj (def -Infinity Double/NEGATIVE_INFINITY))

(defrecord EdgeDesc [target guard update label])
(defrecord Edge [target guard update label index])
(defrecord State [id flows edges on-enter])
(defrecord HA [ha-type init-vars init-state states])
(defrecord HAVal [ha-type id state entry-time v0])

(defn ha? [ha]
  (instance? HA ha))

(defn ha-val? [hav]
  (instance? HAVal hav))

(defn floor [n]
  #?(:clj  (Math/floor n)
     :cljs (.floor js/Math n)))

(defn ceil [n]
  #?(:clj  (Math/ceil n)
     :cljs (.ceil js/Math n)))

(defn round [n]
  #?(:clj  (Math/round n)
     :cljs (.round js/Math n)))

(defn abs [n]
  #?(:clj  (Math/abs n)
     :cljs (.abs js/Math n)))

(defn sqrt [n]
  #?(:clj  (Math/sqrt n)
     :cljs (.sqrt js/Math n)))

(defn quantize [v u]
  (* u (round (/ v u))))

(defn floor-time [t d]
  (* d (floor (/ t d))))

(defn ceil-time [t d]
  (* d (ceil (/ t d))))

(defn constrain-times [interval time-unit]
  (iv/shrink-intervals (fn [s e]
                         (let [new-start (if (<= s time-unit)
                                           time-unit
                                           (ceil-time s time-unit))
                               new-end (floor-time e time-unit)]
                           (iv/interval new-start new-end)))
                       interval))

(defn third [v] (nth v 2))

(defn current-state [ha hav]
  (get (.-states ha) (.-state hav)))

(defn deriv-var? [kw]
  (and (keyword? kw)
       (= (namespace kw) "v")))

(defn NaN? [num]
  #?(:clj  (Double/isNaN num)
     :cljs (.isNaN js/Number num)))

(defn valuation [hav]
  (.-v0 hav))

(defn extrapolate-flow [v0 flows delta]
  (assert (not (NaN? delta)))
  (assert (number? delta))
  (assert (associative? flows))
  (if (or (= 0 delta)
          (= -0 delta))
    v0
    (reduce
      (fn [val [variable flow]]
        (let [x0 (get v0 variable)
              _ (assert (not (NaN? x0)))
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
                                             #__ #_(soft-assert (or (> acc 0)
                                                                    (<= limit x0))
                                                                "Negative acceleration but limit is higher than cur")
                                             cur (+ x0 (if (= acc 0)
                                                         x0
                                                         (* acc delta)))]
                                         #_(println "c" cur "l" limit)
                                         (assert (not (NaN? cur)))
                                         (assert (not (NaN? limit)))
                                         (if (< acc 0)
                                           (max cur limit)
                                           (min cur limit)))
                        :else (assert false))
                      ; var is regular and...
                      (cond
                        ;4. Flow is a constant
                        (number? flow)
                        (if (and (= delta Infinity) (= 0 flow))
                          x0
                          (do
                            (assert (not (NaN? flow)))
                            (+ x0 (* flow delta))))
                        ;flow is a velocity var and...
                        (deriv-var? flow)
                        (let [acc-flow (get flows flow 0)
                              v0 (get v0 flow 0)]
                          ;(println "2 af" x0 acc-flow v0 delta)
                          (assert (not (NaN? v0)))
                          (assert (not (NaN? delta)))
                          (cond
                            ;5. Acc is 0
                            (= acc-flow 0)
                            (+ x0 (if (= v0 0)
                                    0
                                    (* v0 delta)))
                            ;6. Velocity var's flow is [acc limit] but v0 = limit (slow part = 0)
                            (and (vector? acc-flow) (do (assert (not (NaN? (second acc-flow))))
                                                        (= v0 (second acc-flow))))
                            (if (and (= delta Infinity)
                                     (= 0 v0))
                              x0
                              (+ x0 (if (= v0 0)
                                      0
                                      (* v0 delta))))
                            ;7. Velocity var's flow is [acc limit] and v0 != limit
                            (vector? acc-flow)
                            (let [[acc limit] acc-flow
                                  _ (assert (not (NaN? acc)))
                                  _ (assert (not (NaN? limit)))
                                  #__ #_(soft-assert (or (> acc 0)
                                                         (<= limit v0))
                                                     "Negative acceleration but limit is higher than v0")
                                  cur (if (= acc 0)
                                        v0
                                        (+ v0 (* acc delta)))
                                  ;todo: decelerate to limit if cur exceeds limit. here and elsewhere!
                                  cur (if (< acc 0)
                                        (max cur limit)
                                        (min cur limit))
                                  _ (assert (not= 0 acc))
                                  _ (assert (not= 0 delta))
                                  _ (assert (not (NaN? cur)))
                                  slow-part (cond
                                              (= Infinity delta) 0
                                              (not= cur limit) 1
                                              :else (abs (/ (- limit v0) (* acc delta))))
                                  _ (assert (not (NaN? slow-part)))
                                  avg (+ (* (/ (+ v0 cur) 2) slow-part)
                                         (* limit (- 1 slow-part)))
                                  _ (assert (not (NaN? avg)))]
                              (+ x0 (if (= 0 avg)
                                      0
                                      (* avg delta))))
                            :else (assert false)))
                        :else (assert false)))]
          (when (NaN? x-now)
            (println variable "v0:" x0 "vNow:" x-now)
            (assert (not (NaN? x-now))))
          (assoc val variable x-now)))
      v0
      flows)))

(defn extrapolate [ha hav now]
  (assert (not (NaN? now)))
  (let [delta (- now (.-entry-time hav))]
    (if (or (= 0 delta)
            (= -0 delta))
      hav
      (let [s (current-state ha hav)
            _ (assert (some? s))
            flows (.-flows s)
            _ (assert (some? flows))
            vt (extrapolate-flow (.-v0 hav) flows delta)]
        (assoc hav :v0 vt :entry-time now)))))

(defn constant-from-expr [c]
  (cond
    (number? c) c
    (sequential? c) (apply ({'+ + '- - '* * '/ /} (first c))
                           (map #(constant-from-expr %) (rest c)))))

(defn simple-guard-satisfied? [rel v10 v20 c]
  (let [diff (- v10 v20)]
    (case rel
      :gt (> diff c)
      :geq (>= diff c)
      :leq (<= diff c)
      :lt (< diff c))))

(defn flow-equations [val0 flows xv]
  (let [x0 (get val0 xv 0)
        vx (get flows xv 0)]
    (cond
      ;if x is a deriv var, it is constant if it is not accelerating or if it has reached its limit
      (and (deriv-var? xv)
           (or (= 0 vx)
               (and (vector? vx)
                    (or (= 0 (first vx))
                        (= x0 (second vx)))))) [[0 0 x0 0 Infinity]]
      ;if x is a deriv var, it is linear and then constant if it has not reached its limit
      (and (deriv-var? xv)
           (vector? vx)
           (not= (first vx) 0)
           (not= x0 (second vx)))
      (let [[acc limit] vx
            remaining (- limit x0)
            switch-time (abs (/ remaining acc))]
        [[0 acc x0 0 switch-time]
         [0 0 limit switch-time Infinity]])
      ;x is a regular var:
      ;x constant if vx is 0
      (or (= vx 0)
          ; or vx is a velocity variable which is stuck at 0
          (and (deriv-var? vx)
               (let [xvel (get val0 vx 0)
                     xacc (get flows vx 0)]
                 (and (= xvel 0)
                      (or (= xacc 0)
                          (= xacc [0 0])))))) [[0 0 x0 0 Infinity]]
      ;x linear if vx is non-zero constant
      (or (and (number? vx) (not= vx 0))
          ; or vx is a velocity variable which is stuck at its limit or not accelerating
          (and (deriv-var? vx)
               (let [xvel (get val0 vx 0)
                     xacc (get flows vx 0)]
                 (or (= xacc 0)
                     (and (vector? xacc)
                          (or (= (first xacc) 0)
                              (= xvel (second xacc)))))))) [[0
                                                             (if (deriv-var? vx)
                                                               (get val0 vx 0)
                                                               vx)
                                                             x0
                                                             0
                                                             Infinity]]
      ;x nonlinear if vx is a velocity variable which is accelerating
      ; note that this ignores the limits, so we must consider alternatives
      (and (deriv-var? vx)
           (let [xvel (get val0 vx 0)
                 xacc (get flows vx)]
             (and (vector? xacc)
                  (not= (first xacc) 0)
                  (not= xvel (second xacc)))))
      (let [[acc limit] (get flows vx)
            xvel (get val0 vx 0)
            remaining (- limit xvel)
            delta (- xvel limit)
            switch-time (abs (/ remaining acc))
            switch-intercept (+ (* 0.5 acc switch-time switch-time) (* delta switch-time))]
        [[(* 0.5 acc) xvel x0 0 switch-time]
         ; accelerate as above until switch-time then accelerate at a constant rate
         ; the weird formula here makes it so that the line's y0 satisfies y0 = quadratic(Tswitch) = linear(Tswitch)
         ; .5acc t^2 + xv0 t + x0 = limit t + x0 + c
         ; .5acc t^2 + (xv0 - limit) t - c = 0
         ; .5acc tswitch^2 + (xv0 - limit) tswitch = c
         ; either the quadratic part or the linear part of the movement would have reached y0 at time Tswitch
         [0 limit (+ x0 switch-intercept) switch-time Infinity]])
      :else (assert false))))

(defn find-roots [a b c]
  (cond
    ;quadratic: three intervals. at^2 + bt + c = 0
    (not= a 0) (let [det (- (* b b) (* 4 a c))]
                 (if (< det 0)
                   ; no change. constant within range
                   []
                   (let [root (sqrt det)
                         soln-plus (/ (+ (- b) root) (* 2 a))
                         soln-minus (/ (- (- b) root) (* 2 a))]
                     (assert (not (NaN? soln-plus)))
                     (assert (not (NaN? soln-minus)))
                     (if (< soln-plus soln-minus)
                       [soln-plus soln-minus]
                       [soln-minus soln-plus]))))
    ;linear
    (and (= a 0) (not= b 0)) (let [soln (/ (- c) b)]
                               (assert (not (NaN? soln)))
                               [soln])
    ;constant
    :else []))

(defn get-def [ha-defs ha]
  (get ha-defs (.-ha-type ha)))

(defn simple-guard-interval [ha-defs ha-vals this-ha-val guard time-unit]
  (let [[ha1-id xv] (second guard)
        [ha2-id yv] (if (= (count guard) 4)
                      (third guard)
                      [nil nil])
        ha1-id (if (= ha1-id :$self)
                 (.-id this-ha-val)
                 ha1-id)
        ha2-id (if (= ha2-id :$self)
                 (.-id this-ha-val)
                 ha2-id)
        ;_ (println "check" (.-id this-ha-val) "for" ha1-id ha2-id guard)
        debug? false #_(= guard [:gt :x [:ga :x] 4])
        _ (when debug? (println guard))
        rel (first guard)
        is-eq? (or (= rel :gt) (= rel :lt))
        ha1 (get ha-vals ha1-id)
        def1 (get-def ha-defs ha1)
        ha2 (when ha2-id (get ha-vals ha2-id))
        def2 (when ha2-id (get-def ha-defs ha2))
        ;todo: if the new t0 is > the next required transition time of either ha, return the empty interval
        t0 (:entry-time ha1)
        t0 (if (nil? ha2)
             t0
             (max t0 (:entry-time ha2)))
        tshift (:entry-time this-ha-val)
        ha1 (if (> t0 (:entry-time ha1))
              (extrapolate def1 ha1 t0)
              ha1)
        ha2 (when ha2
              (if (> t0 (:entry-time ha2))
                (extrapolate def2 ha2 t0)
                ha2))
        c (constant-from-expr (last guard))

        ; xeqns is a vec of [coefficients tmin tmax] triples
        ; we take all combinations of the xeqns and yeqns, find roots, and clip them to the given range
        flows1 (:flows (current-state def1 ha1))
        xeqns (if ha1
                (flow-equations (.-v0 ha1) flows1 xv)
                [[0 0 0 0 Infinity]])
        flows2 (when ha2-id (:flows (current-state def2 ha2)))
        yeqns (if ha2
                (flow-equations (.-v0 ha2) flows2 yv)
                [[0 0 0 0 Infinity]])
        ; each equation comes with an interval for which it's valid, and any solution intervals learned from an equation
        ; must be intersected with that overall interval.

        intervals (apply concat
                         (for [[xa xb xc xstart xend] xeqns
                               [ya yb yc ystart yend] yeqns
                               :let [a (- xa ya)
                                     b (- xb yb)
                                     c (- xc yc c)
                                     start (+ tshift (max xstart ystart 0) (if is-eq? 0 time-unit))
                                     end (+ tshift (min xend yend) (if is-eq? 0 (- time-unit)))
                                     roots (find-roots a b c)
                                     valid-interval (iv/interval start end)]]
                           (do
                             (assert (not (NaN? start)))
                             (assert (not (NaN? end)))
                             (cond
                               (empty? roots) [(iv/interval start end)]
                               (= (count roots) 1)
                               (let [soln (first roots)]
                                 [(iv/intersection (iv/interval -Infinity
                                                                (+ tshift soln (if is-eq? 0 (- time-unit))))
                                                   valid-interval)
                                  (iv/intersection (iv/interval (+ tshift soln (if is-eq? 0 time-unit))
                                                                Infinity)
                                                   valid-interval)])
                               (= (count roots) 2)
                               (let [first-soln (first roots)
                                     second-soln (second roots)]
                                 [(iv/intersection (iv/interval -Infinity
                                                                (+ tshift first-soln (if is-eq? 0 (- time-unit))))
                                                   valid-interval)
                                  (iv/intersection (iv/interval (+ tshift first-soln (if is-eq? 0 time-unit))
                                                                (+ tshift second-soln (if is-eq? 0 (- time-unit))))
                                                   valid-interval)
                                  (iv/intersection (iv/interval (+ tshift second-soln (if is-eq? 0 time-unit))
                                                                Infinity)
                                                   valid-interval)])))))
        ; filter to just the intervals where the guard is true
        _ (when debug? (println "Drop unmet" intervals))
        intervals (reduce iv/union
                          nil
                          (filter
                            (fn [intvl]
                              (if (iv/empty-interval? intvl)
                                false
                                (let [start (iv/start intvl)
                                      end (iv/end intvl)]
                                  (assert (some? start))
                                  (assert (some? end))
                                  (let [mid (cond
                                              (= end Infinity) (+ start time-unit)
                                              :else (+ start (/ (- end start) 2)))
                                        _ (assert (not (NaN? mid)))
                                        ha1 (when ha1 (extrapolate def1 ha1 mid))
                                        ha2 (when ha2 (extrapolate def2 ha2 mid))
                                        v1 (if ha1 (get-in ha1 [:v0 xv] 0) 0)
                                        v2 (if ha2 (get-in ha2 [:v0 yv] 0) 0)]
                                    (when debug?
                                      (println "check"
                                               [start end] mid
                                               (map :id [ha1 ha2])
                                               [xv yv]
                                               (first guard) v1 v2 c
                                               (simple-guard-satisfied? (first guard) v1 v2 c)))
                                    (simple-guard-satisfied? (first guard)
                                                             v1
                                                             v2
                                                             c)))))
                            intervals))]
    #_(println "constrain" intervals
               (constrain-times intervals time-unit))
    (constrain-times intervals time-unit)))

(defn guard-replace-self-vars [g id]
  (case (first g)
    nil nil
    (:and :or) (apply vector
                      (first g)
                      (map #(guard-replace-self-vars % id) (rest g)))
    (let [rel (first g)
          a (second g)
          a (cond
              (not (vector? a)) [id a]
              (= (first a) :$self) [id (second a)]
              :else a)
          b (if (= 3 (count g))
              nil
              (third g))
          b (cond
              (nil? b) nil
              (not (vector? b)) [id b]
              (= (first b) :$self) [id (second b)]
              :else b)
          c (last g)]
      (if b
        [rel a b c]
        [rel a c]))))

(def guard-memo nil)

(def memo-hit 0)
(def guard-check 0)

(defmacro with-guard-memo [& body]
  `(do
     (assert (nil? guard-memo))
     (set! guard-memo {})
     (let [r# (do ~@body)]
       (set! guard-memo nil)
       r#)))

(defn memoized-guard [ha-defs ha-vals ha-val g time-unit]
  (set! guard-check (inc guard-check))
  (let [memo-key [(.-id ha-val) g]]
    (if-let [memo (and guard-memo
                       (get guard-memo memo-key))]
      (do
        (set! memo-hit (inc memo-hit))
        memo)
      (let [interval (simple-guard-interval ha-defs ha-vals ha-val g time-unit)]
        (when guard-memo
          (set! guard-memo (assoc guard-memo memo-key interval)))
        interval))))

(defn guard-interval [ha-defs ha-vals ha-val g time-unit]
  ;todo: quantification goes here, using ha-vals and ha-val
  (let [et (:entry-time ha-val)
        min-t (+ et time-unit)
        whole-future (iv/interval min-t Infinity)]
    (if (nil? g)
      whole-future
      (case (first g)
        ;bail early if the intersection becomes empty
        :and (reduce (fn [intvl g]
                       (let [intvl (iv/intersection intvl (guard-interval ha-defs ha-vals ha-val g time-unit))]
                         (if (iv/empty-interval? intvl)
                           (reduced nil)
                           intvl)))
                     whole-future
                     (rest g))
        ;bail early if the union contains [now Infinity]. can we do better?
        :or (reduce (fn [intvl g]
                      (let [intvl (iv/union intvl (guard-interval ha-defs ha-vals ha-val g time-unit))
                            intersection (iv/intersection intvl whole-future)]
                        (if (= intersection whole-future)
                          (reduced whole-future)
                          intvl)))
                    (iv/interval 0 0)
                    (rest g))
        (memoized-guard ha-defs ha-vals ha-val g time-unit)))))


(defn transition-interval [ha-defs ha-vals ha-val transition time-unit]
  #_(println "Transition" (:id ha) "et" (:entry-time ha) (:target transition) (:guard transition))
  (let [interval (guard-interval ha-defs ha-vals ha-val (:guard transition) time-unit)]
    (assert (not= interval []) "Really empty interval!")
    #_(println "interval:" interval)
    ; TODO: handle cases where transition is also guarded on states
    {:interval   interval
     :id         (:id ha-val)
     :transition transition}))

(defn propset-get
  ([ps key] (propset-get ps key nil))
  ([ps key default]
   (let [entry (first (filter #(or (= % key)
                                   (and (sequential? %) (= (first %) key)))
                              ps))]
     (cond
       (nil? entry) default
       (= entry key) true
       :else (second entry)))))

(defn propset-subset? [ps1 ps2 prop]
  (let [v1 (propset-get ps1 prop #{})
        v2 (propset-get ps2 prop #{})]
    (set/subset? v1 v2)))

(defn subsumes-inputs? [e1 e2]
  ;e1's ONs are a subset of e2's ONs
  ;e1's OFFs are a subset of e2's OFFs
  ;e1's PRESSED are a subset of e2's PRESSED
  ;e1's RELEASED are a subset of e2's RELEASED
  (let [l1 (:label e1)
        l2 (:label e2)]
    (and (propset-subset? l1 l2 :on)
         (propset-subset? l1 l2 :off)
         (propset-subset? l1 l2 :pressed)
         (propset-subset? l1 l2 :released))))

(defn required-transition? [edge]
  (contains? (:label edge) :required))

(defn optional-transition? [edge]
  (not (required-transition? edge)))

(defn compare-transition-start [a b]
  (let [ivc (iv/compare-intervals (:interval a) (:interval b))]
    (if (= 0 ivc)
      (compare (:index a) (:index b))
      ivc)))

(defn sort-transitions [ts]
  (sort compare-transition-start ts))

(defn constant-flow-overrides [flow-dict]
  (reduce (fn [vel-vals [k v]]
            (cond
              (deriv-var? k) vel-vals
              (not (deriv-var? v)) (assoc vel-vals (keyword "v" (name k)) v)
              :else vel-vals))
          {}
          flow-dict))

(defn lift-state-entry-dicts [states]
  (into {}
        ;for each state
        (map (fn [[id {edges :edges :as src}]]
               ; update edges by lifting target state entry-update-dicts into transition update-dicts
               [id (assoc
                     (dissoc src :enter-update)
                     :edges
                     (map (fn [{target-id :target update-dict :update :as e}]
                            (if (not= target-id id)
                              (let [enter-update (get-in states [target-id :enter-update] {})]
                                (assoc e :update (merge (or update-dict {}) enter-update)))
                              e))
                          edges))])
             states)))

(defn easy-simplify [g]
  (if (not (vector? g))
    g
    (case (first g)
      (:and :or) (walk/walk (fn [g-in]
                              (easy-simplify g-in))
                            (fn [g]
                              (apply vector (first g) (mapcat (fn [g-in]
                                                                (if (= (first g-in)
                                                                       (first g))
                                                                  (rest g-in)
                                                                  [g-in]))
                                                              (rest g))))
                            g)
      g)))

(defn define-has [defs]
  (zipmap (map :ha-type defs)
          defs))

(defn make-ha [htype init-vars init-state & states]
  (let [states (flatten states)
        states (map (fn [s]
                      (update s :edges
                              (fn [es]
                                (map (fn [e]
                                       (update e :guard
                                               #(guard-replace-self-vars % :$self)))
                                     es))))
                    states)
        ;todo: assert all state flows and updates and edge guards and updates refer only to variables in init-vars
        ;todo: assert init-state is a state in states
        state-ids (map :id states)
        state-dict (zipmap state-ids states)
        state-dict (lift-state-entry-dicts state-dict)]
    (println "ha" htype "#states" (count state-dict))
    (assert (> (count state-dict) 0))
    (HA. htype init-vars init-state state-dict)))

(defn init-ha
  ([ha-desc id] (init-ha ha-desc id (.-init-state ha-desc) 0 (.-init-vars ha-desc)))
  ([ha-desc id init-state t init-vars]
    ;todo: ensure init-vars, init-state proper for ha-desc
   (HAVal. (.-ha-type ha-desc)
           id
           init-state
           t
           (merge (.-init-vars ha-desc) init-vars))))

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
    ; we don't know the edge indices just yet so we build these placeholder records
   (EdgeDesc. target (easy-simplify guard) update-dict label)))

(defn priority-label-edges [edges]
  (vec (map-indexed (fn [i e]
                      (assoc e :index i))
                    edges)))

(defn edge-descs->edges [edges]
  (vec (map-indexed (fn [i e]
                      (Edge. (.-target e) (.-guard e) (.-update e) (.-label e) i))
                    edges)))

(defn make-state [id on-enter flows & edges]
  (let [edges (cond
                (nil? edges) []
                (sequential? edges) (flatten edges)
                :else [edges])
        edges (filter #(not (nil? %)) edges)
        edges (edge-descs->edges edges)]
    (assert (associative? flows))
    (assert (or (nil? on-enter) (associative? on-enter)))
    ;assert every var has either constant or deriv-var flow, and every deriv-var has either 0 or [acc limit] flow
    (doseq [[v f] flows]
      (if (deriv-var? v)
        (assert (or (= f 0) (and (vector? f) (= 2 (count f)) (every? number? f))))
        (assert (or (number? f) (= f (keyword "v" (name v)))))))
    (State. id flows edges on-enter)))

(defn valid-for-inputs [{{label :label _target :target} :transition} inputs]
  (if (= inputs :inert)
    false
    (let [on-inputs (propset-get label :on #{})
          off-inputs (propset-get label :off #{})
          pressed-inputs (propset-get label :pressed #{})
          released-inputs (propset-get label :released #{})]
      #_(when (and
                (not (empty? off-inputs))
                (or (= _target :falling-left)
                    (= _target :falling-right)))
          (println "TGT:" _target
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
           (empty? (set/intersection off-inputs (:on inputs)))))))

;todo: handle quantification
(defn term-dependencies [guard-term]
  (if (nil? guard-term)
    []
    (case (first guard-term)
      (:gt :geq :leq :lt) (if (or (= (count guard-term) 3)
                                  (nil? (third guard-term)))
                            [(first (second guard-term))]
                            [(first (second guard-term)) (first (third guard-term))])
      (:and :or) (mapcat term-dependencies (rest guard-term)))))

;todo: handle quantification
(defn ha-dependencies [ha-def ha-val]
  (into {}
        (map (fn [[sid sdef]]
               [sid (set (map (fn [e]
                                [(.-id ha-val)
                                 sid
                                 (:index e)
                                 (into #{(.-id ha-val)} (filter #(not= % :$self)
                                                                (term-dependencies (:guard e))))])
                              (:edges sdef)))])
             (:states ha-def))))

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
   [:geq vbl min]
   ; vbl <= max --> vbl <= max
   [:leq vbl max]])

(defn between [vbl dim other-ha other-dim]
  ; vbl  >= other-ha.vbl - dim && vbl < other-ha.vbl + other-dim
  ; vbl - other-ha.vbl >= - dim && vbl - other-ha.vbl < other-dim
  [:and
   [:geq vbl [other-ha vbl] (list '- dim)]
   [:leq vbl [other-ha vbl] other-dim]])

(defn bumping-guard [dir other precision]
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
      [:and
       (between-c main-vbl (- omain dim) (- omain (* dim 0.75)))
       (between-c sub-vbl (- osub sub-dim (- precision)) (+ osub sub-odim (- precision)))]
      increasing?
      [:and
       (moving-inc main-vbl width other)
       (between sub-vbl (- sub-dim precision) other (- sub-odim precision))]
      const?
      [:and
       (between-c main-vbl (+ omain (* odim 0.75)) (+ omain odim))
       (between-c sub-vbl (- osub sub-dim (- precision)) (+ osub sub-odim (- precision)))]
      :else
      [:and
       (moving-dec main-vbl width other)
       (between sub-vbl (- sub-dim precision) other (- sub-odim precision))])))

(defn bumping-transitions
  ([id dir next-state extra-guard walls other-has precision]
   (map (fn [other]
          (let [bump-guard (bumping-guard dir other precision)
                guard (if extra-guard
                        [:and bump-guard extra-guard]
                        bump-guard)]
            (make-edge next-state guard
                       #{:required [:this id] [:other other]}
                       {(case dir (:left :right) :v/x (:top :bottom) :v/y) 0})))
        (concat walls other-has)))
  ([id dir1 dir2 next-state extra-guard walls other-has precision]
   (mapcat (fn [o1 o2]
             (if (= o1 o2)
               []
               (let [b1 (bumping-guard dir1 o1 precision)
                     b2 (bumping-guard dir2 o2 precision)
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
  (easy-simplify
    (case (first g)
      nil nil
      :and (apply vector :or (map negate-guard (rest g)))
      :or (apply vector :and (map negate-guard (rest g)))
      :gt (apply vector :leq (rest g))
      :geq (apply vector :lt (rest g))
      :leq (apply vector :gt (rest g))
      :lt (apply vector :geq (rest g)))))

(defn non-bumping-guard [dir walls others precision]
  (negate-guard
    (apply vector :or (map (fn [o] (bumping-guard dir o precision))
                           (concat walls others)))))


(defn enter-state [ha-def ha state update-dict now time-unit precision]
  (let [now (floor-time now time-unit)
        _ (assert (>= now (:entry-time ha)) "Time must be monotonic")
        ; extrapolate ha up to now
        ha (extrapolate ha-def ha now)
        ;_ (println "enter state pre-update posns" (:x ha) (:y ha) (:v/x ha) (:v/y ha))
        ; then merge the result with the update-dict
        ha (update ha :v0
                   merge
                   (or update-dict {})
                   ; replace current v/X with constant flow value of X if present
                   (constant-flow-overrides (get-in ha-def [:states state :flows])))
        ;_ (println "overrides" (:id ha) (constant-flow-overrides (get-in ha [state :flows])))
        ;_ (println "enter state pre-quantized posns" (:x ha) (:y ha) (:v/x ha) (:v/y ha))
        _ (assert state)
        _ (assert (not (NaN? now)))
        ha (update ha :v0 (fn [vals]
                            (reduce
                              (fn [vals k]
                                (assoc vals k (quantize (get vals k) precision)))
                              vals
                              (keys vals))))]
    ; set ha's entry-time to the current moment
    ; set the current state to this state
    (assoc ha :entry-time now
              :state state)))

(defn pick-next-transition [ha-def ha inputs reqs opts]
  (let [_ (doseq [r (concat reqs opts)]
            (let [target (get-in r [:transition :target])
                  cur-state (current-state ha-def ha)
                  out-states (set (map :target (:edges cur-state)))]
              (assert (contains? out-states target)
                      (str "Bad target" target "from" cur-state))))
        [input-interval input-values] (if (= inputs :inert)
                                        [(iv/interval Infinity Infinity) {}]
                                        inputs)
        req (first reqs)
        req-t (if req
                (iv/start (:interval req))
                Infinity)
        valid-interval (iv/interval 0 req-t)
        ; opts on the other hand must be filtered and sliced into range
        opts (if (= inputs :inert)
               []
               (sort-transitions (reduce
                                   (fn [opts trans]
                                     (let [intvl (iv/intersection (:interval trans) input-interval)
                                           intvl (iv/intersection intvl valid-interval)]
                                       (if (or (iv/empty-interval? intvl)
                                               (not (valid-for-inputs trans input-values)))
                                         opts
                                         (conj opts (assoc trans :interval intvl)))))
                                   []
                                   opts)))
        min-opt-t (if (empty? opts)
                    Infinity
                    (iv/start (:interval (first opts))))]
    #_(soft-assert (<= (count opts) 1) "Ambiguous optional transitions")
    #_(soft-assert (or (= Infinity req-t)
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
                 (< (get-in req [:transition :index])
                    (get-in (first opts) [:transition :index]))))
      req
      (first opts))))


(defn kw [& args]
  (keyword (string/join "-" (map #(cond
                                   (or (symbol? %1) (keyword? %1) (string? %1)) (name %1)
                                   (number? %1) (str (round %1))
                                   :else (str %1))
                                 args))))

(defn scale-flows [states multipliers]
  (map (fn [state]
         (update state :flows
                 (fn [flow]
                   (if (empty? multipliers)
                     flow
                     (reduce (fn [flow [k v]]
                               (update flow
                                       k
                                       (if (deriv-var? k)
                                         (fn [old-acc]
                                           (cond
                                             (nil? old-acc) 0
                                             (vector? old-acc) (mapv #(* %1 v) old-acc)
                                             :else (* old-acc v)))
                                         (fn [old-acc]
                                           (* old-acc v)))))
                             flow
                             multipliers)))))
       states))

(defn make-paired-states [a af b bf func]
  (let [a-states (flatten [(func a b)])
        a-states (scale-flows a-states af)
        b-states (flatten [(func b a)])
        b-states (scale-flows b-states bf)]
    (println "flipped" af (map :flows a-states) bf (map :flows b-states))
    (apply vector (concat a-states b-states))))