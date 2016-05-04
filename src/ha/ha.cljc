(ns ha.ha
  (:require
    [clojure.set :as set]
    [ha.intervals :as iv]
    [clojure.string :as string]
    [clojure.walk :as walk]
    ))

#?(:clj (def Infinity Double/POSITIVE_INFINITY))
#?(:clj (def -Infinity Double/NEGATIVE_INFINITY))

(defrecord EdgeDesc [target guard update label])
(defrecord Edge [target guard update label index])
(defrecord State [id collider-set flows edges on-enter])
(defrecord HA [ha-type collider-sets init-vars init-state states])
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

(defn third [v] (nth v 2))

(defn current-state [ha hav]
  (get (.-states ha) (.-state hav)))

(defn deriv-var? [kw]
  (and (keyword? kw)
       (= (namespace kw) "v")))

(defn spy [& v]
  (apply println v)
  (last v))

(defn NaN? [num]
  #?(:clj  (Double/isNaN num)
     :cljs (.isNaN js/Number num)))

(defn valuation [hav]
  (.-v0 hav))

(def extrapolations 0)

(defn extrapolate-flow-single-var [variable v0 flows delta]
  (let [flow (get flows variable 0)
        x0 (get v0 variable 0)]
    (if (deriv-var? variable)
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
                         ;(assert (not (NaN? cur)))
                         ;(assert (not (NaN? limit)))
                         ;todo: replace max/min with acceleration to limit
                         (if (< acc 0)
                           (max cur limit)
                           (min cur limit))))
      ; var is regular and...
      (cond
        ;4. Flow is a constant
        (number? flow)
        (if (and (= delta Infinity)
                 (= 0 flow))
          x0
          (do
            ;(assert (not (NaN? flow)))
            (+ x0 (* flow delta))))
        ;flow is a velocity var and...
        (deriv-var? flow)
        (let [acc-flow (get flows flow 0)
              v0 (get v0 flow 0)]
          ;(println "2 af" x0 acc-flow v0 delta)
          ;(assert (not (NaN? v0)))
          ;(assert (not (NaN? delta)))
          (cond
            ;5. Acc is 0
            (= acc-flow 0)
            (+ x0 (if (= v0 0)
                    0
                    (* v0 delta)))
            ;6. Velocity var's flow is [acc limit] but v0 = limit (slow part = 0)
            (and (vector? acc-flow) (do
                                      ;(assert (not (NaN? (second acc-flow))))
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
                  ; _ (assert (not (NaN? acc)))
                  ; _ (assert (not (NaN? limit)))
                  #__ #_(soft-assert (or (> acc 0)
                                         (<= limit v0))
                                     "Negative acceleration but limit is higher than v0")
                  cur (if (= acc 0)
                        v0
                        (+ v0 (* acc delta)))
                  ;todo: decelerate to limit if cur exceeds limit
                  cur (if (< acc 0)
                        (max cur limit)
                        (min cur limit))
                  ;_ (assert (not= 0 acc))
                  ;_ (assert (not= 0 delta))
                  ;_ (assert (not (NaN? cur)))
                  slow-part (cond
                              (= Infinity delta) 0
                              (not= cur limit) 1
                              :else (abs (/ (- limit v0) (* acc delta))))
                  ;_ (assert (not (NaN? slow-part)))
                  avg (+ (* (/ (+ v0 cur) 2) slow-part)
                         (* limit (- 1 slow-part)))
                  ;_ (assert (not (NaN? avg)))
                  ]
              (+ x0 (if (= 0 avg)
                      0
                      (* avg delta))))))))))

(defn extrapolate-flow [v0 flows vars delta]
  ;(assert (not (NaN? delta)))
  ;(assert (number? delta))
  ;(assert (associative? flows))
  (if (or (= 0 delta)
          (= -0 delta))
    v0
    (let [var-count (count vars)]
      (loop [val v0
             vari 0]
        (if (>= vari var-count)
          val
          (let [variable (nth vars vari)
                ; _ (println "extrapolate" variable)
                ;_ (assert (not (NaN? x0)))
                x-now (extrapolate-flow-single-var variable v0 flows delta)]
            (when (NaN? x-now)
              (println variable "v0:" (get v0 variable) "vNow:" x-now)
              (assert (not (NaN? x-now))))
            (recur (assoc val variable x-now)
                   (inc vari))))))))

(defn extrapolate
  ([ha hav now] (extrapolate ha hav now nil))
  ([ha hav now vars]
    ;(assert (not (NaN? now)))
   (let [delta (- now (.-entry-time hav))]
     (if (or (= 0 delta)
             (= -0 delta))
       hav
       (let [s (current-state ha hav)
             ;_ (assert (some? s))
             flows (.-flows s)
             ;_ (assert (some? flows))
             vt (extrapolate-flow (.-v0 hav) flows (or vars (vec (keys (.-init-vars ha)))) delta)]
         (set! extrapolations (inc extrapolations))
         (assoc hav :v0 vt :entry-time now))))))

; todo: add a version that takes a seq of keys to extrapolate. select-keys on flow.
(defn extrapolate-all [ha-defs ha-vals now]
  (reduce
    (fn [ha-vals [ha-id ha-val]]
      (assoc ha-vals ha-id
                     (extrapolate (get ha-defs (.-ha-type ha-val))
                                  ha-val
                                  now)))
    ha-vals
    ha-vals))

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
      :lt (< diff c)
      (:colliding :not-colliding :touching :not-touching :in-state :not-in-state) false)))

;todo: could squeeze a little speed out here by simplifying, extracting constants, etc
; but it's only like 4% of the total, so not worth it right now?
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

(defn find-roots-with-shift [a b c shift]
  (cond
    ;quadratic: three intervals. at^2 + bt + c = 0
    (not= a 0) (let [det (- (* b b) (* 4 a c))]
                 (if (< det 0)
                   ; no change. constant within range
                   []
                   (let [root (sqrt det)
                         soln-plus (+ (/ (+ (- b) root) (* 2 a)) shift)
                         soln-minus (+ (/ (- (- b) root) (* 2 a)) shift)]
                     ;(assert (not (NaN? soln-plus)))
                     ;(assert (not (NaN? soln-minus)))
                     (if (< soln-plus soln-minus)
                       [soln-plus soln-minus]
                       [soln-minus soln-plus]))))
    ;linear
    (and (= a 0) (not= b 0)) (let [soln (/ (- c) b)]
                               ; (assert (not (NaN? soln)))
                               [(+ soln shift)])
    ;constant
    :else []))

(defn find-roots [a b c]
  (find-roots-with-shift a b c 0))

(defn get-def [ha-defs ha]
  (get ha-defs (.-ha-type ha)))

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
      :debug [:debug (easy-simplify (second g))]
      (:and :or) (let [g (walk/walk (fn [g-in]
                                      (easy-simplify g-in))
                                    (fn [g]
                                      (apply vector (first g) (mapcat (fn [g-in]
                                                                        (if (= (first g-in)
                                                                               (first g))
                                                                          (rest g-in)
                                                                          [g-in]))
                                                                      (rest g))))
                                    g)
                       g (filterv some? g)]
                   (if (= 2 (count g))
                     (second g)
                     g))
      g)))

(defn define-has [defs]
  (zipmap (map :ha-type defs)
          defs))

(defn guard-replace-self-vars [g id]
  (case (first g)
    nil nil
    (:and :or :debug) (apply vector
                             (first g)
                             (map #(guard-replace-self-vars % id) (rest g)))
    (:colliding :not-colliding
      :touching :not-touching
      :in-state :not-in-state) g
    (let [rel (first g)
          a (second g)
          a (cond
              (nil? a) a
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

(defn make-ha [htype collider-sets init-vars init-state & states]
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
    (HA. htype collider-sets init-vars init-state state-dict)))

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
             (:colliding :not-colliding :touching :not-touching) (= (count g) 4)
             (:in-state :not-in-state) (= (count g) 3)
             (:and :or :debug) (every? guard? (rest g))))))

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

(defn make-state [id collider-set on-enter flows & edges]
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
    (State. id collider-set flows edges on-enter)))

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

;todo: handle quantification, colliders
(defn term-dependencies [guard-term]
  (if (nil? guard-term)
    []
    (case (first guard-term)
      (:gt :geq :leq :lt) (if (or (= (count guard-term) 3)
                                  (nil? (third guard-term)))
                            [(first (second guard-term))]
                            [(first (second guard-term)) (first (third guard-term))])
      (:and :or :debug) (mapcat term-dependencies (rest guard-term))
      (:in-state :not-in-state) [(second guard-term)]
      ;todo: find every HA with a collider matching the RHS of any of the colliders of the owning HA on the LHS
      (:colliding :not-colliding :touching :not-touching) [])))

;todo: handle quantification, colliders
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

(defn negate-guard [g]
  (assert (guard? g))
  (easy-simplify
    (case (first g)
      nil nil
      :debug [:debug (negate-guard (second g))]
      :colliding (assoc g 0 :not-colliding)
      :not-colliding (assoc g 0 :colliding)
      :touching (assoc g 0 :not-touching)
      :not-touching (assoc g 0 :touching)
      :in-state (assoc g 0 :not-in-state)
      :not-in-state (assoc g 0 :in-state)
      :and (apply vector :or (map negate-guard (rest g)))
      :or (apply vector :and (map negate-guard (rest g)))
      :gt (apply vector :leq (rest g))
      :geq (apply vector :lt (rest g))
      :leq (apply vector :gt (rest g))
      :lt (apply vector :geq (rest g)))))

(defn enter-state [ha-def ha state update-dict now precision]
  (assert (>= now (:entry-time ha)) "Time must be monotonic")
  (let [
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

(defn map-defs [func ha-defs]
  (into {}
        (map (fn [[id def]]
               (let [r (func def)]
                 (assert (ha? def) "Result of mapping an HA def must be an HA def")
                 (assert (= (.-ha-type def) id) "Can't change ha type when mapping")
                 [id r]))
             ha-defs)))

(defn map-states [func ha-def]
  (into {}
        (map (fn [[sid state]]
               (let [r (func state)]
                 (assert (instance? State r) "Result of mapping a state must be a state")
                 (assert (= (:id r) sid) "Can't change state ID when mapping")
                 [sid r]))
             (:states ha-def))))

(defn map-transitions [func state]
  (assoc state
    :edges
    (priority-label-edges (mapcat (fn [e]
                                    (let [r (func e)
                                          rs (if (instance? Edge r)
                                               [r]
                                               r)]
                                      rs))
                                  (:edges state)))))