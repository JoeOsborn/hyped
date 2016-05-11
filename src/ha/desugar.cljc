(ns ha.desugar
  (:require
    [clojure.set :as sets]
    #?(:clj [ha.z3 :as z3])
    [ha.ha :as ha :refer [make-ha make-state make-edge kw]]))

; Desugars HAs with bounded acceleration, transition priorities, required transitions, and disjunctive guards into ones without all that stuff.

(defn map-vals [fun dict]
  (into {}
        (map (fn [[k v]]
               [k (fun v)])
             dict)))

(defn fixpoint [fun val]
  (let [result (fun val)]
    (if (= result val)
      result
      (recur fun result))))

;cartesian-product from Mark Engelberg's clojure/math.combinatorics
(defn cartesian-product
  "All the ways to take one item from each sequence"
  [& seqs]
  (let [v-original-seqs (vec seqs)
        step
        (fn step [v-seqs]
          (let [increment
                (fn [v-seqs]
                  (loop [i (dec (count v-seqs)), v-seqs v-seqs]
                    (if (= i -1)
                      nil
                      (if-let [rst (next (v-seqs i))]
                        (assoc v-seqs i rst)
                        (recur (dec i)
                               (assoc v-seqs i (v-original-seqs i)))))))]
            (when v-seqs
              (cons (map first v-seqs)
                    (lazy-seq (step (increment v-seqs)))))))]
    (when (every? seq seqs)
      (lazy-seq (step v-original-seqs)))))

(defn get-state-flows [ha pred]
  (for [sid (:states ha)
        :let [state (get ha sid)
              flows (get state :flows)]
        [vbl val] flows
        :when (pred state vbl val)]
    [state vbl val]))

(defn prepend-edge [e es]
  (ha/priority-label-edges (concat [e] es)))

(defn bounded-acc-to-states- [ha0]
  ; find some state,flow pair s.t. flow is in state and flow is a bounded acceleration
  (let [result (fixpoint (fn [ha]
                      (if-let [[state vbl flow] (first (get-state-flows ha (fn [_state vbl flow]
                                                                             (and (ha/deriv-var? vbl)
                                                                                  (vector? flow)))))]
                        ; replace it with two states, one with an unbounded acceleration at the same speed
                        ; and the other with zero acceleration
                        (let [sid (:id state)

                              acc-state-id (keyword (str (name sid) "-" (name vbl) "-acc"))
                              limit-state-id (keyword (str (name sid) "-" (name vbl) "-limit"))

                              acc (first flow)
                              limit (second flow)

                              outside-limit-guard [(if (< acc 0) :leq :geq) [(:id ha) vbl] limit]

                              acc-limit-edge (ha/make-edge limit-state-id
                                                           outside-limit-guard
                                                           #{:required}
                                                           {vbl (second flow)})

                              acc-state (assoc state :id acc-state-id
                                                     :flows (assoc (:flows state) vbl acc)
                                                     :edges (prepend-edge acc-limit-edge (:edges state)))

                              limit-state (assoc state :id limit-state-id
                                                       :flows (assoc (:flows state) vbl 0))
                              ; update the states of the HA...
                              result (reduce (fn [ha s2id]
                                               ; replace the old state with the two new states
                                               (if (= s2id sid)
                                                 (assoc
                                                   (dissoc ha s2id)
                                                   acc-state-id acc-state
                                                   limit-state-id limit-state
                                                   :states (conj (filterv #(not= % s2id)
                                                                          (:states ha))
                                                                 acc-state-id
                                                                 limit-state-id))
                                                 ; update other states to retarget to the right new state
                                                 (let [s2 (get ha s2id)
                                                       es (:edges s2)
                                                       ; replace each such edge with two edges,
                                                       ; one into each successor state
                                                       es (mapcat (fn [e]
                                                                    (if (= (:target e) sid)
                                                                      ; with the edge into the limit state guarded on
                                                                      ; the current velocity and updating velocity to the limit
                                                                      (let [elimit (assoc e :target limit-state-id
                                                                                            :guard [:and
                                                                                                    (:guard e)
                                                                                                    outside-limit-guard]
                                                                                            :update (assoc (:update e)
                                                                                                      vbl
                                                                                                      (second flow)))
                                                                            eacc (assoc e :target acc-state-id)]
                                                                        [elimit eacc])
                                                                      [e]))
                                                                  es)
                                                       es (ha/priority-label-edges es)]
                                                   (assoc ha s2id (assoc s2 :edges es)))))
                                             ha
                                             (:states ha))]
                          (println "Turned" (count (:states ha)) "states into" (count (:states result)) "states by fixing" sid vbl "to" acc-state-id limit-state-id)
                          result)
                        ; or else return the ha as-is
                        ha))
                         ha0)]
    (assert (empty? (get-state-flows result (fn [_state vbl flow]
                                              (and (ha/deriv-var? vbl)
                                                   (vector? flow))))))
    (println "Turned" ha0 (count (:states ha0)) "states into" (count (:states result)) "states")
    result))

(defn bounded-acc-to-states [has]
  (map-vals bounded-acc-to-states-
            has))

(defn disjunction-free? [g]
  (or
    (not (vector? g))
    (and (not= (first g) :or)
         (every? disjunction-free? (rest g)))))

(defn split-guard-on-disjunctions [g]
  (case (first g)
    ; each disjunct is recursively split, and the results are all concatenated into one set of splits
    ;  if a disjunct is not split in this way, it will still be packaged in a [] per above
    (:or) (mapcat split-guard-on-disjunctions (rest g))
    ; each conjunct is recursively split, yielding alternatives for each guard
    ;  build a new conjunction with each element of the cartesian product of seq-of-alternatives
    (:and) (let [inner-splits (map split-guard-on-disjunctions (rest g))]
             (map (fn [comb] (apply vector :and comb))
                  (apply cartesian-product inner-splits)))
    ; leave relations alone, wrap them in a [] to survive mapcat
    [g]))

(defn split-edge [e]
  (if (nil? (:guard e))
    [e]
    (do
      (assert e)
      (assert (:guard e))
      (let [split-guards (split-guard-on-disjunctions (:guard e))
            simplified-guards (map ha/easy-simplify split-guards)
            simplified-guards (distinct (filter (fn [g]
                                                  (and g (not= (first g) :contradiction)))
                                                simplified-guards))
            out-edges (map (fn [g] (assoc e :guard g))
                           simplified-guards)]
        out-edges))))

(defn guard-disjunctions-to-transitions- [ha]
  (reduce
    (fn [ha sid]
      (let [state (get ha sid)
            state (fixpoint (fn [state]
                         (let [s (update state
                                         :edges (fn [es]
                                                  (mapcat split-edge es)))]
                           s))
                            state)
            state (assoc state :edges
                               (ha/priority-label-edges (:edges state)))]
        (assoc ha sid state)))
    ha
    (:states ha)))

(defn guard-disjunctions-to-transitions [has]
  (map-vals guard-disjunctions-to-transitions- has))

#?(:clj
   (defn simplify-guards [has z3]
     (map-vals (fn [ha]
                 (reduce (fn [ha sid]
                           (update-in ha [sid :edges]
                                      (fn [edges]
                                        (ha/priority-label-edges
                                          (filter identity
                                                  (map (fn [e]
                                                         (let [simplified (z3/simplify-guard z3 (:guard e))]
                                                           (if (= (first simplified) :contradiction)
                                                             nil
                                                             (assoc e :guard
                                                                      simplified))))
                                                       edges))))))
                         ha
                         (:states ha)))
               has)))


(defn all-collider-defs [ha-def]
  (mapcat (fn [[set-id set-defs]]
            (map (fn [[cid cdef]]
                   (assoc cdef
                     :owner (.-ha-type ha-def)
                     :collider-id cid
                     :collider-set set-id
                     :valid-states (set (keep (fn [[state-id sdef]]
                                                (when (= (.-collider-set sdef)
                                                         set-id)
                                                  state-id))
                                              (.-states ha-def)))))
                 set-defs))
          (:collider-sets ha-def)))


(defn split-collision-guard [g defs wall-colliders colliders]
  ; :colliding/touching my-col-type my-side your-col-type
  ; :not-colliding/not-touching my-col-type my-side your-col-type
  ; for now, split into a disjunction over my-col, over my-side (if :any),
  ; over each member of each type in all collider sets of defs

  ; if g is an inequality, yield [g]
  ; if g is an and/or, yield (map #(apply vector :and %)
  ;                               (map #(split-guard % defs colliders)
  ;                                    (rest g)))
  ; if g is a collision guard:
  (case (first g)
    ; each disjunct is recursively split, and the results are all concatenated
    ; into one set of splits
    ;  if a disjunct is not split in this way, it will still be packaged in a [] per above
    (:colliding :not-colliding
      :touching :not-touching)
    (let [[gtype my-col-type my-side your-col-type] g
          negated? (case gtype
                     (:colliding :touching) false
                     (:not-colliding :not-touching) true)
          lefty-righty? (case my-side
                          (:left :right :any) true
                          false)
          bottomy-toppy? (case my-side
                           (:bottom :top :any) true
                           false)
          all-other-colliders (sets/union
                                (set (mapcat all-collider-defs (vals defs)))
                                (set (vals wall-colliders)))
          my-colliders (if (= my-col-type :any)
                         (vals colliders)
                         (vals (filter #(contains? (:type %) my-col-type)
                                       colliders)))
          colliding? (case gtype
                       (:colliding :not-colliding) true
                       (:touching :not-touching) false)
          appropriate? (fn [my-coll your-type]
                         (some (sets/union
                                 (:collides my-coll)
                                 (if colliding?
                                   #{}
                                   (:touches my-coll)))
                               your-type))
          other-colliders-per-mine
          (into
            {}
            (if (= your-col-type :any)
              ; for each of my colliders, all of the other colliders
              (map (fn [my-coll]
                     [my-coll (filter #(appropriate? my-coll (:type %))
                                      all-other-colliders)])
                   my-colliders)
              (map (fn [my-coll]
                     [my-coll (filter #(and (appropriate? my-coll (:type %))
                                            (contains? (:type %) your-col-type))
                                      all-other-colliders)])
                   my-colliders)))
          collision-guards
          (vec (for [my-col (keys other-colliders-per-mine)
                     your-col (get other-colliders-per-mine my-col)]
                 (let [other (:owner your-col)
                       not-wall? (and (not= other :wall)
                                      (some? other))
                       ;narrow these tolerances based on side.
                       ;if it's "my left side", pull in my right. etc.
                       pull-in 0.8
                       width-off (* (:w my-col) pull-in)
                       height-off (* (:h my-col) pull-in)
                       your-width-off (* (:w your-col) pull-in)
                       your-height-off (* (:h your-col) pull-in)
                       [left-offset right-offset bottom-offset top-offset]
                       (case my-side
                         :any [0 0 0 0]
                         :left [0 width-off 0 0]
                         :right [width-off 0 0 0]
                         :bottom [0 0 0 height-off]
                         :top [0 0 height-off 0])
                       [your-left-offset your-right-offset your-bottom-offset your-top-offset]
                       (case my-side
                         :any [0 0 0 0]
                         :left [your-width-off 0 0 0]
                         :right [0 your-width-off 0 0]
                         :bottom [0 0 your-height-off 0]
                         :top [0 0 0 your-height-off])
                       l1 [[:$self :x] (:x my-col) left-offset]
                       r1 [[:$self :x] (:x my-col) (:w my-col) (- right-offset)]
                       b1 [[:$self :y] (:y my-col) bottom-offset]
                       t1 [[:$self :y] (:y my-col) (:h my-col) (- top-offset)]
                       l2 [(when not-wall?
                             [other :x])
                           (:x your-col)
                           your-left-offset]
                       r2 [(when not-wall?
                             [other :x])
                           (:x your-col)
                           (:w your-col)
                           (- your-right-offset)]
                       b2 [(when not-wall?
                             [other :y])
                           (:y your-col)
                           your-bottom-offset]
                       t2 [(when not-wall?
                             [other :y])
                           (:y your-col)
                           (:h your-col)
                           (- your-top-offset)]
                       overlapping [:and
                                    ; mright >= oleft
                                    ; (sx+mx+mw) - (ox+yx) >= 0 -> sx-ox >= yx-mx-mw
                                    [(if lefty-righty? :geq :gt)
                                     (first r1) (first l2)
                                     (- (apply + (rest l2)) (apply + (rest r1)))]
                                    ; oright >= mleft
                                    [(if lefty-righty? :geq :gt)
                                     (first r2) (first l1)
                                     (- (apply + (rest l1)) (apply + (rest r2)))]
                                    ; mtop >= obot
                                    [(if bottomy-toppy? :geq :gt)
                                     (first t1) (first b2)
                                     (- (apply + (rest b2)) (apply + (rest t1)))]
                                    ; otop >= mbot
                                    [(if bottomy-toppy? :geq :gt)
                                     (first t2) (first b1)
                                     (- (apply + (rest b1)) (apply + (rest t2)))]]]
                   (ha/easy-simplify [:and
                                      (when not-wall?
                                        [:in-state other (:valid-states your-col)])
                                      (case my-side
                                        :any overlapping
                                        :left [:and
                                               (when colliding?
                                                 [:lt
                                                  ;vx - ovx < 0 -> vx < ovx
                                                  [:$self :v/x]
                                                  (when not-wall?
                                                    [other :v/x])
                                                  0])
                                               overlapping]
                                        :right [:and
                                                (when colliding?
                                                  [:gt
                                                   ;vx - ovx > 0 -> vx > ovx
                                                   [:$self :v/x]
                                                   (when not-wall?
                                                     [other :v/x])
                                                   0])
                                                overlapping]
                                        :bottom [:and
                                                 (when colliding?
                                                   [:lt
                                                    ;vy - ovy < 0
                                                    [:$self :v/y]
                                                    (when not-wall?
                                                      [other :v/y])
                                                    0])
                                                 overlapping]
                                        :top [:and
                                              (when colliding?
                                                [:gt
                                                 [:$self :v/y]
                                                 (when not-wall?
                                                   [other :v/y])
                                                 0])
                                              overlapping])]))))]
      (if-not negated?
        ; one guard per different collider
        collision-guards
        ; one guard containing the negation of OR any-collision
        [(ha/negate-guard (apply vector :or collision-guards))]))
    ; each conjunct is recursively split, yielding alternatives for each guard
    ;  build a new conjunction with each element of the cartesian product of seq-of-alternatives
    (:and :or :debug) (let [inner-splits
                            (map (fn [gi]
                                   (split-collision-guard gi
                                                          defs
                                                          wall-colliders
                                                          colliders))
                                 (rest g))]
                        (map (fn [comb] (apply vector (first g) comb))
                             (apply cartesian-product inner-splits)))
    ; leave relations alone, wrap them in a [] to survive mapcat
    [g]))

(defn maybe-split-collision-transition [id {g :guard :as tr} defs wall-colliders colliders]
  (let [guards (map (fn [gi] (ha/guard-replace-self-vars gi id))
                    (split-collision-guard g defs wall-colliders colliders))]
    (map #(assoc tr :guard %) guards)))

; fixme: assumes one ha instance per ha def with same id and ha type
(defn expand-collision-guards [ha-defs wall-colliders]
  (ha/map-defs (fn [def]
                 (let [collider-sets (:collider-sets def)]
                   (assoc def
                     :states
                     (ha/map-states
                       (fn [state]
                         (let [colliders (get collider-sets (:collider-set state))]
                           (ha/map-transitions
                             (fn [t]
                               ; yields transition or (seq transition)
                               (maybe-split-collision-transition
                                 (.-ha-type def)
                                 t
                                 (dissoc ha-defs (.-ha-type def))
                                 wall-colliders
                                 colliders))
                             state)))
                       def))))
               ha-defs))

(defn desugar [ha-defs wall-colliders]
  (-> ha-defs
      (expand-collision-guards wall-colliders)
      (bounded-acc-to-states)
      #_(simplify-guards z3)
      #_(priorities-to-disjoint-guards)
      #_(required-transitions-to-invariants)
      #_(invariant-disjunctions-to-states)
      #_(guard-disjunctions-to-transitions z3)))