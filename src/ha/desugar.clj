(ns ha.desugar
  (:require
    [clojure.math.combinatorics :as comb]
    [clojure.walk :as walk]
    [ha.z3 :as z3]
    [ha.ha :as ha :refer [make-ha make-state make-edge kw]]))

; Desugars HAs with bounded acceleration, transition priorities, required transitions, and disjunctive guards into ones without all that stuff.

(defn map-vals [fun dict]
  (into {}
        (map (fn [[k v]]
               [k (fun v)])
             dict)))

(defn fix [fun val]
  (let [result (fun val)]
    (if (= result val)
      result
      (fix fun result))))

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
  (let [result (fix (fn [ha]
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
                  (apply comb/cartesian-product inner-splits)))
    ; leave relations alone, wrap them in a [] to survive mapcat
    [g]))

(defn split-edge [e z3]
  (if (nil? (:guard e))
    [e]
    (do
      (assert e)
      (assert (:guard e))
      (assert z3)
      (let [split-guards (split-guard-on-disjunctions (:guard e))
            simplified-guards (map #(ha/easy-simplify (z3/simplify-guard z3 %))
                                   split-guards)
            simplified-guards (distinct (filter (fn [g]
                                                  (and g (not= (first g) :contradiction)))
                                                simplified-guards))
            out-edges (map (fn [g] (assoc e :guard g))
                           simplified-guards)]
        out-edges))))

(defn guard-disjunctions-to-transitions- [ha z3]
  (reduce
    (fn [ha sid]
      (let [state (get ha sid)
            state (fix (fn [state]
                         (let [s (update state
                                         :edges (fn [es]
                                                  (mapcat #(split-edge % z3) es)))]
                           s))
                       state)
            state (assoc state :edges
                               (ha/priority-label-edges (:edges state)))]
        (assoc ha sid state)))
    ha
    (:states ha)))

(defn guard-disjunctions-to-transitions [has z3]
  (map-vals #(guard-disjunctions-to-transitions- % z3) has))

(defn simplify-guards [has z3]
  (map-vals (fn [ha]
              (reduce (fn [ha sid]
                        (update-in ha [sid :edges]
                                   (fn [edges]
                                     (ha/priority-label-edges
                                       (filter identity
                                               (map (fn [e]
                                                      (let [simplified (ha/easy-simplify (z3/simplify-guard z3 (:guard e)))]
                                                        (if (= (first simplified) :contradiction)
                                                          nil
                                                          (assoc e :guard
                                                                   simplified))))
                                                    edges))))))
                      ha
                      (:states ha)))
            has))

(defn desugar [has]
  (let [z3 (z3/->z3 has)]
    (-> has
        (bounded-acc-to-states)
        (simplify-guards z3)
        #_(priorities-to-disjoint-guards)
        #_(required-transitions-to-invariants)
        #_(invariant-disjunctions-to-states)
        #_(guard-disjunctions-to-transitions z3))))

#_(defn test-ha []
  (let [precision 0.001
        id :mario
        clear-timers {:jump-timer 0}
        walls #{[0 0 256 8] [64 64 16 16]}
        stand-others #{}
        wall-others #{}
        x 0
        y 0
        fall-speed 80
        jump-speed 144
        move-speed 32
        jump-time 0.5
        min-jump-time 0.1
        ground-move-acc (/ move-speed 0.5)
        brake-acc (/ move-speed 0.5)
        air-move-acc (/ ground-move-acc 2)
        fall-acc (/ fall-speed 0.2)
        jump-gravity (/ fall-acc 2)]
    (make-ha id
             {:x     x :y y
              :v/x   0 :v/y 0
              :w     16 :h 16
              :state (kw :idle :right)}
             ; ground movement and idling pairs
             (make-paired-states
               :left {:v/x -1}                              ; when used with accel states, applied to the acceleration and to the limit
               :right {}
               (fn [dir opp]
                 (vector
                   (make-state
                     (kw :idle dir)
                     (merge clear-timers {:v/y 0})
                     {:x   :v/x
                      :v/x [(- brake-acc) 0]}
                     ; might still have some velocity in idle state, must self-transition and nix velocity in that case
                     (bumping-transitions id dir (kw :idle dir)
                                          (if (= dir :left)
                                            [:gt :v/x 0]
                                            [:lt :v/x 0])
                                          walls wall-others
                                          precision)
                     (bumping-transitions id opp (kw :idle dir)
                                          (if (= dir :left)
                                            [:lt :v/x 0]
                                            [:gt :v/x 0])
                                          walls wall-others
                                          precision)
                     ;idle -> moving in dir
                     (make-edge
                       (kw :moving dir)
                       (non-bumping-guard opp walls wall-others precision)
                       #{[:on #{dir}]})
                     ;idle -> moving in opposite dir
                     (make-edge
                       (kw :moving opp)
                       (non-bumping-guard dir walls wall-others precision)
                       #{[:on #{opp}]})
                     ;idle -> jumping (ascend controlled)
                     (make-edge
                       (kw :jumping dir)
                       nil
                       #{[:on #{:jump}]}
                       {:v/y jump-speed :jump-timer 0})
                     ;idle -> falling
                     (make-edge
                       (kw :falling dir)
                       (unsupported-guard 16 16 walls stand-others)
                       #{:required}))
                   #_(make-state
                       (kw :moving dir)
                       {:v/y 0}
                       {:x   :v/x
                        :v/x [ground-move-acc move-speed]}
                       ;moving -> stopped
                       (bumping-transitions id dir (kw :idle dir)
                                            (if (= dir :left)
                                              [:gt :v/x 0]
                                              [:lt :v/x 0])
                                            walls wall-others
                                            precision)
                       (bumping-transitions id opp (kw :idle dir)
                                            (if (= dir :left)
                                              [:lt :v/x 0]
                                              [:gt :v/x 0])
                                            walls wall-others
                                            precision)
                       ;moving -> other dir
                       (make-edge
                         (kw :moving opp)
                         nil
                         #{[:off #{dir}] [:on #{opp}]})
                       ;moving -> braking
                       (make-edge
                         (kw :idle dir)
                         nil
                         #{[:off #{dir}]})
                       ;moving -> jumping
                       (make-edge
                         (kw :jumping :moving dir)
                         nil
                         #{[:on #{:jump}]}
                         {:v/y jump-speed :jump-timer 0})
                       ;moving -> falling
                       (make-edge
                         (kw :falling :moving dir)
                         (unsupported-guard 16 16 walls stand-others)
                         #{:required}))
                   ; jumping
                   #_(make-state
                       (kw :jumping :moving dir)
                       nil
                       {:x          :v/x
                        :v/x        [air-move-acc move-speed]
                        :y          :v/y
                        :v/y        [(- jump-gravity) 0]
                        :jump-timer 1}
                       ; hit side wall
                       (bumping-transitions id dir (kw :jumping dir)
                                            (if (= dir :left)
                                              [:gt :v/x 0]
                                              [:lt :v/x 0])
                                            walls wall-others
                                            precision)
                       (bumping-transitions id opp (kw :jumping dir)
                                            (if (= dir :left)
                                              [:lt :v/x 0]
                                              [:gt :v/x 0])
                                            walls wall-others
                                            precision)
                       ; -> falling because head bump
                       (bumping-transitions id :bottom (kw :falling :moving dir)
                                            nil
                                            walls wall-others
                                            precision)
                       ;  -> falling at apex
                       (make-edge
                         (kw :falling :moving dir)
                         [:geq :jump-timer jump-time]
                         #{:required})
                       ; -> falling because of button release
                       (make-edge
                         (kw :falling :moving dir)
                         [:geq :jump-timer min-jump-time]
                         #{[:off #{:jump}]})
                       ; -> accelerate other direction
                       (make-edge
                         (kw :jumping :moving opp)
                         (non-bumping-guard dir walls wall-others precision)
                         #{[:off #{dir}] [:on #{opp}]})
                       ; -> stop v/x accel
                       (make-edge
                         (kw :jumping dir)
                         nil
                         #{[:off #{dir opp}]}))
                   #_(make-state
                       (kw :jumping dir)
                       nil
                       {:x          :v/x
                        :v/x        0
                        :y          :v/y
                        :v/y        [(- jump-gravity) 0]
                        :jump-timer 1}
                       ; hit side wall
                       (bumping-transitions id dir (kw :jumping dir)
                                            (if (= dir :left)
                                              [:gt :v/x 0]
                                              [:lt :v/x 0])
                                            walls wall-others
                                            precision)
                       (bumping-transitions id opp (kw :jumping dir)
                                            (if (= dir :left)
                                              [:lt :v/x 0]
                                              [:gt :v/x 0])
                                            walls wall-others
                                            precision)
                       ; -> falling because head bump
                       #_(bumping-transitions id :bottom (kw :falling dir) nil walls wall-others)
                       ;  -> falling at apex
                       (make-edge
                         (kw :falling dir)
                         [:geq :jump-timer jump-time]
                         #{:required})
                       ; -> falling because of button release
                       (make-edge
                         (kw :falling dir)
                         [:geq :jump-timer min-jump-time]
                         #{[:off #{:jump}]})
                       ; -> accelerate direction
                       (make-edge
                         (kw :jumping :moving dir)
                         (non-bumping-guard opp walls wall-others precision)
                         #{[:off #{opp}] [:on #{dir}]})
                       ; -> accelerate other direction
                       (make-edge
                         (kw :jumping :moving opp)
                         (non-bumping-guard dir walls wall-others precision)
                         #{[:off #{dir}] [:on #{opp}]}))
                   #_(make-state
                       (kw :falling :moving dir)
                       nil
                       {:x   :v/x
                        :v/x [air-move-acc move-speed]
                        :y   :v/y
                        :v/y [(- fall-acc) (- fall-speed)]}
                       ; falling -> landed
                       (bumping-transitions id :top (kw :moving dir)
                                            nil
                                            walls wall-others
                                            precision)
                       ; falling while rising -> bumped head
                       (bumping-transitions id :bottom (kw :falling :moving dir)
                                            nil
                                            walls wall-others
                                            precision)
                       ; falling -> bumped wall
                       (bumping-transitions id :left (kw :falling dir)
                                            [:gt :v/x 0]
                                            walls wall-others
                                            precision)
                       (bumping-transitions id :right (kw :falling dir)
                                            [:lt :v/x 0]
                                            walls wall-others
                                            precision)
                       ; falling -> move other dir
                       (make-edge
                         (kw :falling :moving opp)
                         (non-bumping-guard dir walls wall-others precision)
                         #{[:off #{dir}] [:on #{opp}]})
                       ; falling -> stop moving
                       (make-edge
                         (kw :falling dir)
                         nil
                         #{[:off #{dir opp}]}))
                   #_(make-state
                       (kw :falling dir)
                       nil
                       {:x   :v/x
                        :v/x 0
                        :y   :v/y
                        :v/y [(- fall-acc) (- fall-speed)]}
                       ; falling -> landed
                       (bumping-transitions id :top (kw :idle dir)
                                            nil
                                            walls wall-others
                                            precision)
                       ; falling while rising -> bumped head
                       (bumping-transitions id :bottom (kw :falling dir)
                                            nil
                                            walls wall-others
                                            precision)
                       ; falling -> bumped wall (may have residual velocity, so self-transition
                       (bumping-transitions id :left (kw :falling dir)
                                            [:gt :v/x 0]
                                            walls wall-others
                                            precision)
                       (bumping-transitions id :right (kw :falling dir)
                                            [:lt :v/x 0]
                                            walls wall-others
                                            precision)
                       ; falling -> move dir/opp
                       (make-edge
                         (kw :falling :moving dir)
                         (non-bumping-guard opp walls wall-others precision)
                         #{[:off #{opp}] [:on #{dir}]})
                       (make-edge
                         (kw :falling :moving opp)
                         (non-bumping-guard dir walls wall-others precision)
                         #{[:off #{dir}] [:on #{opp}]}))))))))