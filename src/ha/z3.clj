(ns ha.z3
  (:require [clojure.string :as string]
            [ha.ha :as ha]
            [ha.eval :as heval])
  (:import [com.microsoft.z3 Context Expr Goal RatNum
                             BoolExpr RealExpr
                             EnumSort Status
                             Solver ArithExpr Z3Exception Tactic]
           (java.util Map HashMap)))

(defn trim-leading-colon [s]
  (if (= (nth s 0) \:)
    (subs s 1)
    s))

(defn split-var-name [symb-str]
  (let [components (string/split symb-str #"!")
        index (Integer/parseInt (last components))]
    [(butlast components)
     index]))

(defn var-name [& chunks]
  (assert (every? some? chunks) (str chunks))
  (string/join "!"
               (map #(if (instance? Expr %)
                      (.toString %)
                      (trim-leading-colon (str %)))
                    chunks)))

(defn var->const [{ctx :context} [id var] idx]
  (assert id)
  (assert var)
  (let [nom (if (namespace var)
              (var-name id (namespace var) (name var) idx)
              (var-name id var idx))]
    (.mkRealConst ctx nom)))

(defn float->real [{ctx :context} val]
  (when (and (or (instance? Float val)
                 (instance? Double val))
             (or (.isNaN val)
                 (.isInfinite val)))
    (throw (IllegalArgumentException. "Only finite vals are OK")))
  (let [val-denom 10000000
        val-int (Math/round ^double (* val val-denom))]
    (.mkReal ctx val-int val-denom)))

(defn rat->float [c]
  (cond
    ; rational
    (.isRatNum c) (/ (.getInt64 (.getNumerator c))
                     (.getInt64 (.getDenominator c)))
    ; integer
    (.isIntNum c) (.getInt64 c)
    ; sure, why not?
    (= (.toString c) "epsilon") (/ 1 100000000)
    ; something else
    :else (do (println "something else" (.toString c))
              (throw (IllegalArgumentException. (str "Can't make sense of " (.toString c)))))))

(def ^:dynamic *use-datatypes* false)

(defn update-ha-defs [{context :context :as z3} ha-defs]
  (let [state-sorts (into {}
                          (for [[ha-type {states :states}] ha-defs
                                :let [sort-name (var-name ha-type "state")
                                      state-ids (map (fn [[sid _s]]
                                                       (name sid))
                                                     states)
                                      sort (.mkEnumSort context
                                                        ^String sort-name
                                                        ^"[Ljava.lang.String;" (into-array state-ids))]]
                            [sort-name
                             {:sort   (if *use-datatypes*
                                        sort
                                        (.mkRealSort context))
                              :consts (zipmap state-ids
                                              (if *use-datatypes*
                                                (.getConsts sort)
                                                (map #(.mkReal context %) (range 0 (count state-ids)))))}]))]
    (assoc z3 :state-sorts state-sorts
              :ha-defs ha-defs)))

(defn ->z3 [ha-defs settings]
  (update-ha-defs {:context (Context. (reduce
                                        (fn [m [k v]]
                                          (.put m k v)
                                          m)
                                        (HashMap.)
                                        settings))}
                  ha-defs))

(defn map->params [ctx m]
  (reduce
    (fn [params [k v]]
      (.add params (name k) v)
      params)
    (.mkParams ctx)
    m))

(defn with-solver [{ctx :context :as z3} func]
  (let [stacs (.andThen ctx
                        (.usingParams ctx
                                      (.mkTactic ctx "simplify")
                                      (map->params ctx {:som             true :arith-lhs true
                                                        :hoist-cmul      true :hoist-mul true
                                                        :ite-extra-rules true :local-ctx true
                                                        :pull-cheap-ite  true :push-ite-arith true}))
                        (.mkTactic ctx "purify-arith")
                        (into-array Tactic [(.mkTactic ctx "propagate-values")
                                            (.mkTactic ctx "solve-eqs")
                                            (.usingParams ctx
                                                          (.mkTactic ctx "simplify")
                                                          (map->params ctx {:som             true :arith-lhs true
                                                                            :hoist-cmul      true :hoist-mul true
                                                                            :ite-extra-rules true :local-ctx true
                                                                            :pull-cheap-ite  true :push-ite-arith true}))
                                            (.mkTactic ctx "tseitin-cnf")
                                            (.usingParams ctx
                                                          (.mkTactic ctx "qe")
                                                          (map->params ctx {:qe-nonlinear true}))
                                            (.mkTactic ctx "tseitin-cnf")
                                            (.mkTactic ctx "nlqsat")]))
        s (.mkSolver ctx stacs)
        oparams (.mkParams ctx)
        o nil #_(.mkOptimize ctx)
        z3 (assoc z3 :optimizer o :solver s)
        ret (func z3)]
    (when s
      (.setParameters s (map->params ctx
                                     {"smt.arith.nl"        true
                                      "smt.arith.nl.rounds" 4096
                                      "smt.mbqi"            true})))
    (when o
      (.setParameters o oparams))
    (when (seq? ret)
      (doall ret))
    ret))

(defn pop! [{o :optimizer s :solver :as z3}]
  (when o (.Pop o))
  (when s (.pop s))
  z3)

(defn push! [{o :optimizer s :solver :as z3}]
  (when o (.Push o))
  (when s (.push s))
  z3)

(defn check! [{o :optimizer s :solver}]
  (let [status (.check s)]
    (println status)
    (cond
      (= status Status/UNSATISFIABLE) :unsat
      (= status Status/SATISFIABLE) :sat
      (= status Status/UNKNOWN) (do
                                  (Thread/sleep 100)
                                  (println "-----CHECK-----\n" s "\n-----\n" "NAs:" (.getNumAssertions s) "\n" "Stats:" (.getStatistics s))
                                  (println "reason:" (.toString (.getReasonUnknown s)))
                                  (Thread/sleep 500)
                                  (assert false)
                                  :unknown)
      :else (throw (IllegalStateException. (str "Unrecognizable status from solver" status))))))

(defn ^Expr translate-constraint [{ctx :context :as z3} c]
  (try
    (let [c (if (seq? c)
              (vec c)
              c)]
      (if (vector? c)
        (case (first c)
          :ite
          (.mkITE ctx
                  (translate-constraint z3 (nth c 1))
                  (translate-constraint z3 (nth c 2))
                  (translate-constraint z3 (nth c 3)))
          :and
          (let [r (map #(translate-constraint z3 %)
                       (rest c))]
            (.mkAnd ctx (into-array BoolExpr r)))
          :or
          (.mkOr ctx (into-array
                       BoolExpr
                       (map #(translate-constraint z3 %)
                            (rest c))))
          :xor
          (do
            (assert (= (count c) 3))
            (.mkXor ctx
                    (translate-constraint z3 (nth c 1))
                    (translate-constraint z3 (nth c 2))))
          :not
          (.mkNot ctx (translate-constraint z3 (second c)))
          :implies
          (.mkImplies ctx
                      (translate-constraint z3 (nth c 1))
                      (translate-constraint z3 (nth c 2)))
          :iff
          (.mkIff ctx
                  (translate-constraint z3 (nth c 1))
                  (translate-constraint z3 (nth c 2)))
          (:geq :leq :lt :gt :eq)
          (let [[n1 n2] (map #(translate-constraint z3 %)
                             (rest c))]
            (assert (every? some? (rest c)) (str "Nil entries in " c))
            (case (first c)
              :gt (.mkGt ctx n1 n2)
              :geq (.mkGe ctx n1 n2)
              :eq (.mkEq ctx n1 n2)
              :leq (.mkLe ctx n1 n2)
              :lt (.mkLt ctx n1 n2)))
          :forall
          (let [[consts guard body] (rest c)]
            (.mkForall ctx
                       (into-array (map #(translate-constraint z3 %) consts))
                       (.mkImplies ctx
                                   (translate-constraint z3 guard)
                                   (translate-constraint z3 body))
                       0
                       nil
                       nil
                       nil
                       nil))
          :exists
          (let [[consts guard body] (rest c)]
            (.mkExists ctx
                       (into-array (map #(translate-constraint z3 %) consts))
                       (.mkImplies ctx
                                   (translate-constraint z3 guard)
                                   (translate-constraint z3 body))
                       0
                       nil
                       nil
                       nil
                       nil))
          (:+ :- :* :/ :**)
          (let [[rel & args] c
                z3-args (into-array ArithExpr (map #(translate-constraint z3 %) args))]
            (case rel
              :+ (.mkAdd ctx z3-args)
              :- (.mkSub ctx z3-args)
              :* (.mkMul ctx z3-args)
              :/ (do
                   (assert (= (count z3-args) 2)
                           (str "Can't have more than 2 arguments to divide" (map #(.toString %) z3-args)))
                   (.mkDiv ctx (first z3-args) (second z3-args)))
              :** (do
                    (assert (= (count z3-args) 2)
                            (str "Can't have more than 2 arguments to pow" (map #(.toString %) z3-args)))
                    (.mkPower ctx (first z3-args) (second z3-args)))))
          (throw (IllegalArgumentException. (str "Can't convert " c))))
        (cond
          (instance? Expr c) c
          (number? c) (float->real z3 c)
          (or (= :false c)
              (= false c)) (.mkFalse ctx)
          (or (= :true c)
              (= true c)) (.mkTrue ctx)
          (or (keyword? c)
              (string? c)) (do (assert (not= (name c) "flapping"))
                               (.mkRealConst ctx (name c)))
          ; is this always the case?
          (nil? c) (.mkTrue ctx)
          :else (do
                  (println "tried to convert" c (type c))
                  (throw (IllegalArgumentException. (str "Can't convert " c)))))))
    (catch Exception e
      (println (.toString e) "broke on" c)
      (throw e)
      (.mkFalse ctx))))

(defn assert-all! [{context :context
                    opt     :optimizer
                    solv    :solver :as z3} constraints]
  (let [translated (map (fn [c] (translate-constraint z3 c))
                        constraints)]
    (when (or (not (coll? constraints))
              (coll? (ffirst constraints)))
      (throw (IllegalArgumentException. "assert-all! takes a collection of constraints")))
    #_(println "assert all" (map #(.toString %) translated))
    (when opt
      (.Add opt
            ^"[Lcom.microsoft.z3.BoolExpr;"
            (into-array BoolExpr translated)))
    (when solv
      (.add solv
            ^"[Lcom.microsoft.z3.BoolExpr;"
            (into-array BoolExpr translated))
      #_(println "still sat?")
      #_(println (.check solv))))
  z3)

(defn state-var [{state-sorts :state-sorts
                  ctx         :context :as z3}
                 ha-type ha-id nom t-var]
  (let [sort (get-in state-sorts [(var-name ha-type "state") :sort])]
    (.mkConst ctx
              (var-name ha-id nom t-var)
              sort)))

(defn state-val [{state-sorts :state-sorts} ha-type state]
  (get-in state-sorts [(var-name ha-type "state") :consts (name state)]))

(defn assert-valuation! [z3
                         ha-vals
                         t-var]
  (let [constraints (conj
                      (apply
                        concat
                        (for [{this-state :state
                               this-type  :ha-type
                               this-v0    :v0
                               this-id    :id
                               :as        this-ha}
                              (vals ha-vals)]
                          (conj
                            (for [[v k] this-v0]
                              [:eq
                               (var-name this-id v "enter" t-var)
                               k])
                            [:eq
                             (state-var z3 this-type this-id "state" t-var)
                             (state-val z3 this-type this-state)])))
                      [:eq t-var (apply max (map :entry-time (vals ha-vals)))])]
    (assert-all! z3 constraints)
    (assoc z3 :last-t t-var
              :has (into {}
                         (map (fn [ha]
                                [(:id ha) (:ha-type ha)])
                              (vals ha-vals))))))

(defn flow-constraints [{ctx :context :as z3}
                        ha-id
                        flows
                        v0-vars
                        vT-vars
                        last-t
                        new-t]
  (let [dt (var-name ha-id "dt" new-t last-t)
        flow-constraints (for [[v f0] v0-vars
                               :let [f1 (get vT-vars v)
                                     flow (get flows v 0)
                                     _ (when-not f1 (println "uh oh" v vT-vars))
                                     _ (assert v)
                                     _ (assert f0)
                                     _ (assert f1)
                                     _ (assert flow)]]
                           (cond
                             (= flow 0) [:eq f1 f0]
                             (number? flow) [:eq f1 [:+ f0 [:* flow dt]]]
                             (keyword? flow)
                             (let [flow0 (get v0-vars flow)
                                   dflow (get flows flow)]
                               (cond
                                 (= dflow 0) [:eq f1 [:+ f0 [:* flow0 dt]]]
                                 (vector? dflow)
                                 (let [[acc limit] dflow
                                       flow-rel (if (> acc 0)
                                                  :leq
                                                  :geq)
                                       dv-amt (if (> acc 0)
                                                [:- limit flow0]
                                                [:- flow0 limit])
                                       avg-acc-speed [:/ [:+ flow0 limit] 2]
                                       acc-duration [:/ dv-amt acc]
                                       acc-time [:+ last-t acc-duration]
                                       limit-duration [:- new-t acc-time]
                                       acc-part [:* avg-acc-speed acc-duration]
                                       limit-part [:* limit limit-duration]]
                                   [:ite [flow-rel [:+ flow0 [:* acc dt]] limit]
                                    ; linearize to approximate [:+ [:* acc dt dt] [:* flow0 dt] :f0]
                                    [:eq f1 [:+ f0 [:* flow0 dt] [:* acc dt dt]]]
                                    [:eq f1 [:+ f0 acc-part limit-part]]
                                    ])))
                             (vector? flow)
                             (let [[acc limit] flow
                                   acc-rel (if (> acc 0)
                                             :leq
                                             :geq)
                                   f0-not-at-limit [acc-rel [:+ f0 [:* acc dt]] limit]]
                               [:and
                                [:implies f0-not-at-limit [:eq f1 [:+ f0 [:* acc dt]]]]
                                [:implies [:not f0-not-at-limit] [:eq f1 limit]]])))]
    (assert (not= new-t last-t))
    (into
      [:and
       [:eq dt [:- new-t last-t]]
       [:geq dt heval/time-unit]]
      flow-constraints)))

(declare guard->z3)

(defn jump-constraints [{ctx :context :as z3} ha-type ha-id flows edges v0-vars vT-vars next-vars last-t new-t]
  ;todo: later, once collision guards stick around, need to know about colliders
  (let [mid-t "mid-t"
        vmid-vars (into {}
                        (map (fn [[v _]]
                               [v (var-name ha-id v mid-t)])
                             v0-vars))
        self-jump (into [:and
                         ; pick out-edge
                         [:eq (var-name ha-id "out-edge" last-t) -1]
                         ; set new state
                         [:eq
                          (state-var z3 ha-type ha-id "state" new-t)
                          (state-var z3 ha-type ha-id "state" last-t)]]
                        (for [[v vT] vT-vars
                              :let [next-v (get next-vars v)]]
                          [:eq next-v vT]))]
    [:and
     (reduce
       ; the ITE captures priority semantics.
       ; if an edge's guard holds at exit it must be >= (no stronger than) the picked edge.
       ; but this is true already by the ITE construction
       (fn [else {g :guard
                  i :index
                  u :update-dict
                  t :target :as e}]
         ;if guard is satisfied at t:
         [:ite (guard->z3 z3 ha-id g (var-name "exit" last-t))
          (into [:and
                 ; pick out-edge
                 [:eq (var-name ha-id "out-edge" last-t) i]
                 ; set new state
                 [:eq
                  (state-var z3 ha-type ha-id "state" new-t)
                  (state-val z3 ha-type t)]]
                ; set all next-vars to corresponding vT-vars unless update has something
                (for [[v vT] vT-vars
                      :let [uv (get u v nil)
                            next-v (get next-vars v)]]
                  (if (nil? uv)
                    [:eq next-v vT]
                    [:eq next-v uv])))
          ; otherwise
          else])
       self-jump
       ;reverse to put the highest priority edge on the outermost ITE
       (reverse edges))
     ; also, no required guard can be satisfied before t. quantifiers are rough so let's try to avoid it.
     #_[:not [:exists (concat [mid-t (var-name ha-id "dt" mid-t last-t)] (vals vmid-vars))
            true
            [:and
             [:gt mid-t last-t]
             [:lt mid-t new-t]
             (flow-constraints z3 ha-id flows v0-vars vmid-vars last-t mid-t)
             (into [:or]
                   (map (fn [e]
                          (guard->z3 z3
                                     ha-id
                                     (:guard e)
                                     mid-t))
                        (filter ha/required-transition? edges)))]]]]))

(defn symx-1! [{has     :has
                ha-defs :ha-defs
                last-t  :last-t :as z3}
               new-t]
  (assert ha-defs)
  ; flow from last-t to new-t
  (let [constraints (for [[ha-id ha-type] has
                          :let [ha-def (get ha-defs ha-type)
                                _ (assert ha-def)
                                state-var (state-var z3 ha-type ha-id "state" last-t)
                                vars (map first (dissoc (:init-vars ha-def) :w :h))
                                _ (assert (not (empty? vars)))
                                v0-vars (into {}
                                              (map (fn [v]
                                                     [v (var-name ha-id v "enter" last-t)])
                                                   vars))
                                _ (assert (not (empty? v0-vars)))
                                vT-vars (into {}
                                              (map (fn [v] [v (var-name ha-id v "exit" last-t)])
                                                   vars))
                                _ (assert (not (empty? vT-vars)))
                                next-vars (into {}
                                                (map (fn [v] [v (var-name ha-id v "enter" new-t)])
                                                     vars))]]
                      (reduce
                        (fn [else [sid sdef]]
                          (let [flows (:flows sdef)]
                            [:ite [:eq state-var (state-val z3 ha-type sid)]
                             [:and
                              (flow-constraints z3 ha-id flows v0-vars vT-vars last-t new-t)
                              (jump-constraints z3 ha-type ha-id flows (:edges sdef) v0-vars vT-vars next-vars last-t new-t)]
                             else]))
                        false
                        (:states ha-def)))]
    (assert-all! z3 constraints)
    (assoc z3 :last-t new-t)))

(defn assert-flow-jump! [{last-t :last-t
                          has    :has :as z3}
                         controlled-ha-id
                         {target :target index :index}
                         new-t]
  (let [ha-type (get has controlled-ha-id)]
    (assert-all!
      z3
      ; assert that controlled-edge will happen (constrain the future)
      [[:eq (state-var z3 ha-type controlled-ha-id "state" new-t) (state-val z3 ha-type target)]
       [:eq (var-name controlled-ha-id "out-edge" last-t) index]]))
  ; do a symbolic execution step
  (symx-1! z3 new-t))

(defn symx! [{ctx :context :as z3} unroll-limit]
  (let [vars (map (fn [idx]
                    (.mkFreshConst ctx
                                   (str "symx-step-" idx)
                                   (.mkRealSort ctx)))
                  (range 0 unroll-limit))]
    [(reduce symx-1! z3 vars) vars]))

(defn value [{ctx :context o :optimizer s :solver :as z3} var-or-vars]
  (let [vars (if (sequential? var-or-vars)
               var-or-vars
               [var-or-vars])]
    (assert (= :sat (check! z3)))
    (push! z3)
    (let [var-consts (map (fn [var]
                            (if (instance? Expr var)
                              var
                              (.mkRealConst ctx var)))
                          vars)
          _ (check! z3)
          model (.getModel (or o s))
          ;_ (println "Model" (.toString model) "Vc" (.toString var-const))
          results (map (fn [v]
                         (let [result (.getConstInterp model ^Expr v)]
                           (if (.isReal result)
                             (rat->float result)
                             (.toString result))))
                       var-consts)]
      (pop! z3)
      results)))

;;todo: refactor min-loop and max-loop, lex-min and lex-max

(defn- min-loop [{ctx :context s :solver :as z3} var-const upper-bound lower-bound]
  (loop [upper-bound upper-bound
         lower-bound lower-bound]
    (assert (>= upper-bound lower-bound))
    (if (= upper-bound lower-bound)
      lower-bound
      ;bisect-based min-solving. check the lower half first and if it's sat, use model as new upper bound and recurse with same lower bound. if it's unsat, use (/ upper-bound 2) as the next lower bound and check the upper half (/ upper-bound 2) ... (- upper-bound precision). if it's unsat, upper-bound is the best we can do assuming convex optimization region so yield it. if it's sat, recur with the new model value as upper bound and the new lower bound from before.
      (let [delta (- upper-bound lower-bound)
            _ (push! z3)
            z3 (assert-all! z3
                            [[:lt var-const (+ lower-bound (/ delta 2))]
                             [:geq var-const lower-bound]])
            lower-status (check! z3)
            lower-val (if (= lower-status :sat)
                        (value z3 var-const)
                        nil)
            _ (pop! z3)]
        (if (= lower-status :sat)
          (recur lower-val lower-bound)
          (let [_ (push! z3)
                z3 (assert-all! z3
                                ; todo: [:- upper-bound precision]?
                                [[:lt var-const upper-bound]
                                 [:geq var-const (+ lower-bound (/ delta 2))]])
                upper-status (check! z3)
                upper-val (if (= upper-status :sat)
                            (value z3 var-const)
                            nil)
                _ (pop! z3)]
            (if (not= upper-status :sat)
              upper-bound
              (recur upper-val (+ lower-bound (/ delta 2))))))))))

(defn lex-min [{ctx :context s :solver :as z3} vars lb]
  (assert (= :sat (check! z3)))
  (push! z3)
  (let [results (doall (for [var vars
                             :let [var-const (if (instance? Expr var)
                                               var
                                               (.mkRealConst ctx var))
                                   result (min-loop z3 var-const (value z3 var-const) lb)]]
                         (do
                           (assert-all! z3 [[:eq var-const result]])
                           result)))]
    (pop! z3)
    results))

(defn max-loop [{ctx :context s :solver :as z3} var-const lower-bound upper-bound]
  (loop [lower-bound lower-bound
         upper-bound upper-bound]
    (assert (>= upper-bound lower-bound))
    (if (= upper-bound lower-bound)
      upper-bound
      (let [delta (- upper-bound lower-bound)
            ; do the higher half first then the lower half
            _ (push! z3)
            z3 (assert-all! z3
                            [[:gt var-const (+ lower-bound (/ delta 2))]
                             [:leq var-const upper-bound]])
            upper-status (check! z3)
            upper-val (if (= upper-status :sat)
                        (value z3 var-const)
                        nil)
            _ (pop! z3)]
        (if (= upper-status :sat)
          ; we learned a new lower bound (upper val) from the high section. upper bound is unchanged.
          (recur upper-val upper-bound)
          (let [_ (push! z3)
                z3 (assert-all! z3
                                [[:gt var-const lower-bound]
                                 [:leq var-const (+ lower-bound (/ delta 2))]])
                lower-status (check! z3)
                lower-val (if (= lower-status :sat)
                            (value z3 var-const)
                            nil)
                _ (pop! z3)]
            (if (not= lower-status :sat)
              ; more results were not present in the higher nor the lower half, so we're done
              lower-bound
              ; from the lower half, we learned a new upper bound and a new lower bound (since it must be below the pivot)
              (recur lower-val (+ lower-bound (/ delta 2))))))))))

(defn lex-max [{ctx :context s :solver :as z3} vars ub]
  (assert (= :sat (check! z3)))
  (push! z3)
  (let [results (doall (for [var vars
                             :let [var-const (if (instance? Expr var)
                                               var
                                               (.mkRealConst ctx var))
                                   result (max-loop z3 var-const (value z3 var-const) ub)]]
                         (do
                           (assert-all! z3 [[:eq var-const result]])
                           result)))]
    (pop! z3)
    results))

(defn min-value [z3 var lb]
  (lex-min z3 [var] lb))

(defn max-value [z3 var ub]
  (lex-max z3 [var] ub))

(defn path-constraints [{has :has ha-defs :ha-defs :as z3} time-steps]
  (println "has" has "ts" time-steps)
  (assert has)
  (let [all-vars (apply concat (map-indexed
                                 (fn [idx t]
                                   (apply
                                     concat
                                     (for [[ha-id ha-type] has]
                                       (let [exit? (< idx (dec (count time-steps)))
                                             state-var (state-var z3 ha-type ha-id "state" t)
                                             edge-var (when exit? (var-name ha-id "out-edge" t))]
                                         (if exit?
                                           [[:state ha-type state-var] [:edge ha-type edge-var]]
                                           [[:state ha-type state-var]])))))
                                 time-steps))
        all-vals (zipmap all-vars (value z3 (map #(nth % 2) all-vars)))
        result (into [:and]
                     (for [[[var-type ha-type var-nom] val] all-vals]
                       (do (case var-type
                             :state [:eq var-nom (state-val z3 ha-type
                                                            (if *use-datatypes*
                                                              val
                                                              (nth (vec (keys (get-in z3 [:state-sorts (var-name ha-type "state") :consts])))
                                                                   (int val))))]
                             :edge [:eq var-nom val]))))
        moves-per-t (doall (map (fn [t]
                                  (let [ha-edges (doall (for [[ha-id ha-type] has
                                                              :let [state-var [:state ha-type (state-var z3 ha-type ha-id "state" t)]
                                                                    state-val (get all-vals state-var)
                                                                    state-id (if *use-datatypes*
                                                                               state-val
                                                                               (keyword
                                                                                 (nth (vec (keys (get-in z3 [:state-sorts (var-name ha-type "state") :consts])))
                                                                                      (int state-val))))
                                                                    _ (println "sv sval sid" state-var state-val state-id)
                                                                    edge-var [:edge ha-type (var-name ha-id "out-edge" t)]
                                                                    edge-val (get all-vals edge-var)
                                                                    edge (when (not= edge-val -1)
                                                                           (get-in ha-defs [ha-type :states state-id :edges edge-val]))
                                                                    _ (println "ev eval e" edge-var edge-val edge)]]
                                                          [ha-id edge]))]
                                    [t ha-edges]))
                                time-steps))]
    (println "path constraint" (map #(.toString (translate-constraint z3 %)) result))
    (println "moves" moves-per-t)
    [result moves-per-t]))

(defn const->guard-var [const]
  (let [[[id third & [last]] index] (split-var-name (.toString const))]
    [(if last
       [(keyword id) (keyword third last)]
       [(keyword id) (keyword third)])
     index]))

(defn guard-var->const [{context :context} owner-id [ha-id var] idx]
  (when ha-id
    (var->const context
                [(if (= ha-id :$self)
                   owner-id
                   ha-id)
                 var]
                idx)))

(defn primitive-guard->z3 [{ctx :context :as z3}
                           owner-id
                           g
                           idx]
  (assert g)
  (assert (vector? g))
  (let [rel (first g)
        a (if (nth g 1)
            (var->const z3 (update (nth g 1) 0 (fn [id] (if (= id :$self) owner-id id))) idx)
            (.mkReal ctx 0))
        b (if (and (= 4 (count g))
                   (nth g 2))
            (var->const z3 (update (nth g 2) 0 (fn [id] (if (= id :$self) owner-id id))) idx)
            (.mkReal ctx 0))
        a-b (.mkSub ctx (into-array RealExpr [a b]))
        c-float (last g)
        c-denom 1000
        c-int (Math/round ^double (* c-float c-denom))
        c (.mkReal ctx c-int c-denom)]
    (case rel
      :lt
      (.mkLt ctx a-b c)
      :leq
      (.mkLe ctx a-b c)
      :gt
      (.mkGt ctx a-b c)
      :geq
      (.mkGe ctx a-b c))))

(defn guard->z3- [{ctx :context has :has :as z3} owner-id g idx]
  (case (first g)
    :and (.mkAnd ctx (into-array (map #(guard->z3- z3 owner-id % idx) (rest g))))
    :or (.mkOr ctx (into-array (map #(guard->z3- z3 owner-id % idx) (rest g))))
    :debug (guard->z3- z3 owner-id (second g) idx)
    nil (.mkTrue ctx)
    (:in-state :not-in-state)
    (let [[check ha-id state] (rest g)
          ha-type (get has ha-id)
          state-var (state-var z3 ha-type ha-id "state" idx)
          state-val (state-val z3 ha-type state)]
      (case check
        :in-state
        (.mkEq ctx state-var state-val)
        :not-in-state
        (.mkNot ctx (.mkEq ctx state-var state-val))))
    (primitive-guard->z3 z3 owner-id g idx)))

(defn guard->z3
  ([z3 g] (guard->z3 z3 :$self g 0))
  ([{ctx :context :as z3} owner-id g idx]
    #_(println "guard->z3" g)
   (if (nil? g)
     (.mkTrue ctx)
     (let [guard (guard->z3- z3 owner-id g idx)
           tac (.then ctx
                      (.mkTactic ctx "simplify")
                      (.mkTactic ctx "propagate-ineqs")
                      (into-array [(.mkTactic ctx "ctx-solver-simplify")]))
           goal (.mkGoal ctx true false false)
           _ (.add goal (into-array [guard]))
           ar (.apply tac goal)
           sgs (.getSubgoals ar)
           goal-formulae (mapcat #(.getFormulas %) sgs)
           simplified-guard (if (= 1 (count goal-formulae))
                              (first goal-formulae)
                              (.mkAnd ctx (into-array goal-formulae)))]
       (cond
         (.isTrue simplified-guard) nil
         (.isFalse simplified-guard) [:contradiction g]
         :else simplified-guard)))))

(defn flip-rel [rel]
  (case rel
    :lt :gt
    :leq :geq
    :gt :lt
    :geq :leq))

(defn z3->primitive-guard [z3 rel args]
  (case rel
    (:in-state :not-in-state)
    ;(.mkEq ctx state-var state-val)
    (let [state-var (first args)
          [[ha-id _nom] idx] (split-var-name (.toString state-var))
          state-val (second args)
          state-val-kw (keyword (.toString state-val))]
      [rel ha-id state-val-kw])
    (:gt :geq :leq :lt)
    (let [a (first args)
          b (if (= 3 (count args))
              (second args)
              nil)
          c (last args)
          [rel a b c] (if (.isNumeral a)
                        [(flip-rel rel) c b a]
                        [rel a b c])
          [av _idx-a] (const->guard-var a)
          [bv _idx-b] (if (and b (.isNumeral b))
                        (const->guard-var b)
                        nil)
          cv (rat->float c)]
      (if bv
        [rel av bv cv]
        [rel av cv]))))

;todo: handle in-state, not-in-state
(defn z3->guard [z3 g]
  (cond
    (.isFalse g) (throw (IllegalArgumentException. "Can't represent contradiction as guard"))
    (.isTrue g) nil
    (.isAnd g) (apply vector :and (map #(z3->guard z3 %) (.getArgs g)))
    (.isOr g) (apply vector :or (map #(z3->guard z3 %) (.getArgs g)))
    (.isNot g) (let [inner ^Expr (aget (.getArgs g) 0)
                     neg-rel (cond
                               (.isEq inner) :not-in-state
                               (.isLE inner) :gt
                               (.isGE inner) :lt
                               :else (throw (IllegalArgumentException. "Unrecognized simplified guard")))]
                 (z3->primitive-guard z3 neg-rel (.getArgs inner)))
    (.isEq g) (z3->primitive-guard z3 :in-state (.getArgs g))
    (.isLT g) (z3->primitive-guard z3 :lt (.getArgs g))
    (.isLE g) (z3->primitive-guard z3 :leq (.getArgs g))
    (.isGT g) (z3->primitive-guard z3 :gt (.getArgs g))
    (.isGE g) (z3->primitive-guard z3 :geq (.getArgs g))))

(defn simplify-guard [z3 g]
  (if (= (first g) :contradiction)
    g
    (let [zg (guard->z3 z3 g)]
      (if (and (vector? zg)
               (= (first zg) :contradiction))
        zg
        (ha/easy-simplify (z3->guard z3 zg))))))