(ns ha.z3
  (:require [clojure.string :as string]
            [ha.ha :as ha]
            [ha.eval :as heval]
            [ha.desugar :as desugar]
            [fipp.edn :as fipp])
  (:import [com.microsoft.z3 Context Expr Goal RatNum
                             BoolExpr RealExpr
                             EnumSort Status
                             Solver ArithExpr Z3Exception Tactic Global Model]
           (java.util HashMap)
           (ha.ha HA)))

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

(defn rat->float [c]
  (cond
    ; integer
    (.isIntNum c) (.getInt64 c)
    ; rational
    (.isRatNum c) (/ (.getInt64 (.getNumerator c))
                     (.getInt64 (.getDenominator c)))
    ; sure, why not?
    (= (.toString c) "epsilon") (/ 1 100000000)
    (.isAlgebraicNumber c) (Double/parseDouble (subs (.toDecimal c 30) 0 29))
    ; something else
    :else (do (println "something else" (.toString c))
              (throw (IllegalArgumentException. (str "Can't make sense of " (.toString c)))))))

(defn float->real [{ctx :context} val]
  (when (and (or (instance? Float val)
                 (instance? Double val))
             (or (.isNaN val)
                 (.isInfinite val)))
    (throw (IllegalArgumentException. "Only finite vals are OK")))
  (let [val-denom 1000000
        val-int (Math/round ^double (* val val-denom))
        rat (.mkReal ctx val-int val-denom)]
    (assert (<= (Math/abs ^double (- (rat->float rat) (/ (double val-int) val-denom))) 1)
            (str "R: " (.toString rat) " RF: " (rat->float rat) " VALDIV: " val-int "/" val-denom " = " (/ (double val-int) val-denom)))
    rat))

(defn update-ha-defs [{context        :context
                       use-datatypes? :use-datatypes :as z3}
                      ha-defs]
  (let [state-sorts
        (into {}
              (for [[ha-type {states :states}] ha-defs
                    :let [sort-name (var-name ha-type "state")
                          state-ids (sort (map (fn [[sid _s]]
                                                 (name sid))
                                               states))
                          sort (.mkEnumSort context
                                            ^String sort-name
                                            ^"[Ljava.lang.String;" (into-array state-ids))]]
                [sort-name
                 {:sort   (if use-datatypes?
                            sort
                            (.mkIntSort context))
                  :consts (zipmap state-ids
                                  (if use-datatypes?
                                    (.getConsts sort)
                                    (map #(.mkInt context %) (range 0 (count state-ids)))))}]))]
    (assoc z3 :state-sorts state-sorts
              :ha-defs ha-defs)))

(defn ->z3 [ha-defs settings]
  (let [settings (merge {:use-datatypes? false}
                        settings)]
    (update-ha-defs (merge settings
                           {:context (Context. (reduce
                                                 (fn [m [k v]]
                                                   (.put m k v)
                                                   m)
                                                 (HashMap.)
                                                 (merge {"proof"             "false"
                                                         "well_sorted_check" "true"
                                                         "model"             "true"
                                                         "model_validate"    "true"
                                                         "unsat_core"        "false"}
                                                        (into {}
                                                              (map (fn [[k v]]
                                                                     [(name k) (str v)])
                                                                   (dissoc
                                                                     settings
                                                                     :must-semantics?
                                                                     :stuck-implies-done?
                                                                     :use-datatypes?
                                                                     :linearize?))))))})
                    ha-defs)))

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
                                            (.usingParams ctx
                                                          (.mkTactic ctx "qe")
                                                          (map->params ctx {:qe-nonlinear true}))
                                            (.mkTactic ctx "tseitin-cnf")
                                            (.orElse ctx
                                                     (.mkTactic ctx "smt")
                                                     (.cond ctx (.mkProbe ctx "is-lia")
                                                            (.mkTactic ctx "qflia")
                                                            (.cond ctx (.mkProbe ctx "is-nia")
                                                                   (.mkTactic ctx "qfnia")
                                                                   (.orElse ctx
                                                                            (.mkTactic ctx "qfnra")
                                                                            (.orElse ctx
                                                                                     (.mkTactic ctx "qfnra-nlsat")
                                                                                     (.mkTactic ctx "nlsat"))))))]))
        s (.mkSolver ctx stacs)
        oparams (.mkParams ctx)
        o nil #_(.mkOptimize ctx)
        z3 (assoc z3 :optimizer o :solver s :last-t nil :prev-last-t nil)
        ret (func z3)]
    (Global/setParameter "pp.decimal" "true")
    (when s
      (.setParameters s (map->params ctx
                                     {"smt.arith.nl"        true
                                      "smt.arith.nl.rounds" 4096
                                      "smt.mbqi"            true
                                      })))
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

(defn model? [m] (instance? Model m))
(defn not-model? [m] (not (model? m)))

(defn check! [{s :solver}]
  #_(println "check" (.toString s))
  (let [status (.check s)]
    (println status)
    (cond
      (= status Status/UNSATISFIABLE) :unsat                ;todo: unsat core?
      (= status Status/SATISFIABLE) (.getModel s)
      (= status Status/UNKNOWN) (do
                                  (Thread/sleep 100)
                                  (println "-----CHECK-----\n" s "\n-----\n" "NAs:" (.getNumAssertions s) "\n" "Stats:" (.getStatistics s))
                                  (println "reason:" (.toString (.getReasonUnknown s)))
                                  (Thread/sleep 500)
                                  (assert false)
                                  :unknown)
      :else (throw (IllegalStateException. (str "Unrecognizable status from solver" status))))))

(defn value [{ctx :context} ^Model model var]
  (assert (model? model))
  (let [var-expr (if (instance? Expr var)
                   var
                   (.mkRealConst ctx var))
        ;_ (println "get var from model" var var-expr)
        ;todo: if the var is not in the model, return nil. don't just use try/catch!
        result (try
                 (.getConstInterp model ^Expr var-expr)
                 (catch Z3Exception _e
                   #_(println "z3exception" (.toString _e))
                   nil))]
    (cond
      (nil? result) nil
      (or (.isReal result) (.isInt result)) (rat->float result)
      (.isTrue result) true
      (.isFalse result) false
      :else (.toString result))))

(defn picked-out-edge-c [{has     :has
                          ha-defs :ha-defs
                          ctx     :context} ha-id state edge-idx t]
  (let [ha-type (get has ha-id)
        ha-def (get ha-defs ha-type)
        max-edge-count (apply max (map #(count (:edges %)) (vals (:states ha-def))))
        edges (range -1 max-edge-count)
        sdef (get-in ha-def [:states state])]
    (assert (>= edge-idx -1))
    (assert (< edge-idx (count (:edges sdef))) (str "Picked out edge " edge-idx " for state " state " with " (count (:edges sdef)) " edges: " sdef))
    (into [:and]
          (map (fn [i]
                 (let [nom (var-name ha-id "out-edge" i t)
                       bc (.mkBoolConst ctx nom)]
                   (if (= i edge-idx)
                     [:eq bc true]
                     [:eq bc false])))
               edges))))

(defn in-state-c [{has     :has
                   ha-defs :ha-defs
                   ctx     :context} ha-id state-name t]
  (let [ha-type (get has ha-id)
        states (keys (get-in ha-defs [ha-type :states]))]
    (into [:and]
          (map (fn [id]
                 (let [nom (var-name ha-id "state" id t)
                       bc (.mkBoolConst ctx nom)]
                   (if (= id state-name)
                     [:eq bc true]
                     [:eq bc false])))
               states))))

(defn path-component [{has :has ha-defs :ha-defs ctx :context :as z3}
                      model
                      ha-id
                      t]
  (let [ha-type (get has ha-id)
        ha-def (get ha-defs ha-type)
        states (:states ha-def)
        in-state (some (fn [{id :id :as s}]
                         (if (value z3 model (.mkBoolConst ctx (var-name ha-id "state" id t)))
                           s
                           nil))
                       (vals states))
        out-edge (some
                   (fn [{i :index :as e}]
                     (if (value z3 model (.mkBoolConst ctx (var-name ha-id "out-edge" i t)))
                       e
                       nil))
                   (concat [{:index -1 :sample-edge true}]
                           (:edges in-state)))]
    [(:id in-state) (:index out-edge)]))

(defn path-components [{has :has :as z3}
                       model
                       t]
  (into {}
        (map (fn [ha-id]
               [ha-id (path-component z3 model ha-id t)])
             (keys has))))

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
            (doseq [[idx ri] (zipmap (range 0 (count r)) r)]
              (when-not (instance? BoolExpr ri)
                (println "not bool" ri "from" idx "=" (nth (vec (rest c)) idx) "of" c)))
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
            (when (number? (nth c 2))
              (assert (<= (Math/abs ^Double (- (rat->float n2)
                                               (nth c 2))) 1) (str "weird number conversion " (nth c 2) "->" n2 "->" (.toString n2))))
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

(defn assert-all! [{opt  :optimizer
                    solv :solver :as z3} constraints]
  (let [translated (translate-constraint z3 (into [:and] constraints))]
    (when (or (not (coll? constraints))
              (coll? (ffirst constraints)))
      (throw (IllegalArgumentException. "assert-all! takes a collection of constraints")))
    #_(println "assert all" (.toString translated))
    (when opt
      (.Add opt
            ^"[Lcom.microsoft.z3.BoolExpr;"
            (into-array BoolExpr [translated])))
    (when solv
      (.add solv
            ^"[Lcom.microsoft.z3.BoolExpr;"
            (into-array BoolExpr [translated]))
      #_(println "still sat?")
      #_(println (.check solv))))
  z3)

(defn assert-valuation! [z3
                         ha-vals
                         t-var]
  (let [constraints (conj
                      (apply
                        concat
                        (for [{this-state :state
                               this-v0    :v0
                               this-id    :id}
                              (vals ha-vals)]
                          (do
                            (println "init ha" this-id "state" this-state)
                            (conj
                              (for [[v k] this-v0]
                                [:eq
                                 (var-name this-id v "enter" t-var)
                                 k])
                              (in-state-c z3 this-id this-state t-var)))))
                      [:eq t-var (apply max (map :entry-time (vals ha-vals)))])]
    (assert-all! z3 constraints)
    (assoc z3 :last-t t-var
              :prev-last-t nil
              :has (into {}
                         (map (fn [ha]
                                [(:id ha) (:ha-type ha)])
                              (vals ha-vals))))))

(declare guard->z3)


(defn flow-constraints- [{must-semantics? :must-semantics? :as _z3}
                         _ha-id
                         flows
                         v0-vars
                         vT-vars
                         last-t
                         new-t
                         dt]
  (for [[v f0] v0-vars
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
                dv [:- limit flow0]
                avg-acc-speed [:/ [:+ flow0 limit] 2]
                acc-duration [:/ dv acc]
                acc-time [:+ last-t acc-duration]
                limit-duration [:- new-t acc-time]
                acc-part [:* avg-acc-speed acc-duration]
                limit-part [:* limit limit-duration]]
            (if must-semantics?
              ; sampling refinement.
              [:ite [:eq flow0 limit]
               ; linear part
               [:eq f1 [:+ f0 [:* flow0 dt]]]
               ; quadratic part. force dt <= time to reach limit. this means we'll
               ; have a self-transition, probably a global self-transition.
               [:and
                [:eq f1 [:+ f0 [:* flow0 dt] [:* acc dt dt]]]
                [:leq dt acc-duration]]]
              [:ite [flow-rel [:+ flow0 [:* acc dt]] limit]
               ;all quadratic
               [:eq f1 [:+ f0 [:* flow0 dt] [:* acc dt dt]]]
               ;average quadratic part, then add linear part
               [:eq f1 [:+ f0 acc-part limit-part]]]))))
      (vector? flow)
      (let [[acc limit] flow
            acc-rel (if (> acc 0)
                      :leq
                      :geq)
            dv [:- limit f0]
            f0-not-at-limit [acc-rel [:+ f0 [:* acc dt]] limit]]
        (if must-semantics?
          [:ite [:eq f0 limit]
           ; limit part
           [:eq f1 f0]
           ; accelerating part (don't continue past limit!)
           [:and
            [:eq f1 [:+ f0 [:* acc dt]]]
            [:leq dt [:/ dv acc]]]]
          ; max
          [:and
           [:implies f0-not-at-limit [:eq f1 [:+ f0 [:* acc dt]]]]
           [:implies [:not f0-not-at-limit] [:eq f1 limit]]])))))

(defn nonlinear-predicate [_z3 x-ha x-flows x-var t]
  (let [vx (get x-flows x-var 0)
        [_vvx xlimit] (get x-flows vx 0)
        vvx-name (when (keyword? vx) (var-name x-ha vx "enter" t))]
    (if vvx-name
      [:not [:eq xlimit vvx-name]]
      false)))

(defn definitely-linear? [x-flows y-flows x-var y-var]
  (let [vx (get x-flows x-var 0)
        vy (get y-flows y-var 0)]
    (and (or (number? vx) (number? (get x-flows vx 0)))
         (or (number? vy) (number? (get y-flows vy 0))))))

(defn d-dt [z3 x-ha x-flows x-var y-ha y-flows y-var guard t]
  (let [rel (first guard)
        [xacc _xlimit] (get x-flows (get x-flows x-var) [0 0])
        [yacc _ylimit] (get y-flows (get y-flows y-var) [0 0])
        a (- xacc yacc)
        b [:-
           (if x-var
             (var-name x-ha x-var "enter" t)
             0)
           (if y-var
             (var-name y-ha y-var "enter" t)
             0)]]
    [rel (* 2 a) b]))

(defn inv-forall [z3 ha-id state guard v0-vars vT-vars last-t new-t dt]
  #_[:forall (concat [mid-t mid-dt] (vals vmid-vars))
     [:and
      [:gt mid-t last-t]
      [:lt mid-t new-t]
      (flow-constraints- z3 ha-id flows v0-vars vmid-vars last-t mid-t mid-dt)]
     (guard->z3 z3 ha-id guard mid-t)]
  ; can't do the above, so this function implements the \(\tau\) transformation
  ; from http://www.cs.utexas.edu/~hunt/FMCAD/FMCAD12/031.pdf , assuming guard
  ; is the state invariant. Most of the hairiness comes from the inconvenience
  ; of getting variables, flows, etc from either one or two HAs, and the
  ; "accelerate up to limit" semantics.
  (case (first guard)
    (:and :or) (into [(first guard)] (map #(inv-forall z3 ha-id (:flows state) % v0-vars vT-vars last-t new-t dt) (rest guard)))
    (:lt :leq :geq :gt)
    [:and
     ; was satisfied at start and is satisfied at end
     (guard->z3 z3 ha-id guard last-t)
     (guard->z3 z3 ha-id guard new-t)
     ; nonlinear case:
     (let [[x-ha x-var] (second guard)
           x-type (when x-ha (get-in z3 [:has x-ha]))
           x-states (if x-ha
                      (if (= x-ha ha-id)
                        [state]
                        (get-in z3 [:ha-defs x-type :states]))
                      [:none])
           [y-ha y-var] (when (= (count guard) 4)
                          (nth guard 2))
           y-type (when y-ha (get-in z3 [:has y-ha]))
           y-states (if y-ha
                      (if (= y-ha ha-id)
                        [state]
                        (get-in z3 [:ha-defs y-type :states]))
                      [:none])
           c (last guard)]
       (into [:and]
             (for [xs x-states
                   ys y-states
                   :let [x-flows (if (= xs :none)
                                   {}
                                   (:flows xs))
                         y-flows (if (= ys :none)
                                   {}
                                   (:flows ys))
                         [_rel a b] (d-dt z3 x-ha x-flows x-var y-ha y-flows y-var guard last-t)
                         g't b
                         g't' [:+ b [:* a dt]]
                         gt (last guard)
                         gt'-leq (guard->z3 z3 ha-id (assoc guard 0 :leq) new-t)
                         gt'-geq (guard->z3 z3 ha-id (assoc guard 0 :geq) new-t)]]
               (if (definitely-linear? x-flows y-flows x-var y-var)
                 true
                 [:implies
                  [:and
                   [:or
                    (nonlinear-predicate z3 x-ha x-flows x-var last-t)
                    (nonlinear-predicate z3 y-ha y-flows y-var last-t)]
                   (if x-ha
                     (in-state-c z3 x-ha (:id xs) last-t)
                     true)
                   (if y-ha
                     (in-state-c z3 y-ha (:id ys) last-t)
                     true)]
                  ;and constant(d/dt(guard), last-t, new-t)
                  ; we only have at most quadratic invariants, so we only have linear derivatives,
                  ;   so we can roll the definition of <constant> right in here.
                  ; either the derivative was and is positive or it was and is negative within last-t...new-t.
                  ; by definition, the derivative of a linear function is always constant, so we don't have an extra
                  ; "and" clause in here.
                  [:and
                   [:or
                    [:and [:geq g't 0] [:geq g't' 0]]
                    [:and [:leq g't 0] [:leq g't' 0]]]
                   ;lemmas:
                   ; "when the derivative is positive g can only increase
                   ; (thus cannot pass from positive to negative) and vice versa
                   ; when g ̇ is negative g can only decrease
                   ; (thus cannot pass from negative to positive)"
                   ;(g ̇(t) > 0∨g ̇(t′) > 0) →
                   ;((g(t) ≥ 0 → g(t′) ≥ 0) ∧ (g(t′) ≤ 0 → g(t) ≤ 0))∧
                   ;
                   ;(g ̇(t) < 0∨g ̇(t′) < 0) →
                   ;((g(t) ≤ 0 → g(t′) ≤ 0) ∧ (g(t′) ≥ 0 → g(t) ≥ 0))
                   #_[:implies
                      [:or [:gt g't 0] [:gt g't' 0]]
                      [:and
                       [:implies [:geq gt 0] gt'-geq]
                       [:implies gt'-leq [:leq gt 0]]]]
                   #_[:implies
                      [:or [:lt g't 0] [:lt g't' 0]]
                      [:and
                       [:implies [:leq gt 0] gt'-leq]
                       [:implies gt'-geq [:geq gt 0]]]]]]))))]
    guard))

(defn guard-interior [g]
  (case (first g)
    (:and :or :not) (into [(first g)] (map guard-interior (rest g)))
    nil nil
    (:in-state :not-in-state) g
    ; <= -> < and >= -> >
    :leq (assoc g 0 :lt)
    :geq (assoc g 0 :gt)
    ; a - b < c --> a - b <= c - precision
    :lt (assoc g 0 :leq (dec (count g)) (- (last g) heval/precision))
    ; a - b > c --> a - b >= c + precision
    :gt (assoc g 0 :leq (dec (count g)) (+ (last g) heval/precision))))

(defn flow-constraints [{must-semantics? :must-semantics? :as z3}
                        ha-id
                        state
                        v0-vars
                        vT-vars
                        last-t
                        new-t]
  (assert (not= new-t last-t))
  (let [dt (var-name "dt" new-t last-t)
        flow-cons (flow-constraints- z3 ha-id (:flows state) v0-vars vT-vars last-t new-t dt)
        invariant-constraint (if must-semantics?
                               (inv-forall z3
                                           ha-id
                                           state
                                           ;topological closure of complement ~= complement of interior
                                           ; qua http://www-verimag.imag.fr/TR/TR-2015-10.pdf
                                           (ha/negate-guard
                                             (guard-interior (into [:or]
                                                                   (map :guard
                                                                        (filter ha/required-transition? (:edges state))))))
                                           v0-vars
                                           vT-vars
                                           last-t
                                           new-t
                                           dt)
                               true)]
    (into
      [:and
       [:eq dt [:- new-t last-t]]
       [:geq dt heval/time-unit]
       invariant-constraint]
      flow-cons)))

(defn jump-constraints [z3 ha-type ha-id state edges vT-vars next-vars last-t new-t]
  ;todo: later, once collision guards stick around, need to know about colliders
  (println "edges:" (count edges))
  (let [self-jump (into [:and
                         (picked-out-edge-c z3 ha-id state -1 last-t)
                         (in-state-c z3 ha-id state new-t)]
                        (for [[v vT] vT-vars
                              :let [next-v (get next-vars v)]]
                          [:eq next-v vT]))
        optionals (into [:or]
                        (for [{i :index
                               g :guard
                               u :update-dict
                               t :target} (filter #(not (ha/required-transition? %)) edges)]
                          (into [:and
                                 (guard->z3 z3 ha-id g (var-name "exit" last-t))
                                 (picked-out-edge-c z3 ha-id state i last-t)
                                 (in-state-c z3 ha-id t new-t)]
                                ; set all next-vars to corresponding vT-vars unless update has something
                                (for [[v vT] vT-vars
                                      :let [uv (get u v nil)
                                            next-v (get next-vars v)]]
                                  (if (nil? uv)
                                    [:eq next-v vT]
                                    [:eq next-v uv])))))]
    ;"pick an edge, and forbid taking a transition when a higher priority required transition is available".
    ;ITEs among all required guards in reverse order (so innermost is lowest priority), then an OR over optional guards and self-transition in the deepest else.
    (reduce
      (fn [else {i :index
                 g :guard
                 u :update-dict
                 t :target}]
        [:ite (guard->z3 z3 ha-id g (var-name "exit" last-t))
         (into [:and
                (picked-out-edge-c z3 ha-id state i last-t)
                (in-state-c z3 ha-id t new-t)]
               ; set all next-vars to corresponding vT-vars unless update has something
               (for [[v vT] vT-vars
                     :let [uv (get u v nil)
                           next-v (get next-vars v)]]
                 (if (nil? uv)
                   [:eq next-v vT]
                   [:eq next-v uv])))
         else])
      [:or self-jump optionals]
      (filter ha/required-transition? (reverse edges)))
    ; also, no required guard can be satisfied before t. this is actually handled in flow-constraints by forcing the
    ;  invariant (no required guard holding) to be true of all time steps.
    ))

(defn single-jump-constraints [z3 ha-type ha-id state edges edge-index vT-vars next-vars last-t new-t]
  [:and
   (in-state-c z3 ha-id state last-t)
   (picked-out-edge-c z3 ha-id state edge-index last-t)
   (if (= edge-index -1)
     (into [:and
            (in-state-c z3 ha-id state new-t)]
           (for [[v vT] vT-vars
                 :let [next-v (get next-vars v)]]
             [:eq next-v vT]))
     (let [{i :index
            g :guard
            u :update-dict
            t :target} (get edges edge-index)]
       (into [:and
              ; this transition is available
              (guard->z3 z3 ha-id g (var-name "exit" last-t))
              ; and the target state is taken
              (in-state-c z3 ha-id t new-t)]
             ; set all next-vars to corresponding vT-vars unless update has something
             (concat
               (for [[v vT] vT-vars
                     :let [uv (get u v nil)
                           next-v (get next-vars v)]]
                 (if (nil? uv)
                   [:eq next-v vT]
                   [:eq next-v uv]))
               ; no higher priority required transition is available
               (for [{i2 :index
                      g2 :guard} (filter ha/required-transition? edges)
                     :when (< i2 i)]
                 [:not (guard->z3 z3 ha-id g2 (var-name "exit" last-t))])))))])

(defn bmc-1! [{has                 :has
               ha-defs             :ha-defs
               last-t              :last-t
               plt                 :prev-last-t
               stuck-implies-done? :stuck-implies-done?
               ctx                 :context
               :as                 z3}
              new-t]
  (assert ha-defs)
  (assert (not= new-t last-t))
  ; flow from last-t to new-t
  (let [constraints (for [[ha-id ha-type] has
                          :let [ha-def (get ha-defs ha-type)
                                _ (assert ha-def)
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
                                next-vars (into {}
                                                (map (fn [v] [v (var-name ha-id v "enter" new-t)])
                                                     vars))]]
                      [:and
                       (reduce
                         (fn [else [sid sdef]]
                           (let [edges (:edges sdef)]
                             [:ite (in-state-c z3 ha-id sid last-t)
                              [:and
                               (flow-constraints z3 ha-id sdef v0-vars vT-vars last-t new-t)
                               (jump-constraints z3 ha-type ha-id sid edges vT-vars next-vars last-t new-t)]
                              else]))
                         false
                         (:states ha-def))])]
    (assert-all! z3 constraints)
    (assoc z3 :last-t new-t :prev-last-t last-t)))

(defn assert-flow-jump! [{last-t :last-t
                          ;prev-last-t :prev-last-t
                          has    :has :as z3}
                         controlled-ha-id
                         controlled-ha-state
                         {target :target index :index}
                         new-t]
  (assert-all!
    z3
    ; assert that controlled-edge will happen (constrain the future)
    [(in-state-c z3 controlled-ha-id target new-t)
     (picked-out-edge-c z3 controlled-ha-id controlled-ha-state index last-t)])
  ; do a symbolic execution step
  (bmc-1! z3 new-t))

(defn replace-pseudo-vars [z3 state t]
  (if (sequential? state)
    (case (first state)
      (:in-state :not-in-state)
      (let [[pred ha-id targets] state
            constraint (into [:or]
                             (for [target targets]
                               (in-state-c z3 ha-id target t)))]
        (if (= pred :in-state)
          constraint
          [:not constraint]))
      :var (var-name (second state) (nth state 2) "enter" t)
      (into [(first state)]
            (map #(replace-pseudo-vars z3 % t) (rest state))))
    state))

(defn assert-reached-states! [{ctx :context :as z3} time-steps state-seq]
  (let [ts (map (fn [_]
                  (.mkFreshConst ctx "check-t" (.mkRealSort ctx)))
                state-seq)]
    (assert-all!
      z3
      (concat
        ; each state desc in state seq is satisfied at some entry time,
        ; and the last state is satisfied at the last time.
        (map (fn [s t]
               (into [:or]
                     (map (fn [ti] [:and
                                    ; and the check time for this state is fixed to
                                    ; that entry time
                                    [:eq t ti]
                                    (replace-pseudo-vars z3 s ti)])
                          (if (= s (last state-seq))
                            [(last time-steps)]
                            time-steps))))
             state-seq
             ts)
        ; each check time is higher than the last
        (map (fn [prev next]
               [:lt prev next])
             (butlast ts)
             (rest ts))))))

(defn bmc! [{ctx :context :as z3} unroll-limit]
  (println "unroll" unroll-limit)
  (let [vars (map (fn [idx]
                    (.mkFreshConst ctx
                                   (str "bmc-step-" idx)
                                   (.mkRealSort ctx)))
                  (range 0 unroll-limit))
        z3 (reduce bmc-1! z3 vars)]
    [z3 vars]))

;;todo: refactor min-loop and max-loop, lex-min and lex-max

(defn- min-loop [z3 var-const upper-bound lower-bound]
  (let [precision (max heval/precision heval/time-unit)]
    (loop [upper-bound upper-bound
           lower-bound lower-bound]
      (assert (>= upper-bound lower-bound) (str "LB >= UB " lower-bound " >= " upper-bound))
      (if (<= (Math/abs ^Double (- upper-bound lower-bound)) precision)
        upper-bound
        ;bisect-based min-solving. check the lower half first and if it's sat, use model as new upper bound and recurse with same lower bound. if it's unsat, use (/ upper-bound 2) as the next lower bound and check the upper half (/ upper-bound 2) ... (- upper-bound precision). if it's unsat, upper-bound is the best we can do assuming convex optimization region so yield it. if it's sat, recur with the new model value as upper bound and the new lower bound from before.
        (let [delta (- upper-bound lower-bound)
              _ (push! z3)
              z3 (assert-all! z3
                              [[:lt var-const upper-bound]
                               [:lt var-const (+ lower-bound (/ delta 2))]
                               [:geq var-const (+ lower-bound precision)]])
              lower-model (check! z3)
              lower-val (if (model? lower-model)
                          (value z3 lower-model var-const)
                          nil)
              _ (pop! z3)]
          (if (model? lower-model)
            (recur lower-val lower-bound)
            (let [_ (push! z3)
                  z3 (assert-all! z3
                                  [[:lt var-const upper-bound]
                                   [:lt var-const (- upper-bound precision)]
                                   [:geq var-const (+ lower-bound (/ delta 2))]])
                  upper-model (check! z3)
                  upper-val (if (model? upper-model)
                              (value z3 upper-model var-const)
                              nil)
                  _ (pop! z3)]
              (if (not-model? upper-model)
                upper-bound
                (recur upper-val (+ lower-bound (/ delta 2)))))))))))

(defn lex-min [{ctx :context :as z3} vars lb]
  (assert (model? (check! z3)))
  (push! z3)
  (assert-all! z3 (map (fn [v] [:geq v lb]) vars))
  (let [results (doall (for [var vars
                             :let [var-const (if (instance? Expr var)
                                               var
                                               (.mkRealConst ctx var))
                                   _ (println "Minimize" var)
                                   ub (value z3 (check! z3) var-const)
                                   result (min-loop z3 var-const ub lb)]]
                         (do
                           (println "Minimize" var "to" result)
                           (assert-all! z3 [[:leq var-const result]])
                           result)))]
    (pop! z3)
    results))

(defn max-loop [z3 var-const lower-bound upper-bound]
  (let [precision (max heval/precision heval/time-unit)]
    (loop [lower-bound lower-bound
           upper-bound upper-bound]
      (assert (>= upper-bound lower-bound) (str "UB < LB " upper-bound " < " lower-bound))
      (println "lb" lower-bound "ub" upper-bound)
      (if (<= (Math/abs ^Double (- upper-bound lower-bound)) precision)
        lower-bound
        (let [delta (- upper-bound lower-bound)
              ; do the higher half first then the lower half
              _ (push! z3)
              z3 (assert-all! z3
                              [[:gt var-const lower-bound]
                               [:gt var-const (ha/spy "check-lower" (+ lower-bound (max (/ delta 2) precision)))]
                               [:leq var-const (- upper-bound precision)]])
              upper-model (check! z3)
              upper-val (when (model? upper-model)
                          (ha/spy "1 new lb" lower-bound (+ lower-bound (/ delta 2)) "->" (value z3 upper-model var-const)))
              _ (assert (or (not-model? upper-model)
                            (>= upper-val (+ lower-bound (max (/ delta 2) precision)))))
              _ (pop! z3)]
          (if (model? upper-model)
            ; we learned a new lower bound (upper val) from the high section. upper bound is unchanged.
            (recur (ha/spy "1 new-lb" upper-val) (ha/spy "1 new-ub" upper-bound))
            (let [_ (push! z3)
                  z3 (assert-all! z3
                                  [[:gt var-const lower-bound]
                                   [:leq var-const (+ lower-bound (/ delta 2))]])
                  lower-model (check! z3)
                  lower-val (if (model? lower-model)
                              (value z3 lower-model var-const)
                              nil)
                  _ (pop! z3)]
              (if (not-model? lower-model)
                ; more results were not present in the higher nor the lower half, so we're done
                lower-bound
                ; from the lower half, we learned a new upper bound and a new lower bound (since it must be below the pivot)
                (recur (ha/spy "2 new-lb" lower-val) (ha/spy "2 new-ub" (+ lower-bound (/ delta 2))))))))))))

(defn lex-max [{ctx :context :as z3} vars ub]
  (assert (model? (check! z3)))
  (push! z3)
  (assert-all! z3 (map (fn [v] [:leq v ub]) vars))
  (let [results (doall (for [var vars
                             :let [var-const (if (instance? Expr var)
                                               var
                                               (.mkRealConst ctx var))
                                   _ (println "Maximize" var)
                                   upper-model (check! z3)
                                   result (max-loop z3 var-const (value z3 upper-model var-const) ub)]]
                         (do
                           (println "Maximized" var "to" result)
                           (assert-all! z3 [[:geq var-const result]])
                           result)))]
    (pop! z3)
    results))

(defn min-value [z3 var lb]
  (lex-min z3 [var] lb))

(defn max-value [z3 var ub]
  (lex-max z3 [var] ub))

;todo: spec
(defn path-constraints [{has :has :as z3} time-steps]
  (println "has" has "ts" time-steps)
  (assert has)
  (let [model (check! z3)
        all-path-components (map #(path-components z3 model %) time-steps)
        all-path-component-constraints (for [[t step] (zipmap time-steps all-path-components)
                                             [ha-id [this-state this-out-edge]] step
                                             :let [state-c (in-state-c z3 ha-id this-state t)
                                                   edge-c (picked-out-edge-c z3 ha-id this-state this-out-edge t)]]
                                         (if (nil? this-out-edge)
                                           state-c
                                           [:and state-c edge-c]))
        t-vals (map #(value z3 model %) time-steps)]
    (println "path constraint" (map #(.toString (translate-constraint z3 %)) all-path-component-constraints))
    (println "moves" all-path-components)
    [all-path-component-constraints t-vals all-path-components]))

(defn const->guard-var [const]
  (let [[[id third & [last]] index] (split-var-name (.toString const))]
    [(if last
       [(keyword id) (keyword third last)]
       [(keyword id) (keyword third)])
     index]))

#_(defn guard-var->const [{context :context} owner-id [ha-id var] idx]
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

(defn guard->z3 [{ctx :context has :has :as z3} owner-id g idx]
  (case (first g)
    :and (.mkAnd ctx (into-array BoolExpr (map #(guard->z3 z3 owner-id % idx) (rest g))))
    :or (.mkOr ctx (into-array BoolExpr (map #(guard->z3 z3 owner-id % idx) (rest g))))
    :not (.mkNot ctx (guard->z3 z3 owner-id (second g) idx))
    :debug (guard->z3 z3 owner-id (second g) idx)
    nil (.mkTrue ctx)
    (:in-state :not-in-state)
    (let [[check ha-id states] g
          ha-type (get has ha-id)
          _ (assert has "has")
          _ (assert ha-id "ha-id")
          _ (assert ha-type (str "ha-type:" g ":" has ":" ha-id))
          guard-constraints (for [state states]
                              (case check
                                :in-state
                                (translate-constraint z3 (in-state-c z3 ha-id state idx))
                                :not-in-state
                                (translate-constraint z3 [:not (in-state-c z3 ha-id state idx)])))]
      (.mkOr ctx
             (into-array BoolExpr guard-constraints)))
    (primitive-guard->z3 z3 owner-id g idx)))



(defn simplify-clause [{ctx :context :as _z3} g]
  (let [tac (.then ctx
                   (.mkTactic ctx "simplify")
                   (.mkTactic ctx "propagate-ineqs")
                   (into-array [(.mkTactic ctx "ctx-solver-simplify")]))
        goal (.mkGoal ctx true false false)
        _ (.add goal (into-array [g]))
        ar (.apply tac goal)
        sgs (.getSubgoals ar)
        goal-formulae (mapcat #(.getFormulas %) sgs)
        simplified-guard (if (= 1 (count goal-formulae))
                           (first goal-formulae)
                           (.mkAnd ctx (into-array BoolExpr goal-formulae)))]
    (cond
      (.isTrue simplified-guard) nil
      (.isFalse simplified-guard) [:contradiction g]
      :else simplified-guard)))

(defn flip-rel [rel]
  (case rel
    :lt :gt
    :leq :geq
    :gt :lt
    :geq :leq))

;problem: we can't swallow up the in-state/not-in-state disjunctions properly
; into nice single guards again. ):
(defn z3->primitive-guard [_z3 rel args]
  (case rel
    (:in-state :not-in-state)
    (let [state-var (first args)
          [[ha-id _nom] _idx] (split-var-name (.toString state-var))
          state-val (second args)
          state-val-kw (keyword (.toString state-val))]
      [rel ha-id #{state-val-kw}])
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
    (let [zg (guard->z3 z3 nil g 0)
          zg (simplify-clause z3 zg)]
      (if (and (vector? zg)
               (= (first zg) :contradiction))
        zg
        (ha/easy-simplify (z3->guard z3 zg))))))

(defn simplify-guards [{ha-defs :ha-defs :as z3}]
  (ha/map-defs (fn [def]
                 (let [collider-sets (:collider-sets def)]
                   (assoc def
                     :states
                     (ha/map-states
                       (fn [state]
                         (let [colliders (get collider-sets (:collider-set state))]
                           (ha/map-transitions
                             (fn [e]
                               ; yields transition or (seq transition)
                               (let [simplified (simplify-guard z3 (:guard e))]
                                 (if (= (first simplified) :contradiction)
                                   nil
                                   (assoc e :guard
                                            simplified))))
                             state)))
                       def))))
               ha-defs))

(defn map-vals [fnk kvmap]
  (reduce
    (fn [m [k v]]
      (assoc m k (fnk v)))
    kvmap
    kvmap))

(defn option-permutations [dict]
  ; for each element E in (get dict key1), yield a new dict (merge {key1:E} (option-permutations (rest dict))).
  (let [keyvals (seq dict)
        option-groups (apply ha/cartesian-product (map second keyvals))]
    (map (fn [opts] (zipmap (map first keyvals) opts))
         option-groups)))

(defn- symx!- [{ha-defs :ha-defs
                has     :has
                ctx     :context
                :as     z3}
               bound
               target-states
               time-steps
               edge-states]
  ;assert flow condition
  (let [last-t (last time-steps)
        new-t (.mkFreshConst ctx "symx-step" (.mkRealSort ctx))]
    (assert-all! z3
                 (map (fn [[ha-id ha-type]]
                        (let [ha-def (get ha-defs ha-type)
                              [_prev-state _in-edge state] (get (last edge-states) ha-id)
                              sdef (get-in ha-def [:states state])
                              vars (map first (dissoc (:init-vars ha-def) :w :h))
                              _ (assert (not (empty? vars)))
                              v0-vars (into {}
                                            (map (fn [v]
                                                   [v (var-name ha-id v "enter" last-t)])
                                                 vars))
                              _ (assert (not (empty? v0-vars)))
                              vT-vars (into {}
                                            (map (fn [v] [v (var-name ha-id v "exit" last-t)])
                                                 vars))]
                          (flow-constraints z3 ha-id sdef v0-vars vT-vars last-t new-t)))
                      has))
    (if (<= bound 0)
      (do
        (push! z3)
        (assert-reached-states! z3 time-steps target-states)
        (let [reached-model (check! z3)]
          (pop! z3)
          (if (model? reached-model)
            [z3
             :witness
             (ha/spy "witness path"
                     (into {}
                           (map (fn [ts edge-state]
                                  [(.toString ts)
                                   (into [(value z3 reached-model ts)]
                                         edge-state)])
                                time-steps edge-states)))]
            [z3 :bound nil])))
      (let [options (option-permutations (into {}
                                               (map (fn [[ha-id ha-type]]
                                                      (let [ha-def (get ha-defs ha-type)
                                                            [_prev-state _tr-edge state] (get (last edge-states) ha-id)
                                                            state-def (get-in ha-def [:states state])
                                                            edges (concat [{:index -1 :target state :guard nil}]
                                                                          (:edges state-def))]
                                                        [ha-id
                                                         (for [{index :index target :target} edges]
                                                           [state index target])]))
                                                    has)))]
        ; loop over each distinct path constraint (or fail if no path constraints)
        (reduce
          (fn [result opt-edges-by-ha-id]
            (push! z3)
            ;     assert this path constraint and the jump condition of that constraint (giving us exit variables and enter & state variables for the new thing)
            (assert-all! z3 (map (fn [[ha-id ha-type]]
                                   ; in-state is already asserted so we don't need to mess with that
                                   ; we just want to be sure the update condition of out-edge applied
                                   (let [[_prev-state out-edge _next-state] (get opt-edges-by-ha-id ha-id)
                                         ha-def (get ha-defs ha-type)
                                         [_prev'-state _prev-out-edge in-state] (get (last edge-states) ha-id)
                                         state-def (get-in ha-def [:states in-state])
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
                                         next-vars (into {}
                                                         (map (fn [v] [v (var-name ha-id v "enter" new-t)])
                                                              vars))]
                                     (single-jump-constraints z3 ha-type ha-id in-state (:edges state-def) out-edge vT-vars next-vars last-t new-t)))
                                 has))
            (let [cur-model (check! z3)
                  symx-result (if (not-model? cur-model)
                                [z3 :unsat nil]
                                ; else, result = recurse with a decremented bound and the last path constraints
                                (symx!- z3
                                        (dec bound)
                                        target-states
                                        (conj time-steps new-t)
                                        (ha/spy "new path" (conj edge-states opt-edges-by-ha-id))))]
              (pop! z3)
              (if (= (second symx-result) :witness)
                (reduced symx-result)
                result)))
          [z3 :unsat nil]
          options)))))

(defn symx! [z3 ha-vals bound target-states]
  (let [z3 (assert-valuation! z3 ha-vals "t00")]
    (symx!- z3
            bound
            target-states
            ["t00"]
            [(into {}
                   (map (fn [ha]
                          [(:id ha) [:$start -2 (:state ha)]])
                        (vals ha-vals)))])))

(defn model-check [ha-defs ha-vals target-states unroll-limit]
  (println "model check with unroll limit" unroll-limit)
  (try
    (let [z3 (->z3 (desugar/set-initial-labels ha-defs)
                   {:must-semantics?     true
                    :stuck-implies-done? false})
          z3 (assoc z3
               :has (into {}
                          (map (fn [ha]
                                 [(:id ha) (:ha-type ha)])
                               (vals ha-vals))))
          ha-defs (simplify-guards z3)
          z3 (update-ha-defs z3 ha-defs)
          entry-time (apply max (map :entry-time (vals ha-vals)))
          [ha-vals tr-caches] (heval/init-has ha-defs (vals ha-vals) entry-time)
          config {:objects    ha-vals
                  :entry-time entry-time
                  :tr-caches  tr-caches
                  :inputs     #{}}
          check-may-first? true
          [may-status may-witness] (if check-may-first?
                                     (ha/spy "checked may"
                                             (time (reduce (fn [_ bound]
                                                             (println "check may at" bound)
                                                             (let [[may-status may-witness]
                                                                   (time (with-solver
                                                                           (assoc z3 :must-semantics? false)
                                                                           (fn [z3]
                                                                             (rest (symx! z3 (:objects config) bound target-states)))))]
                                                               (if (= may-status :witness)
                                                                 (reduced [may-status may-witness])
                                                                 [:unsat nil])))
                                                           [:unsat nil]
                                                           (range 0 (inc unroll-limit)))))
                                     [:skipped nil])
          start-depth (count may-witness)]
      (if (or (= may-status :skipped)
              (= may-status :witness))
        (ha/spy "checked must"
                (time (reduce (fn [_ bound]
                                (with-solver
                                  (assoc z3 :must-semantics? true)
                                  (fn [z3]
                                    (println "check must at" bound)
                                    (let [[z3 status all-steps] (time (symx! z3 (:objects config) bound target-states))]
                                      (println "check result:" status)
                                      (if (= status :witness)
                                        (let [moves-per-t (map
                                                            (fn [[tprev [tprevval _mprev]]
                                                                 [tnext [tnextval mnext]]]
                                                              [[tprev tprevval] [tnext tnextval] mnext])
                                                            (butlast all-steps)
                                                            (rest all-steps))
                                              ;todo: do we care about getting specific times? if so, we could do that here since we have the list of all time points and can get a valuation of those.
                                              ]
                                          (fipp/pprint ["rollout" moves-per-t] {:print-level 6})
                                          (reduced [:witness moves-per-t]))
                                        [:unsat nil])))))
                              [:unsat nil]
                              (range start-depth (inc unroll-limit)))))
        [:unsat nil]))
    (catch Exception e
      (println "Error!")
      (println (.toString e))
      (.printStackTrace e)
      [:error nil])))