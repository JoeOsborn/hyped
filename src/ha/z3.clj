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
           (java.util HashMap Date)
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
  (.mkRealConst ctx (var-name id var idx)))

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
              :geq (.mkGt ctx n1 (translate-constraint z3 [:- n2 heval/precision]))
              :eq (.mkEq ctx n1 n2)
              ;strict-inequalities-only version, seems to still get stuck.
              #_(cond
                    (and (.isConst n1)
                         ;if we care about constant propagation, try putting (.isConst n2) here and (.isConst n1) in the other one as well.
                         (.isReal n2))
                    (translate-constraint z3 [:and
                                              [:lt n1 [:+ n2 heval/precision]]
                                              [:gt n1 [:- n2 heval/precision]]])
                    (and (.isConst n2)
                         (.isReal n1))
                    (translate-constraint z3 [:and
                                              [:gt n2 [:+ n1 heval/precision]]
                                              [:lt n2 [:- n1 heval/precision]]])
                    :else (.mkEq ctx n1 n2))
              :leq (.mkLt ctx n1 (translate-constraint z3 [:+ n2 heval/precision]))
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
  (let [settings (merge {:use-datatypes?  false
                         :box-approx?     true
                         :quantifiers?    false
                         :must-semantics? true}
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
                                                                     :box-approx?
                                                                     :quantifiers?
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

(defn map-vals [fnk kvmap]
  (reduce
    (fn [m [k v]]
      (assoc m k (fnk v)))
    kvmap
    kvmap))

(defn with-solver [{ctx :context :as z3} func]
  (let [stacs (.andThen ctx
                        ; not sure how to use this properly since it seems to cause exceptions to be thrown.
                        #_(.usingParams ctx (.mkTactic ctx "add-bounds")
                                        (map->params ctx {:add_bound_lower lowest-var-val
                                                          :add_bound_upper highest-var-val}))
                        (.mkTactic ctx "qe-light")
                        (.mkTactic ctx "simplify")
                        (into-array Tactic [
                                            (.mkTactic ctx "purify-arith")
                                            (.mkTactic ctx "propagate-values")
                                            (.mkTactic ctx "propagate-ineqs")
                                            (.mkTactic ctx "solve-eqs")
                                            (.usingParams ctx
                                                          (.mkTactic ctx "simplify")
                                                          (map->params ctx {:som             true :arith-lhs true
                                                                            :hoist-cmul      true :hoist-mul true
                                                                            :ite-extra-rules true :local-ctx true
                                                                            :pull-cheap-ite  true :push-ite-arith true}))
                                            (.mkTactic ctx "aig")
                                            (.mkTactic ctx "propagate-values")
                                            (.mkTactic ctx "propagate-ineqs")
                                            (.mkTactic ctx "solve-eqs")
                                            (.usingParams ctx
                                                          (.mkTactic ctx "simplify")
                                                          (map->params ctx {:som             true :arith-lhs true
                                                                            :hoist-cmul      true :hoist-mul true
                                                                            :ite-extra-rules true :local-ctx true
                                                                            :pull-cheap-ite  true :push-ite-arith true}))
                                            (.cond ctx (.mkProbe ctx "is-lira")
                                                   (.cond ctx (.mkProbe ctx "has-quantifiers")
                                                          (.mkTactic ctx "lira")
                                                          (.mkTactic ctx "smt"))
                                                   (.andThen ctx
                                                             (.mkTactic ctx "tseitin-cnf")
                                                             (.cond ctx (.mkProbe ctx "has-quantifiers")
                                                                    (.mkTactic ctx "nlqsat")
                                                                    (.parOr ctx
                                                                            (into-array Tactic
                                                                                        [(.mkTactic ctx "smt")
                                                                                         (.andThen ctx (.mkTactic ctx "nla2bv") (.mkTactic ctx "smt") (into-array Tactic []))
                                                                                         ;todo: throw random seeds on these three
                                                                                         (.mkTactic ctx "qfnra-nlsat")
                                                                                         (.mkTactic ctx "qfnra")
                                                                                         (.mkTactic ctx "nlsat")])))
                                                             (into-array Tactic [])))]))
        s (.mkSolver ctx stacs)
        oparams (.mkParams ctx)
        o nil #_(.mkOptimize ctx)
        z3 (assoc z3 :optimizer o :solver s :last-t nil :prev-last-t nil)
        ret (func z3)]
    (Global/setParameter "pp.decimal" "true")
    (Global/setParameter "verbose" "10")
    (when s
      (.setParameters s (map->params ctx
                                     {"smt.arith.nl" false
                                      "smt.mbqi"     false})))
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
  #_(println "check\n" (.toString s))
  (spit (str "test/check-" (.getTime (Date.)) ".smt2") (str (.toString s) "\n" "(check-sat-using (then\n  qe-light\n  simplify\n  purify-arith\n  propagate-values\n  propagate-ineqs\n  solve-eqs\n  (using-params simplify\n    :som true :arith-lhs true\n    :hoist-mul true :hoist-cmul true\n    :ite-extra-rules true :local-ctx true\n    :pull-cheap-ite true :push-ite-arith true\n  )\n  aig\n  propagate-values\n  propagate-ineqs\n  solve-eqs\n  (using-params simplify\n    :som true :arith-lhs true\n    :hoist-mul true :hoist-cmul true\n    :ite-extra-rules true :local-ctx true\n    :pull-cheap-ite true :push-ite-arith true\n  )\n  (if is-lira\n    (if has-quantifiers\n      lira\n      smt)\n    (then\n      tseitin-cnf\n      (if has-quantifiers\n        nlsat\n\t(if is-nra\n\t  (par-or\n\t    smt (then nla2bv smt) qfnra-nlsat\n\t    qfnra)\n\t  fail))))))\n\n\n(get-model)"))
  (println "call solver")
  (let [status (time (.check s))]
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

(defn ha-moves [z3 model last-t new-t]
  (let [out-state-edges-by-ha-id (ha/spy "components old" (path-components z3 model last-t))
        new-states-by-ha-id (map-vals first (path-components z3 model new-t))]
    (into {}
          (map (fn [[ha-id [prev-state out-edge]]]
                 (let [in-state (get new-states-by-ha-id ha-id)]
                   [ha-id [prev-state out-edge in-state]]))
               out-state-edges-by-ha-id))))

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

(def ^:dynamic *flow-bins* 4.0)
(defn flow-bins [low high]
  (if (== low high)
    [[low high]]
    (let [w (- high low)
          bin-w (/ w *flow-bins*)]
      (distinct (mapcat (fn [b]
                          (let [lo (+ low (* bin-w b))
                                hi (+ low (* bin-w (inc b)))
                                zero (if (or (== lo 0) (== hi 0))
                                       [[0.0 0.0]]
                                       [])
                                left [] #_(if (== lo low) [[lo lo]] [])
                                right [] #_(if (== hi high) [[hi hi]] [])
                                mid (if (and (<= lo 0) (>= hi 0))
                                      [[lo 0.0] [0.0 hi]]
                                      [[lo hi]])]
                            ; this is in zero left right mid order so that we ITE on "stuck at top" or "at 0" before "near the top".
                            (concat zero left right mid)))
                        (range 0 *flow-bins*))))))

(defn flow-constraints- [{must-semantics? :must-semantics? :as _z3
                          box-approx?     :box-approx?}
                         _ha-id
                         bounds
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
            dflow (get flows flow)
            [bmin bmax] (get bounds flow)
            bins (flow-bins bmin bmax)]
        (cond
          (= dflow 0)
          (if box-approx?
            (reduce (fn [else [a b]]
                      [:ite [:and
                             [:geq flow0 a]
                             [:leq flow0 b]]
                       [:and
                        [:geq f1 [:+ f0 [:* a dt]]]
                        [:leq f1 [:+ f0 [:* b dt]]]]
                       else])
                    false
                    bins)
            [:eq f1 f0])
          (vector? dflow)
          (let [[acc limit] dflow
                dv [:- limit flow0]
                acc-duration [:/ dv acc]]
            (if box-approx?
              [:ite [:and
                     [:geq dv (- heval/precision)]
                     [:leq dv heval/precision]]
               ; linear part
               [:eq f1 [:+ f0 [:* limit dt]]]
               ; quadratic part (we'll use sampling refinement to "switch" it to linear on a subsequent timepoint)
               (reduce (fn [else [a b]]
                         [:ite [:and
                                [:geq flow0 a]
                                [:leq flow0 b]]
                          [:and
                           ;force dt <= time to reach limit. this means we'll
                           ; have a self-transition, probably a global self-transition (sampling refinement)
                           [:leq dt acc-duration]
                           ;force flow1 to be within the bin as well, for the same reason. this means we won't
                           ; have a dt that takes us (much) outside our bin.
                           ; bins have to overlap slightly or we can't leave them.
                           [:geq [:+ flow0 [:* acc dt]] (- a heval/precision)]
                           [:leq [:+ flow0 [:* acc dt]] (+ b heval/precision)]
                           ; actually bound f1 into a box flowpipe
                           [:geq f1 [:+ f0 [:* a dt]]]
                           [:leq f1 [:+ f0 [:* b dt]]]]
                          else])
                       false
                       bins)]
              [:ite [:and
                     [:geq dv (- heval/precision)]
                     [:leq dv heval/precision]]
               ; linear part
               [:eq f1 [:+ f0 [:* limit dt]]]
               ; quadratic part (we'll use sampling refinement to "switch" it to linear on a subsequent timepoint)
               [:and
                ;force dt <= time to reach limit. this means we'll
                ; have a self-transition, probably a global self-transition (sampling refinement)
                [:leq dt acc-duration]
                [:eq f1 [:+ f0 [:* flow0 dt] [:* acc dt dt]]]]]))))
      (vector? flow)
      (let [[acc limit] flow
            dv [:- limit f0]]
        ;no need for binning here. the sampling refinement for bins
        ; will be enforced above. v/ variables can be calculated precisely because
        ; they only have piecewise linear equations.
        [:ite [:or
               [:and
                [:geq dv (- heval/precision)]
                [:leq dv heval/precision]]
               ; cap velocity to limit
               [:and (> acc 0) [:leq dv 0]]
               [:and (< acc 0) [:geq dv 0]]]
         ; limit part
         [:eq f1 limit]
         ; accelerating part (don't continue past limit!)
         [:and
          [:eq f1 [:+ f0 [:* acc dt]]]
          [:leq dt [:/ dv acc]]]]))))

(defn d-dt [z3 x-ha x-flows x-var y-ha y-flows y-var guard t]
  (let [rel (first guard)
        x-flow (get x-flows x-var 0)
        y-flow (get y-flows y-var 0)
        xacc (if (number? x-flow)
               0
               (let [x-flow' (get x-flows x-flow 0)]
                 (if (vector? x-flow')
                   (first x-flow')
                   x-flow')))
        yacc (if (number? y-flow)
               0
               (let [y-flow' (get y-flows y-flow 0)]
                 (if (vector? y-flow')
                   (first y-flow')
                   y-flow')))
        xvel (if (number? x-flow)
               x-flow
               (var-name x-ha x-flow "enter" t))
        yvel (if (number? y-flow)
               y-flow
               (var-name y-ha y-flow "enter" t))
        a (- xacc yacc)
        b [:- xvel yvel]]
    [rel (* 2 a) b]))

; this function implements the \(\tau\) transformation
; from http://www.cs.utexas.edu/~hunt/FMCAD/FMCAD12/031.pdf , assuming guard
; is the state invariant. Most of the hairiness comes from the inconvenience
; of getting variables, flows, etc from either one or two HAs, and the
; "accelerate up to limit" semantics.
(defn tau-transform [z3 ha-id bounds state guard v0-vars vmid-vars vT-vars last-t mid-t new-t dt mid-dt]
  ;(println "tt" guard)
  (case (first guard)
    :not
    (tau-transform z3 ha-id bounds state (ha/negate-guard guard)
                   v0-vars vmid-vars vT-vars
                   last-t mid-t new-t dt mid-dt)
    (:and :or)
    (into [(first guard)]
          (map #(tau-transform z3 ha-id bounds state %
                               v0-vars vmid-vars vT-vars
                               last-t mid-t new-t dt mid-dt)
               (rest guard)))
    (:lt :leq :geq :gt)
    [:and
     ; was satisfied at start and is satisfied at (just before, thanks to closure) end
     (guard->z3 z3 ha-id guard (var-name "enter" last-t))
     (guard->z3 z3 ha-id guard (var-name "exit" last-t))
     ; nonlinear case
     (if (:box-approx? z3)
       true
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
                           ;fixme: is this right?
                           gt [:- x-var y-var (last guard)]
                           gt'-leq (guard->z3 z3 ha-id (assoc guard 0 :leq) (var-name "exit" last-t))
                           gt'-geq (guard->z3 z3 ha-id (assoc guard 0 :geq) (var-name "exit" last-t))]]
                 [:implies
                  [:and
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
                  [:or
                   ;if a is 0 for this derivative, then generate a simpler formula
                   (== a 0)
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
                    ;todo: fixme: these lemmas are wrong. is gt really = c? will it speed things up?
                    #_[:implies
                       [:or [:gt g't 0] [:gt g't' 0]]
                       [:and
                        [:implies [:geq gt 0] gt'-geq]
                        [:implies gt'-leq [:leq gt 0]]]]
                    #_[:implies
                       [:or [:lt g't 0] [:lt g't' 0]]
                       [:and
                        [:implies [:leq gt 0] gt'-leq]
                        [:implies gt'-geq [:geq gt 0]]]]]]]))))]
    guard))

(defn guard-interior [g]
  (case (first g)
    (:and :or :not) (into [(first g)] (map guard-interior (rest g)))
    nil nil
    true true
    false false
    (:in-state :not-in-state) g
    ; <= -> < and >= -> >
    :leq (assoc g 0 :lt)
    :geq (assoc g 0 :gt)
    ; a - b < c --> a - b <= c - precision
    :lt (assoc g 0 :leq (dec (count g)) (- (last g) heval/precision))
    ; a - b > c --> a - b >= c + precision
    :gt (assoc g 0 :geq (dec (count g)) (+ (last g) heval/precision))))

(declare simplify-guard)

(defn inv-forall [z3 ha-id bounds state req-guards v0-vars vmid-vars vT-vars last-t mid-t new-t dt mid-dt]
  ; Z3's QE procedure is too slow/general, so since I know I only have linear quantifiers and binning
  ;  gives flowpipe approx anyway, I can just use the linear case of the quantifier elimination from
  ;  Cimatti et al
  (if (:quantifiers? z3)
    [:forall (concat [mid-t mid-dt] (vals vmid-vars))
     (into [:and
            [:eq mid-dt [:- mid-t last-t]]
            [:lt mid-t new-t]]
           ;todo: FIXME: this needs to flow _all_ HAs, not just this one!
           (flow-constraints- z3 ha-id bounds (:flows state) v0-vars vmid-vars last-t mid-t mid-dt))
     [:not (guard->z3 z3 ha-id (into [:or] req-guards) (var-name "check" last-t))]]
    ;topological closure of complement ~= complement of interior --> invariant
    ; qua http://www-verimag.imag.fr/TR/TR-2015-10.pdf
    ;todo: use mid-t and mid-t-vars as "just before end"? and avoid the complexity of the interior?
    ;todo: bug in interior calculation? something about interior being wrong? or the interior of the wrong thing?
    (let [guard (:invariant state)]
      #_(.substitute guard (into-array Expr [all-world-variables-pre, all-world-variables-post]) (into-array Expr [all-world-variables-pre, all-world-variables-post]))
      ;(println "inv:" guard)
      (tau-transform z3 ha-id bounds state guard v0-vars vmid-vars vT-vars last-t mid-t new-t dt mid-dt))))

(defn flow-constraints [{must-semantics? :must-semantics? :as z3}
                        ha-id
                        bounds
                        state
                        v0-vars
                        vmid-vars
                        vT-vars
                        last-t
                        mid-t
                        new-t]
  (assert (not= new-t last-t))
  (let [dt (var-name "dt" new-t last-t)
        mid-dt (var-name "mid-dt" new-t last-t)
        flow-cons (flow-constraints- z3 ha-id bounds (:flows state) v0-vars vT-vars last-t new-t dt)
        invariant-constraint (if must-semantics?
                               (inv-forall z3
                                           ha-id
                                           bounds
                                           state
                                           (map :guard
                                                (filter ha/required-transition? (:edges state)))
                                           v0-vars
                                           vmid-vars
                                           vT-vars
                                           last-t
                                           mid-t
                                           new-t
                                           dt
                                           mid-dt)
                               true)]
    (into
      [:and
       [:eq dt [:- new-t last-t]]
       [:geq dt heval/time-unit]
       invariant-constraint]
      flow-cons)))

(defn jump-constraints [z3 ha-type ha-id state edges vT-vars next-vars last-t new-t]
  ;todo: later, once collision guards stick around, need to know about colliders
  (let [self-jump (into [:and
                         (picked-out-edge-c z3 ha-id state -1 last-t)
                         (in-state-c z3 ha-id state new-t)]
                        (for [[v vT] vT-vars
                              :let [next-v (get next-vars v)]]
                          [:eq next-v vT]))
        ha-def (get-in z3 [:ha-defs ha-type])
        opt-edges (filter #(not (ha/required-transition? %)) edges)
        optionals (if (empty? opt-edges)
                    false
                    (into [:or]
                          (for [{i :index
                                 g :guard
                                 u :update
                                 t :target} opt-edges]
                            (let [u (merge u
                                           (ha/constant-flow-overrides (get-in ha-def [:states t :flows])))]
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
                                        [:eq next-v uv])))))))]
    ;"pick an edge, and forbid taking a transition when a higher priority required transition is available".
    ;ITEs among all required guards in reverse order (so innermost is lowest priority), then an OR over optional guards and self-transition in the deepest else.
    (reduce
      (fn [else {i :index
                 g :guard
                 u :update
                 t :target}]
        (let [u (merge u (ha/constant-flow-overrides (get-in ha-def [:states t :flows])))]
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
           else]))
      [:or self-jump optionals]
      (filter ha/required-transition? (reverse edges)))))
; also, no required guard can be satisfied before t. this is actually handled in flow-constraints by forcing the
;  invariant (no required guard holding) to be true of all time steps.

;TODO: double check this! make sure the refinement works!
(defn single-jump-constraints [z3 ha-type ha-id state edges edge-index vT-vars next-vars last-t new-t]
  (let [ha-def (get-in z3 [:ha-defs ha-type])]
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
              u :update
              t :target} (get edges edge-index)]
         (let [u (merge u (ha/constant-flow-overrides (get-in ha-def [:states t :flows])))]
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
                     [:not (guard->z3 z3 ha-id g2 (var-name "exit" last-t))]))))))]))

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
                                mid-t (var-name "mid-t" new-t last-t)
                                vmid-vars (into {}
                                                (map (fn [v]
                                                       [v (var-name ha-id v "check" last-t)])
                                                     vars))
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
                               (flow-constraints z3 ha-id (:bounds ha-def) sdef v0-vars vmid-vars vT-vars last-t mid-t new-t)
                               (jump-constraints z3 ha-type ha-id sid edges vT-vars next-vars last-t new-t)]
                              else]))
                         false
                         (:states ha-def))])]
    (assert-all! z3 constraints)
    (assoc z3 :last-t new-t :prev-last-t last-t)))

#_(defn assert-flow-jump! [{last-t :last-t
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

(defn path-constraints [{has :has :as z3} model time-steps]
  (let [all-path-components (map #(path-components z3 model %) time-steps)]
    (for [[t step] (zipmap time-steps all-path-components)
          [ha-id [this-state this-out-edge]] step
          :let [state-c (in-state-c z3 ha-id this-state t)
                edge-c (picked-out-edge-c z3 ha-id this-state this-out-edge t)]]
      (if (nil? this-out-edge)
        state-c
        [:and state-c edge-c]))))

(defn assert-transition-sequence! [z3 path-steps next-vars]
  (doseq [[last-t new-t] (zipmap (butlast next-vars) (rest next-vars))
          [ha-id [prev edge _next]] (get path-steps last-t)
          :let [ha-type (get-in z3 [:has ha-id])
                ha-def (get-in z3 [:ha-defs ha-type])
                bounds (:bounds ha-def)
                sdef (get-in ha-def [:states prev])
                vars (map first (dissoc (:init-vars ha-def) :w :h))
                _ (assert (not (empty? vars)))
                v0-vars (into {}
                              (map (fn [v]
                                     [v (var-name ha-id v "enter" last-t)])
                                   vars))
                _ (assert (not (empty? v0-vars)))
                mid-t (var-name "mid-t" new-t last-t)
                vmid-vars (into {}
                                (map (fn [v]
                                       [v (var-name ha-id v "check" last-t)])
                                     vars))
                vT-vars (into {}
                              (map (fn [v]
                                     [v (var-name ha-id v "exit" last-t)])
                                   vars))]]
    (assert-all! z3 (flow-constraints z3 ha-id bounds sdef v0-vars vmid-vars vT-vars last-t mid-t new-t))
    (assert-all! z3 (single-jump-constraints z3 ha-type ha-id prev (:edges sdef) edge vT-vars next-vars last-t new-t))))

(defn bmc! [{ctx :context :as z3} objects unroll-min unroll-limit target-states]
  (println "unroll" unroll-limit)
  (let [z3 (assert-valuation! z3 objects "t00")
        vars (map (fn [idx]
                    (.mkRealConst ctx
                                  (str "bmc-step-" idx)))
                  (range 0 unroll-limit))
        _ (println "bmc")
        [z3 _t-vars status path]
        (time (reduce
                (fn [[z3 used-vars status path] t-var]
                  (println "generate one-step" (count used-vars))
                  (let [z3 (if (not= t-var "t00")
                             (time (bmc-1! z3 t-var))
                             z3)
                        _ (println "done generating one-step" (count used-vars))
                        next-vars (conj used-vars t-var)
                        z3 (push! z3)
                        z3 (if (> (count next-vars) unroll-min)
                             (assert-reached-states! z3 next-vars target-states)
                             z3)
                        [z3 next-vars status path]
                        (if (<= (count next-vars) unroll-min)
                          [z3 next-vars status path]
                          (loop [z3 z3]
                            (let [model (check! z3)]
                              (if (model? model)
                                ; use all path constraints in model (and the reached state assertions) to create a new goal,
                                ; then solve that goal for the time steps. if SAT, that's our witness,
                                ; otherwise it's spurious; prevent that sequence of transitions and check for a model again.
                                ; we don't need to store this counterexample for the next BMC step however.
                                (let [path-steps (map (fn [prev next]
                                                        (ha-moves z3 model prev next))
                                                      (butlast next-vars)
                                                      (rest next-vars))
                                      pcs (path-constraints z3 model next-vars)
                                      checked-model
                                      ;todo: put this in and check it
                                      (if (:check-real-dynamics? z3)
                                        ; double check against the real dynamics to get real timings
                                        ; (should be a purely real-valued program, I think)
                                        (with-solver (assoc z3 :box-approx? false
                                                               :must-semantics? true)
                                                     (fn [z3]
                                                       (assert-valuation! z3 objects "t00")
                                                       (assert-transition-sequence! z3 path-steps next-vars)
                                                       (assert-reached-states! z3 next-vars target-states)
                                                       (check! z3)))
                                        ; else just assume it's good
                                        model)]
                                  (if (model? checked-model)
                                    (let [witness-path (ha/spy "witness path"
                                                               (map (fn [ts edge-state]
                                                                      [(.toString ts)
                                                                       (value z3 model ts)
                                                                       edge-state])
                                                                    (rest next-vars)
                                                                    path-steps))]
                                      (if target-states
                                        [z3 next-vars :witness witness-path]
                                        [z3 next-vars :sat witness-path]))
                                    (do
                                      (assert-all! z3 (into [:not] pcs))
                                      (recur z3))))
                                [z3 next-vars status path]))))
                        z3 (pop! z3)]
                    (if (or (= status :sat) (= status :witness))
                      (reduced [z3 next-vars status path])
                      [z3 next-vars status path])))
                [z3 [] :unsat nil]
                (concat ["t00"] vars)))]
    (println "done bmc")
    [z3 status path]))

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
        c-float-up (+ c-float heval/precision)
        c-float-down (- c-float heval/precision)
        c-denom 1000
        c-int (Math/round ^double (* c-float c-denom))
        c (.mkReal ctx c-int c-denom)
        c-int-up (Math/round ^double (* c-float-up c-denom))
        c-up (.mkReal ctx c-int-up c-denom)
        c-int-down (Math/round ^double (* c-float-down c-denom))
        c-down (.mkReal ctx c-int-down c-denom)]
    (case rel
      :lt
      (.mkLt ctx a-b c)
      :leq
      (.mkLt ctx a-b c-up)
      :gt
      (.mkGt ctx a-b c)
      :geq
      (.mkGt ctx a-b c-down))))

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
                   (.mkTactic ctx "propagate-values")
                   (into-array [(.mkTactic ctx "propagate-ineqs")
                                (.mkTactic ctx "ctx-solver-simplify")]))
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
               lower-bound
               upper-bound
               target-states
               time-steps
               edge-states]
  ;assert flow condition
  (let [last-t (last time-steps)
        new-t (.mkRealConst ctx (str "symx-step-" (count time-steps)))]
    (when (>= upper-bound 0)
      (println "generating flow constraints")
      (assert-all! z3
                   (time (map (fn [[ha-id ha-type]]
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
                                      mid-t (var-name "mid-t" new-t last-t)
                                      vmid-vars (into {}
                                                      (map (fn [v]
                                                             [v (var-name ha-id v "check" last-t)])
                                                           vars))
                                      vT-vars (into {}
                                                    (map (fn [v]
                                                           [v (var-name ha-id v "exit" last-t)])
                                                         vars))]
                                  (flow-constraints z3 ha-id (:bounds ha-def) sdef v0-vars vmid-vars vT-vars last-t mid-t new-t)))
                              has)))
      (println "generated flow constraints"))
    (println "symx" lower-bound upper-bound)
    (let [try-check (cond
                      (< upper-bound 0) [z3 :bound nil]
                      (<= lower-bound 0)
                      (let [z3 (push! z3)
                            _ (println "generating check constraints")
                            z3 (time (assert-reached-states! z3 time-steps target-states))
                            _ (println "generated check constraints")
                            reached-model (check! z3)
                            z3 (pop! z3)]
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
                          :maybe))
                      :else :maybe)]
      (cond
        (and (= try-check :maybe) (> upper-bound 0))
        ;  but note: solver calls are actually pretty cheap... the bigger issue is that we have to unroll pretty far and we end up with way too many choices to make on our frontier.
        (let [try-all-options true
              _ (println "generating options")
              options
              (time (if try-all-options
                      (option-permutations (into {}
                                                 (map (fn [[ha-id ha-type]]
                                                        (let [ha-def (get ha-defs ha-type)
                                                              [_prev-state _tr-edge state] (get (last edge-states) ha-id)
                                                              state-def (get-in ha-def [:states state])
                                                              edges (concat [{:index -1 :target state :guard nil}]
                                                                            (:edges state-def))]
                                                          [ha-id
                                                           (for [{index :index target :target} edges]
                                                             [state index target])]))
                                                      has)))

                      (do
                        (push! z3)
                        ;   assert that some out edge will be taken
                        (println "generating jump constraint")
                        (assert-all! z3
                                     (time (map (fn [[ha-id ha-type]]
                                                  (let [ha-def (get ha-defs ha-type)
                                                        [_prev-state _in-edge state] (get (last edge-states) ha-id)
                                                        state-def (get-in ha-def [:states state])
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
                                                                             vars))
                                                        edges (:edges state-def)]
                                                    (jump-constraints z3 ha-type ha-id state edges vT-vars next-vars last-t new-t)))
                                                has)))
                        (println "generated jump constraint")
                        ;   loop with accumulated options = []
                        ;     find a model (i.e. outgoing edge index) (if no model, yield options)
                        ;     add the model to new-options
                        ;     assert that this edge will not be taken and recurse with new-options
                        (let [options (loop [options []]
                                        (let [model (check! z3)]
                                          (if (model? model)
                                            (let [edge-states (ha-moves z3 model last-t new-t)
                                                  step-constraints (for [[ha-id [prev-state out-edge in-state]] edge-states
                                                                         ;we already have a constraint that prev-state held in last-t.
                                                                         :let [state-c (in-state-c z3 ha-id in-state new-t)
                                                                               _ (assert out-edge (str ha-id ":" prev-state "-" out-edge "->" in-state ":: " last-t "->" new-t))
                                                                               edge-c (picked-out-edge-c z3 ha-id prev-state out-edge last-t)]]
                                                                     [:and state-c edge-c])]
                                              (assert-all! z3 [[:not (into [:and] step-constraints)]])
                                              (recur (conj options (ha/spy "new opt" edge-states))))
                                            options)))]
                          (pop! z3)
                          options))))
              _ (println "generated options")]
          ; loop over each distinct path constraint (or fail if no path constraints)
          (reduce
            (fn [result opt-edges-by-ha-id]
              (push! z3)
              (println "generating jump constraint B")
              ;     assert this path constraint and the jump condition of that constraint (giving us exit variables and enter & state variables for the new thing)
              (time (assert-all! z3 (map (fn [[ha-id ha-type]]
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
                                         has)))
              (println "generated jump constraint B")
              (println "try" opt-edges-by-ha-id)
              (if (model? (check! z3))
                (let [symx-result (symx!- z3
                                          (dec lower-bound)
                                          (dec upper-bound)
                                          target-states
                                          (conj time-steps new-t)
                                          (ha/spy "new path" (conj edge-states opt-edges-by-ha-id)))]
                  (pop! z3)
                  (if (= (second symx-result) :witness)
                    (reduced symx-result)
                    result))
                (do
                  (pop! z3)
                  [z3 :unsat nil])))
            [z3 :unsat nil]
            (shuffle options)))
        (<= upper-bound 0)
        [z3 :bound nil]
        :else
        try-check))))

(defn symx! [z3 ha-vals lower-bound upper-bound target-states]
  (reduce
    (fn [_ iter]
      (let [z3 (assert-valuation! z3 ha-vals "t00")
            result (symx!- z3
                           lower-bound
                           iter
                           target-states
                           ["t00"]
                           [(into {}
                                  (map (fn [ha]
                                         [(:id ha) [:$start -2 (:state ha)]])
                                       (vals ha-vals)))])]
        (if (= (second result) :witness)
          (reduced result)
          result)))
    (range lower-bound upper-bound)))

(defn calc-invariants [z3 ha-defs]
  (ha/map-defs
    (fn [def]
      (assoc def
        :states
        (ha/map-states
          (fn [s]
            (let [req-guards (map :guard (filter ha/required-transition? (:edges s)))]
              (assoc s :invariant
                       ;(simplify-guard z3
                       (ha/negate-guard (into [:or] (map guard-interior req-guards)))
                       ;)
                       )))
          def)))
    ha-defs))

(defn bound-variables [ha-defs]
  (ha/map-defs
    (fn [{init-vars :init-vars
          states    :states :as def}]
      ;todo: calculate bounds for non-velocity variables too. for now just give arbitrary ones?
      (let [all-var-bounds (concat
                             (mapcat (fn [s]
                                       (map (fn [k]
                                              (if (= (namespace k) "v")
                                                (let [f1 (get-in s [:flows k] 0)
                                                      f2 (get-in s [:flows (name k)] 0)
                                                      u (get-in s [:update k] 0)
                                                      us (map #(get-in % [:update k] 0)
                                                              (:edges s))
                                                      f1 (if (vector? f1)
                                                           (second f1)
                                                           f1)]
                                                  [k (apply min u f1 f2 us) (apply max u f1 f2 us)])
                                                [k ha/-Infinity ha/Infinity]))
                                            (keys init-vars)))
                                     (vals states))
                             (map (fn [[k init-v]]
                                    (if (= (namespace k) "v")
                                      [k init-v init-v]
                                      [k ha/-Infinity ha/Infinity]))
                                  init-vars))]
        (assoc def
          :bounds
          (ha/spy "ha-def" (:ha-type def) "var bounds:"
                  (reduce
                    (fn [vs [v l h]]
                      (let [[old-l old-h] (get vs v [0 0])]
                        (assoc vs v [(min old-l l) (max old-h h)])))
                    {}
                    all-var-bounds)))))
    ha-defs))

(defn model-check [ha-defs ha-vals target-states unroll-limit]
  (println "model check with unroll limit" unroll-limit)
  (try
    (let [z3 (->z3 (desugar/set-initial-labels (bound-variables ha-defs))
                   {:must-semantics?     true
                    :stuck-implies-done? false
                    :box-approx?         false
                    :quantifiers?        false})
          z3 (assoc z3 :ha-defs (calc-invariants z3 (:ha-defs z3)))
          z3 (assoc z3
               :has (into {}
                          (map (fn [ha]
                                 [(:id ha) (:ha-type ha)])
                               (vals ha-vals))))
          entry-time (apply max (map :entry-time (vals ha-vals)))
          [ha-vals tr-caches] (heval/init-has ha-defs (vals ha-vals) entry-time)
          config {:objects    ha-vals
                  :entry-time entry-time
                  :tr-caches  tr-caches
                  :inputs     #{}}
          check-may-first? false
          ;todo: the performance on this model checking is nowhere near good enough. If I could get formula generation sped up then maybe it would be worth considering, but even running the solver at a depth of 15 or 16 takes over a second.
          [may-status may-witness] (if check-may-first?
                                     (let [[may-status may-witness]
                                           (time (with-solver
                                                   (assoc z3 :must-semantics? false)
                                                   (fn [z3]
                                                     (rest (bmc! z3 (:objects config) 0 unroll-limit target-states)))))]
                                       (if (= may-status :witness)
                                         [may-status may-witness]
                                         [:unsat nil]))
                                     [:skipped nil])
          start-depth (max 0 (dec (count may-witness)))]
      (if (or (= may-status :skipped)
              (= may-status :witness))
        (ha/spy "checked must"
                (time (with-solver
                        (assoc z3 :must-semantics? true)
                        (fn [z3]
                          (println "check must at" start-depth ".." unroll-limit)
                          (let [[z3 status all-steps] (time (bmc! z3 (:objects config) start-depth unroll-limit target-states))]
                            (println "check result:" status all-steps)
                            (if (= status :witness)
                              (let [moves-per-t (map
                                                  (fn [[tprev tprevval _mprev]
                                                       [tnext tnextval mnext]]
                                                    [[tprev tprevval] [tnext tnextval] mnext])
                                                  (butlast (concat [["t00" 0 nil]]
                                                                   all-steps))
                                                  all-steps)]
                                (fipp/pprint ["rollout" moves-per-t] {:print-level 6})
                                [:witness moves-per-t])
                              [:unsat nil]))))))
        [:unsat nil]))
    (catch Exception e
      (println "Error!")
      (println (.toString e))
      (.printStackTrace e)
      [:error nil])))