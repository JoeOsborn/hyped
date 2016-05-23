(ns ha.z3
  (:require [clojure.string :as string]
            [ha.ha :as ha]
            [ha.eval :as heval])
  (:import [com.microsoft.z3 Context Expr Goal RatNum
                             BoolExpr RealExpr
                             EnumSort Status
                             Solver ArithExpr Z3Exception]))

(defn trim-leading-colon [s]
  (if (= (nth s 0) \:)
    (subs s 1)
    s))

(defn split-var-name [symb-str]
  (let [components (string/split symb-str "!")
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
  (let [val-denom 1000
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
    (= (.toString c) "epsilon") (/ (min heval/time-unit heval/precision) 1000)
    ; something else
    :else (do (println "something else" (.toString c)) (throw (IllegalArgumentException. (str "Can't make sense of " (.toString c)))))))

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
                             {:sort   sort
                              :consts (zipmap state-ids
                                              (.getConsts sort))}]))]
    (assoc z3 :state-sorts state-sorts
              :ha-defs ha-defs)))

(defn ->z3 [ha-defs]
  (update-ha-defs {:context (Context.)} ha-defs))

(defn with-solver [z3 func]
  (let [z3 (assoc z3 :optimizer (.mkOptimize (:context z3))
                     #_:solver #_(.mkSolver (:context z3)))
        ret (func z3)]
    (when (seq? ret)
      (doall ret))
    ret))

(defn pop! [{s :optimizer cs :solver :as z3}]
  (when s (.Pop s))
  (when cs (.pop cs))
  z3)

(defn push! [{s :optimizer cs :solver :as z3}]
  (when s (.Push s))
  (when cs (.pop cs))
  z3)

(defn check! [{s :optimizer cs :solver}]
  (println "-----CHECK-----\n" (.toString (or s cs)) "\n-----")
  (if s
    (let [status (.Check s)]
      (when (and cs (not= status Status/SATISFIABLE))
        (let [check-status (.check cs)]
          (println "s status" status "cs status" check-status)
          (if (= status Status/UNKNOWN)
            (println "-------unknown----" (.getReasonUnknown cs) "--------")
            (println "-------unsat core" check-status "-------\n" (string/join "\n" (map #(.toString %) (.getUnsatCore cs))) "\n--------------"))))
      (cond
        (= status Status/UNSATISFIABLE) :unsat
        (= status Status/SATISFIABLE) :sat
        (= status Status/UNKNOWN) (do (println "reason:" (.getReasonUnknown s))
                                      :unknown)
        :else (throw (IllegalStateException. (str "Unrecognizable status from solver" status)))))
    (let [status (.check cs)]
      (cond
        (= status Status/UNSATISFIABLE) :unsat
        (= status Status/SATISFIABLE) :sat
        (= status Status/UNKNOWN) (do (println "reason:" (.getReasonUnknown cs))
                                      :unknown)
        :else (throw (IllegalStateException. (str "Unrecognizable status from solver" status)))))))

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
                       (into-array consts)
                       (.mkImplies ctx
                                   (translate-constraint z3 guard)
                                   (translate-constraint z3 body))
                       0
                       nil
                       nil
                       nil
                       nil))
          (:+ :- :* :/)
          (let [[rel & args] c
                z3-args (into-array ArithExpr (map #(translate-constraint z3 %) args))]
            (case rel
              :+ (.mkAdd ctx z3-args)
              :- (.mkSub ctx z3-args)
              :* (.mkMul ctx z3-args)
              :/ (do
                   (assert (= (count z3-args) 2)
                           (str "Can't have more than 2 arguments to divide" (map #(.toString %) z3-args)))
                   (.mkDiv ctx (first z3-args) (second z3-args)))))
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
    (println "assert all" (map #(.toString %) translated))
    (when opt
      (.Add opt
            ^"[Lcom.microsoft.z3.BoolExpr;"
            (into-array BoolExpr translated)))
    (when solv
      (.add solv
            ^"[Lcom.microsoft.z3.BoolExpr;"
            (into-array BoolExpr translated))
      (println "still sat?")
      (println (.check solv))))
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
  (let [dt (var-name ha-id "dt" last-t)
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
                             (let [dflow (get flows flow 0)
                                   flow0 (get v0-vars flow)]
                               (cond
                                 (= dflow 0)
                                 [:eq f1 [:+ f0 [:* flow0 dt]]]
                                 (vector? dflow)
                                 (let [[acc limit] dflow
                                       dv-amt (if (> acc 0)
                                                [:- limit f0]
                                                [:- f0 limit])
                                       dv [:- limit f0]
                                       avg-acc-speed [:/ dv 2]
                                       acc-duration [:/ dv-amt acc]
                                       acc-time [:+ last-t acc-duration]
                                       limit-duration [:- new-t acc-time]
                                       acc-part [:* avg-acc-speed acc-duration]
                                       limit-part [:* limit limit-duration]
                                       flow-rel (if (> acc 0)
                                                  :leq
                                                  :geq)
                                       linearize-splits 4
                                       portion-size (/ 1.0 linearize-splits)
                                       ; make sure 0 and 1 are both in there
                                       splits (sort (set (conj (range 0 1 portion-size) 1)))
                                       portions (map
                                                  (fn [prev next]
                                                    (let [prev-acc-ratio [:* prev acc-duration]
                                                          next-acc-ratio [:* next acc-duration]
                                                          dv-by-prev [:* prev-acc-ratio dv]
                                                          dv-by-next [:* next-acc-ratio dv]
                                                          dt-prev [:* acc-duration prev-acc-ratio]
                                                          dt-next [:* acc-duration next-acc-ratio]
                                                          avg-dv-here [:/ [:+ dv-by-prev dv-by-next] 2]]
                                                      [dt-prev [:* avg-dv-here [:- dt-next dt-prev]]]))
                                                  (butlast splits)
                                                  (rest splits))]
                                   [:eq f1
                                    [:ite [flow-rel [:+ flow0 [:* acc dt]] limit]
                                     ; approximate this by...
                                     #_[:+ [:* acc dt dt] [:* flow0 dt] f0]
                                     (into [:+ [:* flow0 dt] f0]
                                           (map (fn [[dt-prev flow-contrib]]
                                                  [:ite [:geq dt dt-prev]
                                                   flow-contrib
                                                   0])
                                                portions))
                                     [:+ f0 acc-part limit-part]]])))
                             (vector? flow)
                             (let [[acc limit] flow]
                               [:eq
                                f1
                                (if (> acc 0)
                                  [:ite [:leq [:+ f0 [:* acc dt]] limit]
                                   [:+ f0 [:* acc dt]]
                                   limit]
                                  [:ite [:geq [:+ f0 [:* acc dt]] limit]
                                   [:+ f0 [:* acc dt]]
                                   limit])])))]
    (assert (not= new-t last-t))
    (into
      [:and
       [:eq dt [:- new-t last-t]]
       [:gt dt 0]]
      flow-constraints)))

(declare guard->z3)

(defn jump-constraints [{ctx :context :as z3} ha-type ha-id flows edges v0-vars vT-vars next-vars last-t new-t]
  ;todo: later, once collision guards stick around, need to know about colliders
  (let [mid-t (.mkFreshConst ctx "mid-t" (.mkRealSort ctx))
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
       (fn [else {g :guard
                  i :index
                  u :update-dict
                  t :target}]
         ; if guard satisfied
         [:ite (guard->z3 z3 g (var-name "exit" last-t))
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
          else])
       self-jump
       ;reverse to put the highest priority edge on the outermost ITE
       (reverse edges))
     ; if an edge's guard holds at exit it must be >= (no stronger than) the picked edge.
     ; but this is true already by the construction above

     ; for all mid-t between last-t and new-t, there is no case where flow constraints lead to a guard being satisfied.
     [:forall [mid-t]
      [:and [:gt mid-t last-t] [:lt mid-t new-t]]
      [:not
       [:and
        (flow-constraints z3 ha-id flows v0-vars vmid-vars last-t mid-t)
        (into [:or]
              (for [{eg :guard} (filter ha/required-transition? edges)]
                (guard->z3 z3 eg mid-t)))]]]]))

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
                          has    :has :as z3} controlled-ha-id {target :target index :index} new-t]
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

(defn max-value [{ctx :context
                  o   :optimizer
                  s   :solver :as z3} var]
  (push! z3)
  (let [var-const (if (instance? Expr var)
                    var
                    (.mkRealConst ctx var))
        result (if o
                 (let [var-handle (.MkMinimize o var-const)]
                   (assert (= :sat (check! z3)))
                   (rat->float (.getValue var-handle)))
                 (let [opt-const (.mkFreshConst ctx "opt" (.mkRealSort ctx))]
                   (assert-all! z3 [[:not [:exists [opt-const]
                                           [:lt opt-const var-const]
                                           (.substitute (into [:and] (.getAssertions s))
                                                        var-const
                                                        opt-const)]]])))]
    (pop! z3)
    result))

(defn max-value [{ctx :context
                  o   :optimizer
                  s   :solver :as z3} var]
  (push! z3)
  (let [var-const (if (instance? Expr var)
                    var
                    (.mkRealConst ctx var))
        result (if o
                 (let [var-handle (.MkMaximize o var-const)]
                   (assert (= :sat (check! z3)))
                   (rat->float (.getValue var-handle)))
                 (let [opt-const (.mkFreshConst ctx "opt" (.mkRealSort ctx))]
                   (assert-all! z3 [[:not [:exists [opt-const]
                                           [:gt opt-const var-const]
                                           (.substitute (into [:and] (.getAssertions s))
                                                        var-const
                                                        opt-const)]]])))]
    (pop! z3)
    result))

(defn value [{ctx :context o :optimizer s :solver :as z3} var]
  (push! z3)
  (let [var-const (if (instance? Expr var)
                    var
                    (.mkRealConst ctx var))
        _ (assert (= :sat (check! z3)))
        model (.getModel (or o s))
        _ (println "Model" (.toString model) "Vc" (.toString var-const))
        result (.getConstInterp model ^Expr var-const)]
    (pop! z3)
    (if (.isReal result)
      (rat->float result)
      (.toString result))))

(defn path-constraints [{has :has :as z3} time-steps]
  (println "has" has "ts" time-steps)
  (assert has)
  (into [:and]
        (for [[ha-id ha-type] has
              [t idx] (zipmap time-steps (range 0 (count time-steps)))]
          (let [state-var (state-var z3 ha-type ha-id "state" t)
                this-in-state (value z3 state-var)
                exit? (< idx (dec (count time-steps)))
                edge-var (when exit? (var-name ha-id "out-edge" t))
                this-out-edge (when exit? (value z3 edge-var))
                state-constraint [:eq (state-val z3 ha-type this-in-state) state-var]]
            (if exit?
              [:and
               state-constraint
               [:eq this-out-edge edge-var]]
              state-constraint)))))

(defn const->guard-var [const]
  (let [[[_type id third & [last]] index] (split-var-name (.toString const))]
    [(if last
       [(keyword id) (keyword third)]
       [(keyword id) (keyword third last)])
     index]))

(defn guard-var->const [{context :context} [ha-id var] idx]
  (when ha-id
    (var->const context [ha-id var] idx)))

(defn primitive-guard->z3 [{ctx :context :as z3}
                           g
                           idx]
  (assert g)
  (assert (vector? g))
  (let [rel (first g)
        a (if (nth g 1)
            (var->const z3 (nth g 1) idx)
            (.mkReal ctx 0))
        b (if (and (= 4 (count g))
                   (nth g 2))
            (var->const z3 (nth g 2) idx)
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

(defn guard->z3- [{ctx :context has :has :as z3} g idx]
  (case (first g)
    :and (.mkAnd ctx (into-array (map #(guard->z3- z3 % idx) (rest g))))
    :or (.mkOr ctx (into-array (map #(guard->z3- z3 % idx) (rest g))))
    :debug (guard->z3- z3 (second g) idx)
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
    (primitive-guard->z3 z3 g idx)))

(defn guard->z3
  ([z3 g] (guard->z3 z3 g 0))
  ([{ctx :context :as z3} g idx]
    #_(println "guard->z3" g)
   (if (nil? g)
     (.mkTrue ctx)
     (let [guard (guard->z3- z3 g idx)
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