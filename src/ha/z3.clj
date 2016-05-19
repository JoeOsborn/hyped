(ns ha.z3
  (:require [clojure.string :as string]
            [ha.ha :as ha])
  (:import [com.microsoft.z3 Context Expr Goal RatNum
                             BoolExpr EnumSort Status
                             Solver]))

(defn split-var-name [symb-str]
  (let [components (string/split symb-str "!")
        index (Integer/parseInt (last components))]
    [(butlast components) index]))

(defn var-name [& chunks]
  (string/join (map name chunks) "!"))

(defn var->const [ctx [type id var] idx]
  (let [nom (if (namespace var)
              (var-name type id (namespace var) (name var) idx)
              (var-name type id var idx))]
    (.mkRealConst ctx nom)))

(defn float->real [z3 val]
  (let [val-denom 1000
        val-int (Math/round ^double (* val val-denom))]
    (.mkReal z3 val-int val-denom)))

(defn rat->float [c]
  (/ (.getInt64 (.getNumerator c))
     (.getInt64 (.getDenominator c))))

(defn ->z3 [ha-defs]
  (let [context (Context.)
        state-sorts (into {}
                          (for [{states  :states
                                 ha-type :ha-type} ha-defs
                                :let [sort-name (var-name ha-type "state")
                                      state-ids (map (fn [s]
                                                       (name (.id s)))
                                                     states)
                                      sort (.mkEnumSort context
                                                        ^String sort-name
                                                        ^"[Ljava.lang.String;" (into-array state-ids))]]
                            [sort-name
                             {:sort   sort
                              :consts (zipmap state-ids
                                              (.getConsts sort))}]))]
    {:context     context
     :state-sorts state-sorts}))

(defn with-solver [z3 func]
  (let [z3 (assoc z3 :solver (.mkOptimize (:context z3)))
        ret (func z3)]
    (when (seq? ret)
      (doall ret))
    ret))

(defn pop! [{s :solver}]
  (.pop s))

(defn push! [{s :solver}]
  (.push s))

(defn check! [{s :solver}]
  (case (.check s)
    Status/UNSATISFIABLE :unsat
    Status/SATISFIABLE :sat
    Status/UNKNOWN :unknown))

(defn translate-constraints [{state-sorts :state-sorts :as ctx}
                             constraints]
  (for [c constraints]
    (case (first c)
      :ite
      (.mkITE ctx
              (translate-constraints ctx (nth c 1))
              (translate-constraints ctx (nth c 2))
              (translate-constraints ctx (nth c 3)))
      :and
      (.mkAnd ctx (into-array
                    (map #(translate-constraints ctx %)
                         (rest c))))
      :or
      (.mkOr ctx (into-array
                   (map #(translate-constraints ctx %)
                        (rest c))))
      :not
      (.mkNot ctx (translate-constraints ctx (second c)))
      (:geq :leq :lt :gt :eq)
      (let [[n1 n2] (map #(translate-constraints ctx %)
                         (rest c))]
        (case (first c)
          :gt (.mkGt ctx n1 n2)
          :geq (.mkGe ctx n1 n2)
          :eq (.mkEq ctx n1 n2)
          :leq (.mkLe ctx n1 n2)
          :lt (.mkLt ctx n1 n2)))
      :state-val
      (let [[ha-type state] (rest c)]
        (get-in state-sorts [(var-name ha-type "state") :consts state]))
      :state-var
      (let [[ha-type & rest] (rest c)
            sort (get-in state-sorts [(var-name ha-type "state") :sort])]
        (.mkConst ctx
                  (apply var-name ha-type rest)
                  (:sort sort)))
      :t
      (.mkRealConst ctx (apply var-name "t" (rest c)))
      ;else
      (cond
        (number? c) (float->real ctx c)
        (or (keyword? c)
            (string? c)) (.mkConst ctx (name c))
        :else (throw (str "Can't convert " c))))))

(defn assert-all! [{context :context
                    solver  :solver} constraints]
  (.add solver (translate-constraints context constraints)))

(defn assert-valuation! [{ha-defs :ha-defs :as z3}
                         ha-vals
                         t-var]
  (let [constraints (for [{this-et    :entry-time
                           this-state :state
                           this-v0    :v0
                           this-id    :id
                           :as        this-ha}
                          (vals ha-vals)
                          :let [this-def (get ha-defs (.id this-ha))]]
                      (conj
                        (for [[v k] this-v0]
                          [:eq
                           [this-def this-id v "enter" t-var]
                           k])
                        [:eq
                         [this-def this-id "time" t-var]
                         this-et]
                        [:eq
                         [:state-var this-def this-id "state" t-var]
                         [:state-val this-def this-state]]))]
    (assert-all! z3 constraints)
    (assoc z3 :last-t t-var
              :has (map (fn [ha] [(:ha-type ha) (:id ha)]) ha-vals))))


#_(defn assert-valuation! [{z3          :context
                            state-sorts :state-sorts
                            ha-defs     :ha-defs
                            ha-vals     :ha-vals :as z3-ctx}]
    :ok
    ;todo: have to actually assert in a solver these 'mkeqs' and mkconsts and so on!
    ; todo: this stuff just creates ASTs and hten I have to _do_ something with them!
    #_(doseq [{e-t  :entry-time
               type :ha-type
               id   :id
               v0   :v0 :as ha-val} ha-vals
              :let [ha-def (get ha-defs type)
                    state (ha/current-state ha-def ha-val)
                    time-var (.mkRealConst z3 (str (name type) "!"
                                                   (name id) "!"
                                                   "t" "!"
                                                   "0"))
                    state-var (.mkConst z3
                                        (get state-sorts (.id state))
                                        (str (name type) "!" (name id) "!" "state!" 0))]]
        (.mkEq z3 time-var (float->real z3 e-t))
        (.mkEq z3 state-var (name (.id state)))
        (doseq [[var val] v0
                :let [z3-var (.mkRealConst z3 (str (name type) "!"
                                                   (name id) "!"
                                                   (if (namespace var)
                                                     (str (namespace var) "!" (name var))
                                                     (name var)) "!"
                                                   "0"))
                      val-real (float->real z3 val)]]
          (.mkEq z3 z3-var val-real))
        ;todo: a z3variable for "how long spent in this transition" and z3variables for the values of each ha variable defined in terms of that time z3variable?
        ;todo: do all the consts defined above have to be made available somehow/stored in a dict? probably!!
        ;todo: should the upcoming transition times be calculated here and stored in consts? probably!!
        ;todo: generalize this to support an arbitrary evaluation, and support an index i, and support merging in update dicts. the above is most of the way to a reduction!
        )
    z3-ctx)

(defn assert-flow-jump! [{ctx     :context
                          has     :has
                          ha-defs :ha-defs
                          last-t  :last-t :as z3}
                         controlled-ha-id
                         controlled-src-state
                         {target      :target
                          guard       :guard
                          index       :index
                          update-dict :update-dict :as controlled-edge}
                         new-t
                         zeno-limit]
  (let [final-t
        (loop [zeno-limit zeno-limit
               last-t last-t]
          (let [next-t (.mkFreshConst ctx "t" (.mkRealSort ctx))
                dt [:- next-t last-t]]
            ;todo: definitely iterate outside of here (in sym-x) to be sure we aren't stymied in search by transition heavy systems
            ;todo: consider ignoring t0 and the optional transition, rephrasing those as constraints on valuations (but then what's the return value of sym-x? distinct subregions of those initial constraints? a set of constraints for each locally reached state?)
            ;todo: rephrase as "do the first flow-jump(s) available, iterating until a zeno bound is reached or ha-id transitions along required edge"
            ;      rephrase flows as per-variable, per-state functions of v0 and t, avoiding need for end-of-flow symbols?
            ; assert that all required-edge HAs flow appropriately from the last time-var to this time-var at the previous time point's flow rates, i.e. introduce new "end of flow" variables defined in terms of last-t
            (doseq [[ha-type ha-id] has
                    :let [def (get ha-defs ha-type)
                          vars (map first (:variables def))
                          ha-s (var-name ha-type ha-id "state" last-t)
                          flow-constraint-sets (for [[sid sdef] (:states def)
                                                     :when (or (not= ha-id controlled-ha-id)
                                                               (= sid controlled-src-state))
                                                     :let [flows (:flows sdef)]]
                                                 (map (fn [v]
                                                        (let [f0 (var-name ha-type ha-id v "enter" last-t)
                                                              f1 (var-name ha-type ha-id v "exit" last-t)
                                                              flow (get flows v 0)]
                                                          (cond
                                                            (= flow 0) [[:eq f1 f0]]
                                                            (number? flow) [[:eq f1 [:+
                                                                                     f0
                                                                                     [:*
                                                                                      flow
                                                                                      dt]]]]
                                                            (keyword? flow)
                                                            (let [dflow (get flows flow 0)
                                                                  flow0 (var-name ha-type ha-id flow "enter" last-t)]
                                                              (cond
                                                                (= dflow 0)
                                                                [[:eq f1 [:+
                                                                          f0
                                                                          [:*
                                                                           flow0
                                                                           dt]]]]
                                                                (vector? dflow)
                                                                (let [[acc limit] dflow]
                                                                  [[:eq
                                                                    f1
                                                                    (if (> acc 0)
                                                                      [:ite [:leq [:+ flow0 [:* acc dt]] limit]
                                                                       [:+
                                                                        [:* acc dt dt]
                                                                        [:* flow0 dt]
                                                                        f0]
                                                                       ; linear from start at avg speed
                                                                       ; avg: quadratic part is avg (max-min)/2
                                                                       ;      linear part is linear.
                                                                       ;      what's the length of the quadratic part?
                                                                       ;todo:
                                                                       0]
                                                                      [:ite [:geq [:+ flow0 [:* acc dt]] limit]
                                                                       [:+
                                                                        [:* acc dt dt]
                                                                        [:* flow0 dt]
                                                                        f0]
                                                                       ;todo:
                                                                       0])]])))
                                                            (vector? flow)
                                                            (let [[acc limit] flow]
                                                              [[:eq
                                                                f1
                                                                (if (> acc 0)
                                                                  [:ite [:leq [:+ f0 [:* acc dt]] limit]
                                                                   [:+ f0 [:* acc dt]]
                                                                   limit]
                                                                  [:ite [:geq [:+ f0 [:* acc dt]] limit]
                                                                   [:+ f0 [:* acc dt]]
                                                                   limit])]]))))
                                                      vars))]]
              (assert-all! z3 (reduce (fn [so-far [s cs]]
                                        [:ite [:eq ha-s s]
                                         cs
                                         so-far])
                                      [:false]
                                      flow-constraint-sets))
              ))

          ;;whoa whoa whoa. let's start over. let's just analyze one-ha systems and later reduce multi-ha systems to that.
          ;; let's produce a formula that does bounded model checking up to a certain length, assuming the desired given transition happens first. we'll also store at each step which transition index was used, so we can recover edges from the resulting witnesses. if we do this bounded model checking and get models, those models will have certain transitions on their fringe. what we have to do is get a model, assert some fringe transition isn't taken, see if there's another model, ... etc. alternately, get a minimum (and/or maximum?) t0 value, find out which transitions it's taking, assert that that particular combination of transitions is disallowed, get a new minimum (maximum?) t0 value, etc. will that work?
          ;; actually, "find a transition sequence (check-sat), then push/assert that transition sequence is definitely the one/minimize-or-maximize-t0/pop/assert that transition sequence is definitely not the one, check-sat, repeat"

          ; either the required edge happened here, or it didn't and we transition the system naturally. in either case we recur with a lower zeno bound. [:xor (happened-here) (happens-next)]. this turns the zeno resolution into something in SMT land rather than something push/pop-y, but maybe we should stick with push/pop-y. In that case, either assert that the required edge's guard is satisfied or that it's not satisfied. the "no other ha transitions before" thing handles "wasn't ever satisfied". UNFORTUNATELY, if we have multiple possibilities with a push/pop-y regime, we need to propagate those backwards into worlds! and if we do it all SMT-y, we need a better way to get the splits than min-value/max-value. maybe assumptions? but then I can't get min/max bounds...
          ; so if we want to do it in a push/pop way we need to change the API to have a continuation, "I did the flow-jump and now you can continue, and when you're done I'm gonna pop and explore the next option."
          ;; if we want to do it in a SMT way, we need to do something else to get the different t0 values that trigger different explanations in the OR stuff. I think I must track the choice-formulae, and then do the "get a minimal value assuming only one at a time is true" dance. but that's not quite right, since some choice formulae might depend on others. more like, for each xor I create, assert only one of their members is true, but this yields tons and tons of possibilities.......
          ;; the push-pop way with continuations seems good. otherwise, do the "roll out <limit> steps, and assert that the desired transition happened at step 1 // happened at step 2 // happened at step 3 // etc," but this isn't quite right because we also need to make assertions about which other required transitions fired so we can split t0 properly. so let's do the push/pop way for now, rolling out until M steps after the required transition happens or N steps without the required transition happening, and the continuation will just do the check, minvalue, maxvalue dance.
          ; if the required edge happened here:
          ; for the required edge:
          ;  assert that the transition guard holds over the end-of-flow variables, that no higher priority required transition of this HA has a satisfied guard at new-t
          ;  assert that no required transition, including this one, of this HA could have fired earlier. one way is to see if there is to create another t variable and assert last-t < t < new-t and (required transition 1 holds OR required transition 2 holds OR ... in terms of fresh end-of-flow variables for t) using check(...) or push/pop and hope it's unsatisfiable. but I think it's easier and better to use a quantifier?
          ; assert that no required transition of any other HA could have fired earlier. one way is to see if there is to create another t variable and assert last-t < t < new-t and (required transition 1 holds OR required transition 2 holds OR ... in terms of fresh end-of-flow variables for t) using check(...) or push/pop and hope it's unsatisfiable. but I think it's easier and better to use a quantifier.
          ; ; (could I use just one type of formula for both the required-transitioning and other HAs?)
          ; ;  nb: In the future, since z3 holds last-t, I could let other HAs make transitions before these ones by recursively calling assert-flow-jump! with made-up time-points in between last-t and new-t.
          ; if the required edge did not happen here, do a flow and any required transitions which can be made true can trigger jumps, provided no other required transitions of other HAs happened before those required transitions become true. so for each required transition of each HA, push, assert that it's true, if it is call the continuation and then pop. or something...
          ; to do a jump, assert that every HA experiences a discrete (possibly self) transition at time-var, i.e. introduce new "enter" variables defined in terms of "end of flow" variables or update dict entries. also update state and entry-time IF. more or less like 'assert-valuation' but for z3 land.
          ; ; The required transitioning HAs have a fixed guard that must be true.
          ; ; The not-required transitioning HAs _may_ have a true required transition guard, in which case we need a formula like
          ; ;   "(ite req-transition-1-guard-valid: new-state-is-this, new-entry-is-this, new-v0-is-this-post-update
          ; ;     ite req-transition-2-guard-valid: ...
          ; ;     else new-state-is-old-state, new-entry-is-old-entry, new-v0-is-old-v0)"
          ; ; We already know they didn't have any earlier true required guards.
          ; ; We could write the code for the "HAs that must transition" in terms of the "HAs that _may_ transition" without any changes, at the cost of a slightly larger formula?
          )]
    (assert-all! z3 [[:eq final-t new-t]])
    (assoc z3 :last-t final-t)))

(defn min-value [{ctx :context
                  s   :solver} var]
  (.push s)
  (let [var-const (.mkRealConst ctx var)
        var-handle (.MkMinimize s var-const)
        _ (assert (= :sat (.check s)))
        result (rat->float (.getValue var-handle))]
    (.pop s)
    result))

(defn max-value [{ctx :context
                  s   :solver} var]
  (.push s)
  (let [var-const (.mkRealConst ctx var)
        var-handle (.MkMaximize s var-const)
        _ (assert (= :sat (.check s)))
        result (rat->float (.getValue var-handle))]
    (.pop s)
    result))

(defn const->guard-var [const]
  (let [[[_type id third & [last]] index] (split-var-name (.toString const))]
    [(if last
       [(keyword id) (keyword third)]
       [(keyword id) (keyword third last)])
     index]))

(defn guard-var->const [{context :context
                         ha-vals :ha-vals} [ha-id var] idx]
  (when ha-id
    (let [haval-a (get ha-vals ha-id)
          hatype-a (:ha-type haval-a)]
      (var->const context [hatype-a ha-id var] idx))))

(defn primitive-guard->z3 [{ctx :context :as z3}
                           g
                           idx]
  (assert g)
  (assert (vector? g))
  (let [rel (first g)
        a (guard-var->const z3 (nth g 1) idx)
        b (if (= 3 (count g))
            (.mkReal ctx 0)
            (guard-var->const z3 (nth g 2) idx))
        a-b (.mkSub ctx (into-array [a b]))
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

(defn guard->z3- [{ctx :context :as z3} g idx]
  (case (first g)
    :and (.mkAnd ctx (into-array (map #(guard->z3- z3 % idx) (rest g))))
    :or (.mkOr ctx (into-array (map #(guard->z3- z3 % idx) (rest g))))
    :debug (guard->z3- z3 (second g) idx)
    (primitive-guard->z3 z3 g idx)))

;todo: handle in-state, not-in-state
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
      [rel av cv])))

;todo: handle in-state, not-in-state
(defn z3->guard [z3 g]
  (cond
    (.isFalse g) (throw "Can't represent contradiction as guard")
    (.isTrue g) nil
    (.isAnd g) (apply vector :and (map #(z3->guard z3 %) (.getArgs g)))
    (.isOr g) (apply vector :or (map #(z3->guard z3 %) (.getArgs g)))
    (.isNot g) (let [inner ^Expr (aget (.getArgs g) 0)
                     neg-rel (cond
                               (.isLE inner) :gt
                               (.isGE inner) :lt
                               :else (throw "Unrecognized simplified guard"))]
                 (z3->primitive-guard z3 neg-rel (.getArgs inner)))
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