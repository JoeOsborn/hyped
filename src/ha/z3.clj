(ns ha.z3
  (:require [clojure.string :as string])
  (:import [com.microsoft.z3 Context Expr Goal RatNum BoolExpr]))

(defn var->const [ctx [id var]]
  (let [idn (name id)
        nom (if (namespace var)
              (str idn "!" (namespace var) "!" (name var))
              (str idn "!" (name var)))]
    (.mkRealConst ctx nom)))

(defn ->z3 [has]
  (let [context (Context.)
        vars (distinct (mapcat (fn [{id :id :as ha}]
                                 (mapcat (fn [var] [[id var] [id (keyword "v" (name var))]]) (:variables ha)))
                               (vals has)))
        consts (map #(var->const context %) vars)
        vars->consts (zipmap vars consts)
        consts->vars (zipmap consts vars)]
    {:context      context
     :vars->consts vars->consts
     :consts->vars consts->vars}))

(defn const->var [z3 const]
  (get (:consts->vars z3) const))

(defn primitive-guard->z3 [{consts :vars->consts
                            ctx    :context}
                           g]
  (let [rel (first g)
        a (get consts (second g))
        b (if (= 3 (count g))
            (.mkReal ctx 0)
            (get consts (nth g 2)))
        a-b (.mkSub ctx (into-array [a b]))
        c (.mkReal ctx (last g))]
    (case rel
      :lt
      (.mkLt ctx a-b c)
      :leq
      (.mkLe ctx a-b c)
      :gt
      (.mkGt ctx a-b c)
      :geq
      (.mkGe ctx a-b c))))

(defn guard->z3- [{ctx :context :as z3} g]
  (case (first g)
    :and (.mkAnd ctx (into-array (map #(guard->z3- z3 %) (rest g))))
    :or (.mkOr ctx (into-array (map #(guard->z3- z3 %) (rest g))))
    (primitive-guard->z3 z3 g)))

(defn guard->z3 [{ctx :context :as z3} g]
  (if (nil? g)
    (.mkTrue ctx)
    (let [guard (guard->z3- z3 g)
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
        :else simplified-guard))))

(defn z3->primitive-guard [z3 rel args]
  (let [a (first args)
        b (if (= 3 (count args))
            (second args)
            nil)
        c (last args)
        _ (println a b c)
        av (const->var z3 a)
        bv (if (and b (.isNumeral b))
             (const->var z3 b)
             nil)
        cv (/ (.getInt64 (.getNumerator c)) (.getInt64 (.getDenominator c)))]
    (if bv
      [rel av bv cv]
      [rel av cv])))

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
  (z3->guard z3 (guard->z3 z3 g)))