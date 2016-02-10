(ns ha.z3
  (:require [clojure.string :as string])
  (:import [com.microsoft.z3 Context Expr Goal RatNum BoolExpr]))

(def ctx (Context.))

(defn var->const [[id var]]
  (let [idn (name id)
        nom (if (namespace var)
              (str idn "!" (namespace var) "!" (name var))
              (str idn "!" (name var)))]
    (.mkRealConst ctx nom)))

(defn const->var [const]
  (let [cstr (.toString (.getName (.getFuncDecl const)))
        [id name-or-space maybe-name] (string/split cstr #"\!")]
    [(keyword id) (if maybe-name
                    (keyword name-or-space maybe-name)
                    (keyword maybe-name))]))

(defn vars->consts [so-far g]
  (case (first g)
    (:and :or) (reduce vars->consts
                       so-far
                       (rest g))
    (let [a (second g)
          so-far (if (contains? so-far a)
                   so-far
                   (assoc so-far a (var->const a)))
          b (if (= 3 (count g))
              nil
              (nth g 2))
          so-far (if (or (nil? b)
                         (contains? so-far b))
                   so-far
                   (assoc so-far b (var->const b)))]
      so-far)))

(defn primitive-guard->z3 [g consts]
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

(defn guard->z3- [g consts]
  (case (first g)
    :and (.mkAnd ctx (into-array (map #(guard->z3- % consts) (rest g))))
    :or (.mkOr ctx (into-array (map #(guard->z3- % consts) (rest g))))
    (primitive-guard->z3 g consts)))

(defn guard->z3 [g]
  (if (nil? g)
    (.mkTrue ctx)
    (let [guard (guard->z3- g (vars->consts {} g))
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

(defn z3->primitive-guard [rel args]
  (let [a (first args)
        b (if (= 3 (count args))
            (second args)
            nil)
        c (last args)
        _ (println a b c)
        av (const->var a)
        bv (if (and b (.isNumeral b))
             (const->var b)
             nil)
        cv (/ (.getInt64 (.getNumerator c)) (.getInt64 (.getDenominator c)))]
    (if bv
      [rel av bv cv]
      [rel av cv])))

(defn z3->guard [g]
  (cond
    (.isFalse g) (throw "Can't represent contradiction as guard")
    (.isTrue g) nil
    (.isAnd g) (apply vector :and (map z3->guard (.getArgs g)))
    (.isOr g) (apply vector :or (map z3->guard (.getArgs g)))
    (.isNot g) (let [inner ^Expr (aget (.getArgs g) 0)
                     neg-rel (cond
                               (.isLE inner) :gt
                               (.isGE inner) :lt
                               :else (throw "Unrecognized simplified guard"))]
                 (z3->primitive-guard neg-rel (.getArgs inner)))
    (.isLT g) (z3->primitive-guard :lt (.getArgs g))
    (.isLE g) (z3->primitive-guard :leq (.getArgs g))
    (.isGT g) (z3->primitive-guard :gt (.getArgs g))
    (.isGE g) (z3->primitive-guard :geq (.getArgs g))))
