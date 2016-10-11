(ns ha.hl-to-js
  (:require [clojure.string :as string])
  (:use ha.hl-utils))

(declare jsify-value)
(defn rel-expr [opts rel rel-js args]
  (if (= 2 (count args))
    (str "("
         (jsify-value opts (first args))
         " " rel-js " "
         (jsify-value opts (second args))
         ")")
    (jsify-value opts
                 (into [:and]
                       (map
                        (fn [a b]
                          [:= a b])
                        (butlast args)
                        (rest args))))))

(defn jsify-value [opts val]
  (cond
    (boolean? val) (str val)
    (nil? val)     "null"
    (keyword? val) (cond
                     ;;todo: have to handle this for real later, this forces all the guard functions to call the variable :ha.
                     (contains? (:special-names opts) val)
                     (sanitize-var (str (name val) "_" (:suffix opts)))
                     (= ::self val) (sanitize-var :ha)
                     :else          (sanitize-var (name val)))
    (number? val)  (str val)
    (string? val)  (str "\"" val "\"")
    (map? val)     (str "{" (string/join ", " (for [[k v] val]
                                                (str (jsify-value opts k) ": "
                                                     (jsify-value opts v)))) "}")
    :else
    (case (first val)
      :contains ;;gotta pass an expression returning a string!
      (let [[d k] (rest val)]
        (str "(" (jsify-value opts k) " in " (jsify-value opts d) ")"))
      :contains-key ;;gotta pass a key!
      (let [[d k] (rest val)]
        (str "('" (jsify-value opts k) "' in " (jsify-value opts d) ")"))
      :and
      (str "("
           (string/join " && " (map #(jsify-value opts %)
                                    (rest val)))
           ")")
      :or
      (str "("
           (string/join " || " (map #(jsify-value opts %)
                                    (rest val)))
           ")")
      :not
      (str "!" (jsify-value opts (second val)))
      (:+ :- :/ :*)
      (str "(" (string/join (name (first val))
                            (map #(jsify-value opts %)
                                 (rest val)))
           ")")
      :**
      (str "Math.pow("
           (jsify-value opts (second val)) ", "
           (jsify-value opts (last val))
           ")")
      :=
      (rel-expr opts (first val) " == " (rest val))
      (:< :<= :>= :>)
      (rel-expr opts (first val) (name (first val)) (rest val))
      (:dict :string :number ::basic ::var ::constant)
      (jsify-value opts (second val))
      :list
      (str "[" (string/join "," (map #(jsify-value opts %) (second val))) "]")
      :deref   (do
                 (assert (every? some? (rest val)))
                 (string/join "."
                             (map #(jsify-value opts %)
                                  (rest val))))
      :lookup  (str (jsify-value opts (nth val 1))
                    "["
                    (jsify-value opts (nth val 2))
                    "]")
      ::lookup (jsify-value opts [:deref
                                  ;;todo: have to handle ::self specially.
                                  (::ref (second val))
                                  (::var (second val))])
      :call    (str (if (keyword? (nth val 1))
                      (jsify-value opts (nth val 1))
                      (str "(" (jsify-value opts (nth val 1)) ")"))
                    "("
                    (string/join ","
                                 (map #(jsify-value opts %)
                                      (nth val 2)))
                    ")")
      (do (println "Weird value " val)
          (assert false)))))

(defn indent->spaces [opts]
  (string/join (repeat (* 2 (get opts :indent 0)) " ")))

(defn jsify-statement [opts [vk & vrest :as v]]
  (let [indent (:indent opts)
        spaces (indent->spaces opts)]
    (case vk
      :block
      (string/join "\n"
                   (map #(jsify-statement opts %) vrest))
      :case
      (let [[value & checks] vrest
            inner-opts       (update opts :indent inc)
            more-spaces      (indent->spaces inner-opts)]
        (str spaces
             "switch(" (jsify-value opts value) ") {\n"
             (string/join "\n"
                          (map
                           (fn [[check body]]
                             (str more-spaces "case " (jsify-value opts check) ":\n"
                                  (jsify-statement inner-opts
                                                   [:block body [:break]])))
                           checks))
             "\n"
             spaces "}"))
      :def
      (str spaces "var " (sanitize-var (first vrest)) " = " (jsify-value opts (second vrest)) ";")
      :assign
      (str spaces (jsify-value opts (first vrest)) " = " (jsify-value opts (second vrest)) ";")
      :if
      (str spaces
           "if(" (jsify-value opts (first vrest)) ") {\n"
           (jsify-statement (update opts :indent inc) (second vrest)) "\n"
           spaces "}"
           (if (= 3 (count vrest))
             (str " else {\n"
                  (jsify-statement (update opts :indent inc) (last vrest)) "\n"
                  spaces "}")
             ""))
      :breakable-block
      (str spaces "for(var _bk_" indent " = true; _bk_" indent "; _bk_" indent " = false) {\n"
           (jsify-statement (update opts :indent inc) vrest) "\n"
           spaces "}")
      :break
      (str spaces "break;")
      :return
      (str spaces "return (" (if (empty? vrest)
                             ""
                             (jsify-value opts (first vrest))) ");")
      ;;...?
      (cond
        (keyword? vk)    ;;implicit expr
        (str spaces (jsify-value opts v) ";")
        (sequential? vk) ;;implicit block
        (jsify-statement opts (into [:block] v))
        (nil? vk)        "" ;;implicit empty block
        :else            (do (println "weird value"
                                      vk v)
                             (assert false))))))

(defn jsify-root [opts hlcode]
  (let [opts (merge {:indent 0} opts)]
    (string/join
     "\n\n"
     (for [[nom df] hlcode
           :let     [nomjs (str (sanitize-var nom) "_" (:suffix opts))
                     spaces (indent->spaces opts)]]
       (if (= :defn (first df))
         (let [[args & body] (rest df)]
           (str
            spaces "function " nomjs "(" (string/join "," (map sanitize-var args)) ") {\n"
            (string/join "\n"
                         (map #(jsify-statement (update opts :indent inc) %)
                              body)) "\n"
            spaces "}"))
         (jsify-statement opts [:def nom df]))))))
