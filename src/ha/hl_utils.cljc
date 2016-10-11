(ns ha.hl-utils
  (:require [clojure.string :as string]))

(defn degree [vbl]
  (let [vn (name vbl)]
    (cond
      (.endsWith vn "'''") 3
      (.endsWith vn "''")  2
      (.endsWith vn "'")   1
      :else                0)))

(defn sort-primes-descending [vbls]
  (reverse (sort-by degree vbls)))

(defn prime [vbl]
  (if (= (degree vbl) 3)
    nil
    (keyword (str (name vbl) "'"))))

(defn higher-primes [vbl]
  (if (= (degree vbl) 3)
    []
    (conj (higher-primes (prime vbl)) (prime vbl))))

(defn sanitize-var [k]
  (let [n (-> (name k)
              (string/replace #"-" "_"))
        n (case (degree k)
            0 n
            1 (str "v" n)
            2 (str "a" n)
            3 (str "da" n))]
    (string/replace n #"\'" "")))

