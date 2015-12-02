(ns player.intervals)

(defn simple? [i]
  (if-let [[imin imax] i]
    (and (number? imin) (number? imax))
    false))

(defn empty-interval? [i]
  (if (simple? i)
    (>= (first i) (second i))
    (every? empty-interval? i)))

(declare merge-overlapping)

(defn intersection [a b]
  (cond
    (or (empty-interval? a) (empty-interval? b)) [Infinity Infinity]
    (and (simple? a) (simple? b)) (let [[amin amax] a
                                        [bmin bmax] b]
                                    (cond
                                      (< bmin amin) (intersection b a)
                                      (< amax bmin) nil
                                      :else [(.max js/Math amin bmin) (.min js/Math amax bmax)]))
    ; b (resp. a) is a disjunction of simple intervals; intersect each with a (resp. b)
    (simple? a) (merge-overlapping (mapv #(intersection a %) b))
    (simple? b) (merge-overlapping (mapv #(intersection b %) a))
    ; both are disjunctions of simple intervals. union of intersections
    ; (a1 u a2 u a3) ^ (b1 u b2 u b3) == (a1 ^ b1 u a1 ^ b2 u a1 ^ b3) u ...
    :else (merge-overlapping (vec
                               ; union of unions of pairwise intersections
                               (mapcat (fn [ai]
                                         ; union of pairwise intersections
                                         (mapv (fn [bi]
                                                 (intersection ai bi))
                                               b))
                                       a)))))

(defn compare-intervals [a b]
  (cond
    (and (simple? a) (simple? b)) (compare (first a) (first b))
    (simple? a) (compare (first a) (ffirst b))
    (simple? b) (compare (ffirst a) (first b))
    :else (compare (ffirst a) (ffirst b))))

(defn sort-intervals [intervals]
  (if (simple? intervals)
    intervals
    (sort compare-intervals intervals)))

(defn flatten-intervals [intervals]
  (if (simple? intervals)
    intervals
    (reduce (fn [sofar interval]
              (if (simple? interval)
                (conj sofar interval)
                (into sofar (flatten-intervals interval))))
            []
            intervals)))

(defn merge-overlapping [intervals]
  (if (simple? intervals)
    intervals
    (let [intervals (flatten-intervals intervals)
          intervals (filter #(not (empty-interval? %)) intervals)
          intervals (sort-intervals intervals)
          [last-i merged] (reduce (fn [[[amin amax :as a] merged] [bmin bmax :as b]]
                                    (if (intersection a b)
                                      [[amin (.max js/Math amax bmax)] merged]
                                      [[bmin bmax] (conj merged a)]))
                                  [(first intervals) []]
                                  (rest intervals))]
      (cond
        (empty? intervals) []
        (empty-interval? last-i) merged
        :else (conj merged last-i)))))

(defn first-subinterval [i]
  (if (simple? i)
    i
    (first (merge-overlapping (flatten-intervals i)))))

(defn start-time [i]
  (first (first-subinterval i)))

(defn map-simple-intervals [func intvl]
  (merge-overlapping (if (simple? intvl)
                       (func (first intvl) (second intvl))
                       (mapv (fn [intvl-i]
                               (map-simple-intervals func intvl-i))
                             intvl))))