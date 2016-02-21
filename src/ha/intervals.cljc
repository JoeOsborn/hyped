(ns ha.intervals)

#?(:clj (def Infinity Double/POSITIVE_INFINITY))
#?(:clj (def -Infinity Double/NEGATIVE_INFINITY))

(defn simple? [i]
  (if-let [[imin imax] i]
    (and (number? imin) (number? imax))
    false))

(defn empty-interval? [i]
  (cond
    (nil? i) true
    (simple? i) (>= (first i) (second i))
    :else (every? empty-interval? i)))

(defn -interval? [i]
  (and (some? i)
       (or (empty-interval? i)
           (simple? i)
           (every? -interval? i))))

(defn interval? [i]
  (or (nil? i)
      (-interval? i)))

(defn width [iv]
  (cond
    (empty-interval? iv) 0
    (simple? iv) (- (second iv) (first iv))
    :else (reduce + 0 (map width iv))))

(defn open? [iv]
  (= Infinity (width iv)))

(declare merge-overlapping)

(defn intersection [a b]
  (cond
    (or (empty-interval? a) (empty-interval? b)) [Infinity Infinity]
    (and (simple? a) (simple? b)) (let [[amin amax] a
                                        [bmin bmax] b]
                                    (cond
                                      (< bmin amin) (intersection b a)
                                      (< amax bmin) nil
                                      :else [(max amin bmin) (min amax bmax)]))
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
                                      [[amin (max amax bmax)] merged]
                                      [[bmin bmax] (conj merged a)]))
                                  [(first intervals) []]
                                  (rest intervals))]
      (cond
        (empty? intervals) [[Infinity Infinity]]
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

(defn intersect-all [intervals]
  (if (simple? intervals)
    intervals
    (reduce (fn [a b]
              (if-let [intr (intersection a b)]
                intr
                (reduced [Infinity Infinity])))
            [0 Infinity]
            intervals)))

(defn union-all [intervals]
  (merge-overlapping intervals))

(defn complement-interval [interval]
  (cond
    ; empty -> infinite
    (empty-interval? interval) [-Infinity Infinity]
    ; infinite -> empty
    (= interval [-Infinity Infinity]) nil
    ; union -> intersection of complements (demorgan's law)
    (not (simple? interval)) (intersect-all (mapv complement-interval interval))
    ; no deferred representation of intersection, so no case for that
    ; open on left --> open on right
    (= (first interval) -Infinity) [(second interval) Infinity]
    ; open on right --> open on left
    (= (second interval) Infinity) [-Infinity (first interval)]
    ; closed on left, right -> open on left U open on right
    :else [[-Infinity (first interval)] [(second interval) Infinity]]))

; I1 - I2 = I1 ^ ~I2
(defn subtract [i1 i2]
  (merge-overlapping (flatten-intervals (intersection i1 (complement-interval i2)))))

; guaranteed to be uniform unless the interval is open on either side.
; in that case, we turn the interval [-Inf b] into [(- b K) b] and [a Inf] into [a (+ a K)] for some large K
(defn rand-t [iv]
  (cond
    (open? iv) (throw "Can't get random time of open interval")
    (empty-interval? iv) (throw "Can't get random time of empty interval")
    ; simple? uniform within range
    (simple? iv) (let [[min max] iv]
                   (+ min (rand (- max min))))
    :else (let [flat (flatten-intervals iv)
                merged (merge-overlapping flat)
                widths (map width merged)
                total-width (reduce + 0 widths)
                weights (map #(/ % total-width) widths)
                pick (rand)]
            (reduce (fn [sum [iv w]]
                      ; this always yields an interval since the weights sum to 1 and pick is <= 1
                      (if (>= (+ sum w) pick)
                        ; iv should be simple, so a uniform random will do fine.
                        ; pick-sum will yield a number between 0 and w.
                        ; we want to divide that by w to get "how far into this interval", then
                        ; multiply that by the width and then add start time to get a number between start and end.
                        (reduced (+ (start-time iv)
                                    (* (width iv) (/ (- pick sum) w))))
                        (+ sum w)))
                    0
                    (zipmap merged weights)))))

(defn interval-contains? [iv t]
  (cond
    (empty-interval? iv) false
    (simple? iv) (<= (first iv) t (second iv))
    :else (some (fn [iv] (interval-contains? iv t)) iv)))