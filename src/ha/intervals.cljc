(ns ha.intervals)

#?(:clj (def Infinity Double/POSITIVE_INFINITY))
#?(:clj (def -Infinity Double/NEGATIVE_INFINITY))

(defrecord SimpleInterval [^Number start ^Number end])

(defn interval [start end]
  (if (>= start end)
    nil
    (SimpleInterval. start end)))

(defn ^Boolean simple? [i]
  ;(assert (not (and (vector? i) (= (count i) 2) (number? (first i)) (number? (second i)))))
  (or (nil? i)
      (instance? SimpleInterval i)))

(defn ^Boolean empty-interval? [i]
  (cond
    (nil? i) true
    (simple? i) (>= (.-start i) (.-end i))
    (empty? i) true
    :else (every? empty-interval? i)))

(defn ^Boolean nonempty-interval? [i]
  (not (empty-interval? i)))

(defn ^Boolean interval? [i]
  (or (empty-interval? i)
      (simple? i)
      (every? simple? i)))

(defn width [iv]
  (cond
    (empty-interval? iv) 0
    (simple? iv) (- (.-end iv) (.-start iv))
    :else (reduce + (map width iv))))

(defn ^Boolean open? [iv]
  (= Infinity (width iv)))

(defn first-subinterval [i]
  (if (simple? i)
    i
    (first i)))

(defn last-subinterval [i]
  (if (simple? i)
    i
    (last i)))

(defn start [i]
  (.-start (first-subinterval i)))

(defn end [i]
  (.-end (last-subinterval i)))

(defn start-end [i]
  (if (empty-interval? i)
    [Infinity Infinity]
    [(start i) (end i)]))

(declare union)

(defn intersection [a b]
  (cond
    (or (empty-interval? a) (empty-interval? b)) nil
    (and (simple? a) (simple? b)) (let [amin (.-start a)
                                        amax (.-end a)
                                        bmin (.-start b)
                                        bmax (.-end b)]
                                    (cond
                                      (<= amin bmin bmax amax) b
                                      (<= bmin amin amax bmax) a
                                      (< bmax amin) nil
                                      (< amax bmin) nil
                                      :else (interval (max amin bmin) (min amax bmax))))
    :else
    (let [result (cond
                   ; b (resp. a) is a disjunction of simple intervals; intersect each with a (resp. b)
                   ; every subinterval only gets smaller, so there's no need to merge anything ever
                   (simple? a) (reduce (fn [b bi] (let [i (intersection a bi)]
                                                    (if (empty-interval? i)
                                                      b
                                                      (conj b i))))
                                       []
                                       b)
                   (simple? b) (reduce (fn [a ai] (let [i (intersection b ai)]
                                                    (if (empty-interval? i)
                                                      a
                                                      (conj a i))))
                                       []
                                       a)
                   ; both are disjunctions of simple intervals. union of intersections
                   ; (a1 u a2 u a3) ^ (b1 u b2 u b3) == (a1 ^ b1 u a1 ^ b2 u a1 ^ b3) u ...
                   :else (reduce union (mapcat (fn [ai]
                                                 ; union of pairwise intersections
                                                 (map (fn [bi]
                                                        (intersection ai bi))
                                                      b))
                                               a)))]
      (if (empty-interval? result)
        nil
        result))))

(defn compare-intervals [a b]
  (cond
    (and (empty-interval? a) (empty-interval? b)) 0
    (empty-interval? a) 1
    (empty-interval? b) -1
    :else (compare (start a) (start b))))

(defn union [i1 i2]
  (cond
    (empty-interval? i1) i2
    (empty-interval? i2) i1
    (= i1 i2) i1
    ; union one one
    (and (simple? i1) (simple? i2))
    (let [i1min (.-start i1)
          i1max (.-end i1)
          i2min (.-start i2)
          i2max (.-end i2)]
      (cond
        ;i1 contains i2
        (<= i1min i2min i2max i1max) i1
        ;i2 contains i1
        (<= i2min i1min i1max i2max) i2
        ;i1 and i2 overlap
        (or (<= i1min i2min i1max)
            (<= i2min i1max i2max)) (interval (min i1min i2min)
                                              (max i1max i2max))
        ;i1 and i2 don't overlap
        :else [i1 i2]))
    ; union one many -> union many one
    (simple? i1) (union i2 i1)
    ; union many one
    (simple? i2)
    (cond
      (< (.-end i2) (start i1)) (vec (concat [i2] i1))
      (< (end i1) (.-start i2)) (conj i1 i2)
      :else (loop [is []
                   i1s i1
                   i i2]
              (if (seq i1s)
                (let [i1 (first i1s)
                      i1min (.-start i1)
                      i1max (.-end i1)
                      i2min (.-start i)
                      i2max (.-end i)]
                  (cond
                    ;i1 ends before i2 begins -- pass i1 on and continue
                    (<= i1max i2min) (recur (conj is i1) (rest i1s) i)
                    ;i2 ends before i1 starts -- conj in (the possibly extended) i2 and then finish up
                    (<= i2max i1min) (into (conj is i) i1s)
                    ;i1 contains i2 -- drop i2 completely and finish up
                    (<= i1min i2min i2max i1max) (into is i1s)
                    ;i2 contains i1 -- drop i1 and continue
                    (<= i2min i1min i1max i2max) (recur is (rest i1s) i)
                    ;i2 overlaps i1 -- extend i2 by i1, drop i1, and continue
                    (or (<= i1min i2min i1max)
                        (<= i2min i1min i2max)) (recur is (rest i1s) (interval (min i1min i2min)
                                                                               (max i1max i2max)))
                    ; that should be all the cases!
                    :else (assert false)))
                ;got to the end without bailing early, which means i ought to be included
                (conj is i))))
    ; union many many
    ; reduce union-with-i1 over elements of i2
    :else (reduce union i1 i2)))

(defn shrink-intervals [func intvl]
  (cond
    (empty-interval? intvl) nil
    (simple? intvl) (func (.-start intvl) (.-end intvl))
    :else (let [new-intvl (reduce
                            (fn [intvl i]
                              (let [new-i (func (.-start i) (.-end i))]
                                (if (empty-interval? new-i)
                                  intvl
                                  (do
                                    #_(assert (and (>= (.-start new-i) (.-start i))
                                                   (<= (.-end new-i) (.-end i))))
                                    (conj intvl new-i)))))
                            []
                            intvl)]
            (if (empty? new-intvl)
              nil
              new-intvl))))

(defn complement-interval [intvl]
  (cond
    ; union -> intersection of complements (demorgan's law)
    (not (simple? intvl)) (reduce intersection (map complement-interval intvl))
    ; empty -> infinite
    (empty-interval? intvl) (interval -Infinity Infinity)
    ; infinite -> empty
    (and
      (simple? intvl)
      (= (.-start intvl) -Infinity)
      (= (.-end intvl) Infinity)) nil
    ; open on left --> open on right
    (= (.-start intvl) -Infinity) (interval (.-end intvl) Infinity)
    ; open on right --> open on left
    (= (.-end intvl) Infinity) (interval -Infinity (.-start intvl))
    ; closed on left, right -> open on left U open on right
    :else (union (interval -Infinity (.-start intvl)) (interval (.-end intvl) Infinity))))

; I1 - I2 = I1 ^ ~I2
(defn subtract [i1 i2]
  (intersection i1 (complement-interval i2)))

; guaranteed to be uniform
(defn rand-t [iv]
  (assert (not (open? iv)) "Can't get random time of open interval")
  (assert (not (empty-interval? iv)) "Can't get random time of empty interval")
  (if (simple? iv)
    (let [min (.-start iv)
          max (.-end iv)]
      (+ min (rand (- max min))))
    (let [widths (map width iv)
          total-width (reduce + widths)
          weights (map #(/ % total-width) widths)
          pick (rand)]
      (reduce (fn [sum [iv w]]
                ; this always yields an interval since the weights sum to 1 and pick is <= 1
                (if (>= (+ sum w) pick)
                  ; iv should be simple, so a uniform random will do fine.
                  ; pick-sum will yield a number between 0 and w.
                  ; we want to divide that by w to get "how far into this interval", then
                  ; multiply that by the width and then add start time to get a number between start and end.
                  (reduced (+ (.-start iv)
                              (* (width iv) (/ (- pick sum) w))))
                  (+ sum w)))
              0
              (zipmap iv weights)))))

(defn ^Boolean interval-contains? [iv t]
  (cond
    (empty-interval? iv) false
    (simple? iv) (<= (.-start iv) t (.-end iv))
    :else (some (fn [iv] (interval-contains? iv t)) iv)))