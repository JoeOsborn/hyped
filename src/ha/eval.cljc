(ns ha.eval
  (:require [ha.ha :as ha]
            [ha.intervals :as iv]))

#?(:clj (def Infinity Double/POSITIVE_INFINITY))
#?(:clj (def -Infinity Double/NEGATIVE_INFINITY))

(def ^:dynamic *debug?* false)

(def frame-length (/ 1 30))
(def time-units-per-frame 10000)
(def time-unit (/ frame-length time-units-per-frame))
(def precision 0.1)

(def guard-memo nil)

(def memo-hit 0)
(def guard-check 0)

(declare transition-interval with-guard-memo)

(defn recalculate-edge [ha-defs ha-vals ha tr-cache index t]
  (let [valid-interval (iv/interval t Infinity)
        ha-def (get ha-defs (.-ha-type ha))
        edge (nth (:edges (ha/current-state ha-def ha)) index)
        ;  _ (println "recalc" (.-id ha) index t (:target edge))
        transition (update (transition-interval ha-defs ha-vals ha edge time-unit)
                           :interval (fn [intvl]
                                       (iv/intersection intvl valid-interval)))
        tr-cache (assoc-in tr-cache [:upcoming-transitions index] transition)]
    #_(println "got" (:interval transition))
    (if (contains? (get-in transition [:transition :label]) :required)
      (assoc tr-cache :required-transitions (ha/sort-transitions
                                              (filter #(and
                                                        (contains? (get-in % [:transition :label]) :required)
                                                        (not (iv/empty-interval? (:interval %))))
                                                      (:upcoming-transitions tr-cache))))
      (assoc tr-cache :optional-transitions (ha/sort-transitions
                                              (filter #(and
                                                        (not (contains? (get-in % [:transition :label]) :required))
                                                        (not (iv/empty-interval? (:interval %))))
                                                      (:upcoming-transitions tr-cache)))))))

(defn enter-state [ha-def ha tr-cache state update-dict now]
  #_(println "enter state" (:id ha) (:v0 ha) (:state ha) "->" state now (- now (:entry-time ha)))
  (let [ha (ha/enter-state ha-def ha state update-dict (ha/floor-time now time-unit) precision)]
    [ha
     (assoc tr-cache
       :upcoming-transitions (mapv (fn [_] nil)
                                   (:edges (ha/current-state ha-def ha)))
       :required-transitions []
       :optional-transitions [])]))

(defn next-transition [ha-defs ha tr-cache inputs]
  (ha/pick-next-transition (get ha-defs (.-ha-type ha))
                           ha
                           inputs
                           (:required-transitions tr-cache)
                           (:optional-transitions tr-cache)))

(defn follow-single-transition [ha-defs
                                ha-vals
                                tr-caches
                                {id                    :id
                                 intvl                 :interval
                                 {target      :target
                                  update-dict :update} :transition :as _tr}]
  #_(println "Follow transition" id intvl target update-dict
           (:index (:transition _tr)) #_(:guard (:transition _tr)))
  (let [[new-ha-val new-tr-cache] (enter-state (get ha-defs id)
                                               (get ha-vals id)
                                               (get tr-caches id)
                                               target
                                               update-dict
                                               (iv/start intvl))]
    #_(println "Old v0" (get ha-vals id) "new v0" new-ha-val)
    [(assoc ha-vals id new-ha-val)
     (assoc tr-caches id new-tr-cache)]))

(defn recalculate-dirtied-edges [ha-defs ha-vals tr-caches transitions t]
  (let [transitioned-ids (set (map :id transitions))
        ; get dependencies of transitioned HAs.
        ; note that these may include some of the transitioned HAs: given the ordering sensitivity
        ; mentioned above, they might have calculated their new intervals based on stale information.
        ; calculating intervals is idempotent and has no second-order effects so it is fine to do it repeatedly
        ; and it also suffices to do it a single time once all the HAs are updated with new times, values and flows.
        ; todo: cache these per-edge?
        dependencies (filter (fn [[_id _sid _idx deps]]
                               (some transitioned-ids deps))
                             (mapcat (fn [hav] (get-in tr-caches [(.-id hav) :depends-on (.-state hav)]))
                                     (vals ha-vals)))
        ;_ (println "deps" deps)
        ; No need to worry about ordering effects here, recalculating edges will not change any behaviors
        ; or entry times so there's no problem with doing it in any order.
        ;_ (println "memo hit 1" ha/memo-hit ha/guard-check)
        ha-vals (ha/extrapolate-all ha-defs
                                    ha-vals
                                    (apply max (map :entry-time (vals ha-vals))))
        ;_ (println "extrapolations before" ha/extrapolations)
        tr-caches (do
                    (assert (nil? guard-memo))
                    (set! guard-memo {})
                    (let [r (reduce (fn [tr-caches [id _sid idx _deps]]
                                      (let [ha (get ha-vals id)
                                            tr-cache (get tr-caches id)
                                            tr-cache (recalculate-edge ha-defs ha-vals ha tr-cache idx t)]
                                        #_(println "T recalc" id idx)
                                        (assoc tr-caches id tr-cache)))
                                    tr-caches
                                    dependencies)]
                      (set! guard-memo nil)
                      r))]
    ;_ (println "extrapolations after" ha/extrapolations)
    ;_ (println "memo hit 2" ha/memo-hit ha/guard-check)

    tr-caches))

(defn follow-transitions [ha-defs ha-vals tr-caches transitions]
  (let [t (iv/start (:interval (first transitions)))
        #__ #_(assert (every? #(= t (iv/start (:interval %))) transitions)
                      "All transitions must have same start time")
        ;_ (println "Transitioning" transitions)
        ; simultaneously transition all the HAs that can transition.
        [ha-vals tr-caches] (reduce
                              (fn [[ha-vals tr-caches] transition]
                                (follow-single-transition ha-defs ha-vals tr-caches transition))
                              [ha-vals tr-caches]
                              transitions)]
    [ha-vals (recalculate-dirtied-edges ha-defs ha-vals tr-caches transitions t)]))

(defn init-has [ha-defs ha-val-seq t]
  (let [obj-ids (map :id ha-val-seq)
        tr-caches (into {} (map (fn [{id    :id
                                      htype :ha-type :as hav}]
                                  [id
                                   {:depends-on           (ha/ha-dependencies (get ha-defs htype) hav)
                                    :upcoming-transitions []
                                    :required-transitions []
                                    :optional-transitions []}])
                                ha-val-seq))
        ha-vals (zipmap obj-ids ha-val-seq)
        start-interval (iv/interval t (+ t time-unit))]
    (set! memo-hit 0)
    (set! guard-check 0)
    ; got to let every HA enter its current (initial) state to set up state invariants like
    ; pending required and optional transitions
    (follow-transitions ha-defs
                        ha-vals
                        tr-caches
                        (map (fn [[id hav]]
                               {:interval   start-interval
                                :id         id
                                :transition {:target (:state hav)}})
                             ha-vals))))

(defn recache-trs [ha-defs config]
  (let [[objs caches] (init-has ha-defs
                                (vals (:objects config))
                                (:entry-time config))]
    (assoc config :tr-caches caches :objects objs)))

(defn update-config [ha-defs config now inputs bailout-limit bailout]
  (if (>= (count bailout) bailout-limit)
    (do
      ;todo: get soft assert working here
      (println "Recursed too deeply in update-config" bailout-limit "vs" (count bailout) bailout)
      [:timeout config])
    (let [config (if (nil? (:tr-caches config))
                   (recache-trs ha-defs config)
                   config)
          qthen (ha/floor-time (:entry-time config) time-unit)
          qnow (ha/floor-time now time-unit)
          valid-interval (iv/interval (+ qthen time-unit) now)]
      (if (= qthen qnow)
        ; do nothing if no delta
        [:ok config]
        (let [has (:objects config)
              tr-caches (:tr-caches config)
              [min-t transitions] (reduce (fn [[min-t transitions] {intvl :interval :as trans}]
                                            (if (nil? trans)
                                              [min-t transitions]
                                              (let [intvl (iv/intersection intvl valid-interval)
                                                    trans (assoc trans :interval intvl)]
                                                ;(assert (<= (iv/width intvl) (iv/width (:interval trans))))
                                                (if (iv/empty-interval? intvl)
                                                  [min-t transitions]
                                                  (let [start (iv/start intvl)]
                                                    (cond
                                                      (< start min-t) [start [trans]]
                                                      (= start min-t) [min-t (conj transitions trans)]
                                                      :else [min-t transitions]))))))
                                          [Infinity []]
                                          (map #(next-transition ha-defs % (get tr-caches (:id %)) inputs)
                                               (vals has)))
              config' (if (and (< min-t Infinity)
                               (<= min-t qnow))
                        (let [
                              ;_ (println "How long to follow transitions?")
                              [has tr-caches] (follow-transitions ha-defs has tr-caches transitions)]
                          (assoc config :entry-time min-t
                                        :inputs inputs
                                        :objects has
                                        :tr-caches tr-caches))
                        config)]
          ;(println "update" qthen min-t qnow)
          #_(println "trs:" transitions)
          #_(println "recur" bailout "now" now qnow "then" qthen "mt" min-t "tr" transitions)
          (if (>= min-t qnow)
            ; this also handles the min-t=Infinity case
            [:ok config']
            (update-config ha-defs
                           config'
                           now
                           (if (= inputs :inert)
                             :inert
                             [(iv/interval min-t (+ min-t frame-length)) (assoc (second inputs) :pressed #{} :released #{})])
                           bailout-limit
                           (conj bailout [min-t transitions]))))))))

(defn simple-guard-sat? [rel xa xb xc ya yb yc c t]
  (ha/simple-guard-satisfied? rel
                              (+ (* xa t t)
                                 (* xb t)
                                 xc)
                              (+ (* ya t t)
                                 (* yb t)
                                 yc)
                              c))

(defn guard-eqn-intervals [xeqns yeqns rel rc t0 tshift time-unit]
  (let [xeqn-count (count xeqns)
        yeqn-count (count yeqns)
        is-eq? (or (= rel :geq) (= rel :leq))]
    (loop [intervals nil
           i 0
           j 0]
      (if (>= j yeqn-count)
        (recur intervals (inc i) 0)
        (if (>= i xeqn-count)
          intervals
          (let [[xa xb xc xstart xend] (nth xeqns i)
                [ya yb yc ystart yend] (nth yeqns j)

                unshifted-start (max xstart ystart 0)

                a (- xa ya)
                b (- xb yb)
                c (- xc yc rc)

                start (+ tshift unshifted-start)
                end (+ tshift (min xend yend))

                roots (ha/find-roots-with-shift a b c tshift)
                _ (when *debug?* (println "unfiltered roots" roots))
                roots (filter #(<= start % end)
                              roots)

                start (+ start (if is-eq? 0 time-unit))
                end (- end (if is-eq? 0 time-unit))

                valid-interval (iv/interval start end)]
            (when *debug?*
              (println "a b c" a b c "s e" start end "roots" roots))
            (case (count roots)
              ; no toggles
              0
              (let [sat? (simple-guard-sat? rel xa xb xc ya yb yc rc unshifted-start)]
                (when *debug?*
                  (println "no toggles, truthy?" sat? (iv/union intervals valid-interval)))
                (recur (if sat?
                         (iv/union intervals valid-interval)
                         intervals)
                       i
                       (inc j)))
              ; 1 toggle -> 1 good interval
              1
              (let [soln (first roots)
                    sat-before? (simple-guard-sat? rel xa xb xc ya yb yc rc (- soln tshift time-unit))
                    new-intervals (if sat-before?
                                    ; first interval is good
                                    (iv/intersection (iv/interval -Infinity
                                                                  (+ soln (if is-eq? 0 (- time-unit))))
                                                     valid-interval)
                                    ; second interval is good
                                    (iv/intersection (iv/interval (+ soln (if is-eq? 0 time-unit))
                                                                  Infinity)
                                                     valid-interval))]
                (when *debug?*
                  (println "toggles at" soln "truthy?" sat-before? "nis:" new-intervals))
                (recur (iv/union intervals new-intervals)
                       i
                       (inc j)))
              ; 2 toggles -> 2 good, 1 bad / 2 bad, 1 good
              2 (let [s1 (first roots)
                      sat-before? (simple-guard-sat? rel xa xb xc ya yb yc rc (- s1 tshift time-unit))
                      s2 (second roots)
                      before-interval (iv/intersection (iv/interval -Infinity
                                                                    (+ s1 (if is-eq? 0 (- time-unit))))
                                                       valid-interval)
                      mid-interval (iv/intersection (iv/interval (+ s1 (if is-eq? 0 time-unit))
                                                                 (+ s2 (if is-eq? 0 (- time-unit))))
                                                    valid-interval)
                      after-interval (iv/intersection (iv/interval (+ s2 (if is-eq? 0 time-unit))
                                                                   Infinity)
                                                      valid-interval)]
                  (when *debug?*
                    (println "two toggles" s1 s2 "truthy?" sat-before?))
                  (if (= s1 s2)
                    (if sat-before?
                      (recur (iv/union intervals (iv/union before-interval
                                                           after-interval))
                             i
                             (inc j))
                      (recur (if is-eq?
                               (iv/union intervals
                                         (iv/interval s1 (+ s1 time-unit)))
                               intervals)
                             i
                             (inc j)))
                    ; t0 is either before s1 or after s1, but before s2.
                    (cond
                      ; before s1.
                      (<= t0 s1)
                      (if sat-before?
                        ; good, bad, good
                        (do
                          #_(println "toggles 1 g b g" (iv/union (iv/union intervals
                                                                           (iv/intersection (iv/interval -Infinity
                                                                                                         (+ s1 (if is-eq? 0 (- time-unit))))
                                                                                            valid-interval))
                                                                 (iv/intersection (iv/interval (+ s2 (if is-eq? 0 time-unit))
                                                                                               Infinity)
                                                                                  valid-interval)))
                          (recur (iv/union (iv/union intervals
                                                     before-interval)
                                           after-interval)
                                 i
                                 (inc j)))
                        ; bad, good, bad
                        (do
                          #_(println "toggles 1 b g b" (iv/union intervals
                                                                 (iv/intersection (iv/interval (+ s1 (if is-eq? 0 time-unit))
                                                                                               (+ s2 (if is-eq? 0 (- time-unit))))
                                                                                  valid-interval)))
                          (recur (iv/union intervals
                                           mid-interval)
                                 i
                                 (inc j))))
                      ; between s1 and s2
                      :else (if sat-before?
                              ;bad, good, bad
                              (do
                                #_(println "toggles 2 b g b" (iv/union intervals
                                                                       (iv/intersection (iv/interval (+ s1 (if is-eq? 0 time-unit))
                                                                                                     (+ s2 (if is-eq? 0 (- time-unit))))
                                                                                        valid-interval)))
                                (recur (iv/union intervals
                                                 (iv/intersection (iv/interval (+ s1 (if is-eq? 0 time-unit))
                                                                               (+ s2 (if is-eq? 0 (- time-unit))))
                                                                  valid-interval))
                                       i
                                       (inc j)))
                              ;good, bad, good
                              (do
                                #_(println "toggles 2 g b g" (iv/union (iv/union intervals
                                                                                 (iv/intersection (iv/interval -Infinity
                                                                                                               (+ s1 (if is-eq? 0 (- time-unit))))
                                                                                                  valid-interval))
                                                                       (iv/intersection (iv/interval (+ s2 (if is-eq? 0 time-unit))
                                                                                                     Infinity)
                                                                                        valid-interval)))
                                (recur (iv/union (iv/union intervals
                                                           (iv/intersection (iv/interval -Infinity
                                                                                         (+ s1 (if is-eq? 0 (- time-unit))))
                                                                            valid-interval))
                                                 (iv/intersection (iv/interval (+ s2 (if is-eq? 0 time-unit))
                                                                               Infinity)
                                                                  valid-interval))
                                       i
                                       (inc j))))))))))))))

(defn constrain-times [interval time-unit]
  (iv/shrink-intervals (fn [s e]
                         (let [new-start (if (<= s time-unit)
                                           time-unit
                                           (ha/ceil-time s time-unit))
                               new-end (ha/floor-time e time-unit)]
                           (iv/interval new-start new-end)))
                       interval))

;todo: can we avoid all the lookups of ha-id against ha-defs and ha-vals? can the former be cached somehow?
(defn simple-guard-interval [ha-defs ha-vals this-ha-val guard time-unit]
  (let [[ha1-id xv] (or (second guard) [nil nil])
        vxv (when ha1-id (keyword "v" (name xv)))
        [ha2-id yv] (if (= (count guard) 4)
                      (ha/third guard)
                      [nil nil])
        vyv (when ha2-id (keyword "v" (name yv)))
        ha1-id (if (= ha1-id :$self)
                 (.-id this-ha-val)
                 ha1-id)
        ha2-id (if (= ha2-id :$self)
                 (.-id this-ha-val)
                 ha2-id)
        ;_ (println "check" (.-id this-ha-val) "for" ha1-id ha2-id guard)
        _ (when *debug?* (println guard))
        rel (first guard)
        ha1 (when ha1-id (get ha-vals ha1-id))
        def1 (when ha1-id (ha/get-def ha-defs ha1))
        ha2 (when ha2-id (get ha-vals ha2-id))
        def2 (when ha2-id (ha/get-def ha-defs ha2))
        ;todo: if the new t0 is > the next required transition time of either ha, return the empty interval
        t0 (max (or (:entry-time ha1) 0) (or (:entry-time ha2) 0))
        tshift (:entry-time this-ha-val)
        ha1 (when ha1
              (if (> t0 (:entry-time ha1))
                (ha/extrapolate def1 ha1 t0 [xv vxv])
                ha1))
        v10 (when ha1
              (get (.-v0 ha1) xv))
        ha2 (when ha2
              (if (> t0 (:entry-time ha2))
                (ha/extrapolate def2 ha2 t0 [yv vyv])
                ha2))
        v20 (when ha2
              (get (.-v0 ha2) yv))
        c (ha/constant-from-expr (last guard))

        ; xeqns is a vec of [coefficients tmin tmax] triples
        ; we take all combinations of the xeqns and yeqns, find roots, and clip them to the given range
        flows1 (when ha1-id (:flows (ha/current-state def1 ha1)))
        xeqns (if ha1
                (ha/flow-equations (.-v0 ha1) flows1 xv)
                [[0 0 0 0 Infinity]])
        flows2 (when ha2-id (:flows (ha/current-state def2 ha2)))
        yeqns (if ha2
                (ha/flow-equations (.-v0 ha2) flows2 yv)
                [[0 0 0 0 Infinity]])
        _ (when *debug?* (println "XEqs:" xeqns "YEqs:" yeqns "Vs:" v10 v20 c))
        ; each equation comes with an interval for which it's valid, and any solution intervals learned from an equation
        ; must be intersected with that overall interval.
        intervals (guard-eqn-intervals xeqns yeqns rel c t0 tshift time-unit)]
    (when *debug?* (println "Eqn Intervals:" intervals))
    #_(println "constrain" intervals
               (constrain-times intervals time-unit))
    (constrain-times intervals time-unit)))

(defn memoized-guard [ha-defs ha-vals ha-val g time-unit]
  (set! guard-check (inc guard-check))
  (let [memo-key (conj g (.-id ha-val) (.-entry-time ha-val))]
    (if-let [memo (and guard-memo
                       (get guard-memo memo-key))]
      (do
        (set! memo-hit (inc memo-hit))
        memo)
      (let [interval (simple-guard-interval ha-defs ha-vals ha-val g time-unit)]
        (when guard-memo
          (set! guard-memo (assoc guard-memo memo-key interval)))
        interval))))

(declare guard-interval)

(defn guard-interval-conjunction [ha-defs ha-vals ha-val g time-unit whole-future]
  ;bail early if the intersection becomes empty
  (when *debug?* (println "AND" g))
  (let [g-count (count g)]
    (loop [intvl whole-future
           gi 1]
      (if (>= gi g-count)
        intvl
        (let [g (nth g gi)
              intvl0 (guard-interval ha-defs ha-vals ha-val g time-unit)
              intvl (iv/intersection intvl intvl0)]
          (when *debug?* (println "AND" g intvl0 "->" intvl))
          (if (iv/empty-interval? intvl)
            nil
            (recur intvl (inc gi))))))))

(defn guard-interval-disjunction [ha-defs ha-vals ha-val g time-unit whole-future]
  (when *debug?* (println "OR" g))
  (let [g-count (count g)]
    (loop [intvl nil
           gi 1]
      (if (>= gi g-count)
        intvl
        (let [g (nth g gi)
              intvl0 (guard-interval ha-defs ha-vals ha-val g time-unit)
              intvl (iv/union intvl intvl0)
              intersection (iv/intersection intvl whole-future)]
          (when *debug?* (println "OR" g intvl0 "->" intvl "->" intersection))
          (if (= intersection whole-future)
            whole-future
            (recur intvl (inc gi))))))))

(defn guard-interval [ha-defs ha-vals ha-val g time-unit]
  ;todo: quantification goes here, using ha-vals and ha-val
  (let [et (:entry-time ha-val)
        min-t (+ et time-unit)
        whole-future (iv/interval min-t Infinity)]
    (if (nil? g)
      whole-future
      (case (first g)
        :and (guard-interval-conjunction ha-defs ha-vals ha-val g time-unit whole-future)
        ;bail early if the union contains [now Infinity]. can we do better?
        :or (guard-interval-disjunction ha-defs ha-vals ha-val g time-unit whole-future)
        (:in-state :not-in-state)
        (do
          (when *debug?*
            (println g (get ha-vals (second g)) (if (contains? (ha/third g) (.-state (get ha-vals (second g))))
                                                  (if (= (first g) :in-state)
                                                    whole-future
                                                    nil)
                                                  (if (= (first g) :not-in-state)
                                                    whole-future
                                                    nil))))
          (if (contains? (ha/third g) (.-state (get ha-vals (second g))))
            (if (= (first g) :in-state)
              whole-future
              nil)
            (if (= (first g) :not-in-state)
              whole-future
              nil)))
        ;todo: colliding overlapping not colliding not overlapping
        (:colliding :not-colliding :touching :not-touching) nil
        :debug (binding [*debug?* true]
                 (guard-interval ha-defs ha-vals ha-val (second g) time-unit))
        (memoized-guard ha-defs ha-vals ha-val g time-unit)))))


(defn transition-interval [ha-defs ha-vals ha-val transition time-unit]
  #_(println "Transition" (:id ha-val) "et" (:entry-time ha-val) (:target transition) (:guard transition))
  (let [checked-guard (:guard transition)
        #_checked-guard #_(if (and (= (:state ha-val) :moving-right)
                                   (= (:x (.-v0 ha-val)) 144)
                                   (= (:target transition) :idle-right))
                            (do
                              (println "UPCOMING" transition)
                              [:debug checked-guard])
                            checked-guard)
        interval (guard-interval ha-defs ha-vals ha-val checked-guard time-unit)]
    ;(assert (not= interval []) "Really empty interval!")
    #_(println "interval:" interval)
    ; TODO: handle cases where transition is also guarded on states
    {:interval   interval
     :id         (:id ha-val)
     :transition transition}))