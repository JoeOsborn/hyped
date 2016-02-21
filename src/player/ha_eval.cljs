(ns player.ha-eval
  (:require [ha.ha :as ha]
            [ha.intervals :as iv])
  (:require-macros [player.macros :refer [soft-assert]]))

(def frame-length (/ 1 30))
(def time-units-per-frame 10000)
(def time-unit (/ frame-length time-units-per-frame))
(def precision 0.1)

(defn transition-intervals [has ha before-t transitions]
  (ha/sort-transitions
    (filter #(not (iv/empty-interval? (:interval %)))
            (map #(let [transition-data (ha/transition-interval has ha % time-unit)]
                   (update transition-data
                           :interval
                           (fn [i]
                             (iv/intersection i [-Infinity before-t]))))
                 transitions))))

(defn recalculate-edge [has ha index t]
  (let [edge (nth (:edges (ha/current-state ha)) index)
        transition (update (ha/transition-interval has ha edge time-unit)
                           :interval (fn [intvl]
                                       (iv/intersection intvl [t Infinity])))
        ha (assoc-in ha [:upcoming-transitions index] transition)]
    #_(println "recalc" (:id ha) index transition)
    #_(println "REQS" (:id ha) (:entry-time ha) #_transition
               (ha/sort-transitions
                 (filter #(and
                           (contains? (get-in % [:transition :label]) :required)
                           (not (iv/empty-interval? (:interval %))))
                         (:upcoming-transitions ha))))
    (if (contains? (get-in transition [:transition :label]) :required)
      (assoc ha :required-transitions (ha/sort-transitions
                                        (filter #(and
                                                  (contains? (get-in % [:transition :label]) :required)
                                                  (not (iv/empty-interval? (:interval %))))
                                                (:upcoming-transitions ha))))
      (assoc ha :optional-transitions (ha/sort-transitions
                                        (filter #(and
                                                  (not (contains? (get-in % [:transition :label]) :required))
                                                  (not (iv/empty-interval? (:interval %))))
                                                (:upcoming-transitions ha)))))))

(defn enter-state [ha state update-dict now]
  (println "enter state" (:id ha) [(:x ha) (:y ha) (:v/x ha) (:v/y ha)] (:state ha) "->" state now)
  (let [ha (ha/enter-state ha state update-dict now time-unit precision)]
    (assoc ha
      :upcoming-transitions (mapv (fn [_] nil)
                                  (:edges (ha/current-state ha)))
      :required-transitions []
      :optional-transitions [])))

(defn next-transition [_has ha inputs]
  (ha/pick-next-transition ha inputs
                           (:required-transitions ha)
                           (:optional-transitions ha)))

(defn follow-single-transition [has {id                    :id
                                     intvl                 :interval
                                     {target      :target
                                      update-dict :update} :transition}]
  (assoc has
    id
    (enter-state (get has id)
                 target
                 update-dict
                 (iv/start-time intvl))))

(defn recalculate-dirtied-edges [has transitions t]
  (let [transitioned-ids (into #{} (map :id transitions))
        ; get dependencies of transitioned HAs.
        ; note that these may include some of the transitioned HAs: given the ordering sensitivity
        ; mentioned above, they might have calculated their new intervals based on stale information.
        ; calculating intervals is idempotent and has no second-order effects so it is fine to do it repeatedly
        ; and it also suffices to do it a single time once all the HAs are updated with new times, values and flows.
        ; todo: cache these?
        dependencies (filter (fn [[_id _idx deps]]
                               (some transitioned-ids deps))
                             (mapcat #(ha/ha-dependencies %)
                                     (vals has)))
        ;_ (println "deps" deps)
        ; No need to worry about ordering effects here, recalculating edges will not change any behaviors
        ; or entry times so there's no problem with doing it in any order.
        _ (println "memo hit 1" ha/memo-hit ha/guard-check)
        has (ha/with-guard-memo
              (fn [] (reduce (fn [has [id idx _deps]]
                               (let [ha (get has id)]
                                 #_(println "T recalc" id)
                                 (assoc has id (recalculate-edge has ha idx t))))
                             has
                             dependencies)))
        _ (println "memo hit 2" ha/memo-hit ha/guard-check)]
    has))

(defn follow-transitions [has transitions]
  (let [t (iv/start-time (:interval (first transitions)))
        _ (assert (every? #(= t (iv/start-time (:interval %))) transitions)
                  "All transitions must have same start time")
        ;_ (println "Transitioning" transitions)
        ; simultaneously transition all the HAs that can transition.
        has (reduce
              follow-single-transition
              has
              transitions)]
    (recalculate-dirtied-edges has transitions t)))

(defn init-has [ha-seq]
  (let [obj-ids (map :id ha-seq)
        obj-dict (zipmap obj-ids ha-seq)]
    (set! ha/memo-hit 0)
    (set! ha/guard-check 0)
    ; got to let every HA enter its current (initial) state to set up state invariants like
    ; pending required and optional transitions
    (follow-transitions obj-dict
                        (map (fn [[id ha]]
                               {:interval [0 time-unit]
                                :id       id
                                :transition {:target (:state ha)}})
                             obj-dict))))

(defn update-config [config now inputs bailout-limit bailout]
  (assert (<= bailout bailout-limit) "Recursed too deeply in update-config")
  (let [qthen (ha/floor-time (:entry-time config) time-unit)
        qnow (ha/floor-time now time-unit)]
    (if (= qthen qnow)
      ; do nothing if no delta
      config
      (let [has (:objects config)
            [min-t transitions] (reduce (fn [[min-t transitions] {intvl :interval :as trans}]
                                          (let [intvl (iv/intersection intvl [(+ qthen time-unit) now])
                                                start (iv/start-time intvl)]
                                            (cond
                                              (iv/empty-interval? intvl) [min-t transitions]
                                              (nil? trans) [min-t transitions]
                                              (< start min-t) [start [trans]]
                                              (= start min-t) [min-t (conj transitions trans)]
                                              :else [min-t transitions])))
                                        [Infinity []]
                                        (map #(next-transition has % inputs) (vals has)))
            config' (if (<= min-t qnow)
                      (assoc config :entry-time min-t
                                    :inputs inputs
                                    :objects (follow-transitions has transitions))
                      config)]
        (println "update" qthen min-t qnow)
        #_(println "trs:" transitions)
        #_(println "recur" bailout "now" now qnow "then" qthen "mt" min-t "tr" transitions)
        (if (>= min-t qnow)
          ; this also handles the min-t=Infinity case
          config'
          (update-config config'
                         now
                         (if (= inputs :inert)
                           :inert
                           [[min-t (+ min-t frame-length)] (assoc (second inputs) :pressed #{} :released #{})])
                         bailout-limit
                         (inc bailout)))))))
