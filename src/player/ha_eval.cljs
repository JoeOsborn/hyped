(ns player.ha-eval
  (:require [ha.ha :as ha :refer-macros [with-guard-memo]]
            [ha.intervals :as iv])
  (:require-macros [player.macros :refer [soft-assert]]))

(def frame-length (/ 1 30))
(def time-units-per-frame 10000)
(def time-unit (/ frame-length time-units-per-frame))
(def precision 0.1)

(defn transition-intervals [has ha before-t transitions]
  (let [valid-interval (iv/interval -Infinity before-t)]
    (ha/sort-transitions
      (filter #(not (iv/empty-interval? (:interval %)))
              (map #(let [transition-data (ha/transition-interval has ha % time-unit)]
                     (update transition-data
                             :interval
                             (fn [i]
                               (iv/intersection i valid-interval))))
                   transitions)))))

(defn recalculate-edge [has ha index t]
  (let [valid-interval (iv/interval t Infinity)
        edge (nth (:edges (ha/current-state ha)) index)
        transition (update (ha/transition-interval has ha edge time-unit)
                           :interval (fn [intvl]
                                       (iv/intersection intvl valid-interval)))
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
  ;(println "enter state" (:id ha) [(:x ha) (:y ha) (:v/x ha) (:v/y ha)] (:state ha) "->" state now)
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
                 (iv/start intvl))))

(defn recalculate-dirtied-edges [has transitions t]
  (let [transitioned-ids (set (map :id transitions))
        ; get dependencies of transitioned HAs.
        ; note that these may include some of the transitioned HAs: given the ordering sensitivity
        ; mentioned above, they might have calculated their new intervals based on stale information.
        ; calculating intervals is idempotent and has no second-order effects so it is fine to do it repeatedly
        ; and it also suffices to do it a single time once all the HAs are updated with new times, values and flows.
        ; todo: cache these per-edge?
        dependencies (filter (fn [[_id _idx deps]]
                               (some transitioned-ids deps))
                             (mapcat (fn [ha] (get-in ha [:depends-on (:state ha)]))
                                     (vals has)))
        ;_ (println "deps" deps)
        ; No need to worry about ordering effects here, recalculating edges will not change any behaviors
        ; or entry times so there's no problem with doing it in any order.
        ;_ (println "memo hit 1" ha/memo-hit ha/guard-check)
        has (with-guard-memo
              (reduce (fn [has [id idx _deps]]
                        (let [ha (get has id)]
                          #_(println "T recalc" id)
                          (assoc has id (recalculate-edge has ha idx t))))
                      has
                      dependencies))
        ;_ (println "memo hit 2" ha/memo-hit ha/guard-check)
        ]
    has))

(defn follow-transitions [has transitions]
  (let [t (iv/start (:interval (first transitions)))
        _ (assert (every? #(= t (iv/start (:interval %))) transitions)
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
        ha-seq (map (fn [ha]
                      (assoc ha :depends-on (ha/ha-dependencies ha)))
                    ha-seq)
        obj-dict (zipmap obj-ids ha-seq)
        start-interval (iv/interval 0 time-unit)]
    (set! ha/memo-hit 0)
    (set! ha/guard-check 0)
    ; got to let every HA enter its current (initial) state to set up state invariants like
    ; pending required and optional transitions
    (follow-transitions obj-dict
                        (map (fn [[id ha]]
                               {:interval   start-interval
                                :id         id
                                :transition {:target (:state ha)}})
                             obj-dict))))

(defn update-config [config now inputs bailout-limit bailout]
  (assert (<= bailout bailout-limit) "Recursed too deeply in update-config")
  (let [qthen (ha/floor-time (:entry-time config) time-unit)
        qnow (ha/floor-time now time-unit)
        valid-interval (iv/interval (+ qthen time-unit) now)]
    (if (= qthen qnow)
      ; do nothing if no delta
      config
      (let [has (:objects config)
            ;todo: a bug in here? we're getting two with different start times!!!
            [min-t transitions] (reduce (fn [[min-t transitions] {intvl :interval :as trans}]
                                          (if (nil? trans)
                                            [min-t transitions]
                                            (let [intvl (iv/intersection intvl valid-interval)
                                                  trans (assoc trans :interval intvl)]
                                              (assert (<= (iv/width intvl) (iv/width (:interval trans))))
                                              (if (iv/empty-interval? intvl)
                                                [min-t transitions]
                                                (let [start (iv/start intvl)]
                                                  (cond
                                                    (< start min-t) [start [trans]]
                                                    (= start min-t) [min-t (conj transitions trans)]
                                                    :else [min-t transitions]))))))
                                        [Infinity []]
                                        (map #(next-transition has % inputs) (vals has)))
            config' (if (<= min-t qnow)
                      (assoc config :entry-time min-t
                                    :inputs inputs
                                    :objects (follow-transitions has transitions))
                      config)]
        ;(println "update" qthen min-t qnow)
        #_(println "trs:" transitions)
        #_(println "recur" bailout "now" now qnow "then" qthen "mt" min-t "tr" transitions)
        (if (>= min-t qnow)
          ; this also handles the min-t=Infinity case
          config'
          (update-config config'
                         now
                         (if (= inputs :inert)
                           :inert
                           [(iv/interval min-t (+ min-t frame-length)) (assoc (second inputs) :pressed #{} :released #{})])
                         bailout-limit
                         (inc bailout)))))))
