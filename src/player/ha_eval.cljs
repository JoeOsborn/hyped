(ns player.ha-eval
  (:require [ha.ha :as ha :refer-macros [with-guard-memo]]
            [ha.intervals :as iv])
  (:require-macros [player.macros :refer [soft-assert]]))

(def frame-length (/ 1 30))
(def time-units-per-frame 10000)
(def time-unit (/ frame-length time-units-per-frame))
(def precision 0.1)

(defn recalculate-edge [ha-defs ha-vals ha tr-cache index t]
  (let [valid-interval (iv/interval t Infinity)
        ha-def (get ha-defs (.-ha-type ha))
        edge (nth (:edges (ha/current-state ha-def ha)) index)
        transition (update (ha/transition-interval ha-defs ha-vals ha edge time-unit)
                           :interval (fn [intvl]
                                       (iv/intersection intvl valid-interval)))
        tr-cache (assoc-in tr-cache [:upcoming-transitions index] transition)]
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
  ;(println "enter state" (:id ha) (:v0 ha) (:state ha) "->" state now)
  (let [ha (ha/enter-state ha-def ha state update-dict now time-unit precision)]
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
  (let [[new-ha-val new-tr-cache] (enter-state (get ha-defs id)
                                               (get ha-vals id)
                                               (get tr-caches id)
                                               target
                                               update-dict
                                               (iv/start intvl))]
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
        tr-caches (with-guard-memo
                              (reduce (fn [tr-caches [id _sid idx _deps]]
                                        (let [ha (get ha-vals id)
                                              tr-cache (get tr-caches id)
                                              tr-cache (recalculate-edge ha-defs ha-vals ha tr-cache idx t)]
                                          #_(println "T recalc" id idx)
                                          (assoc tr-caches id tr-cache)))
                                      tr-caches
                                      dependencies))
        ;_ (println "memo hit 2" ha/memo-hit ha/guard-check)
        ]
    tr-caches))

(defn follow-transitions [ha-defs ha-vals tr-caches transitions]
  (let [t (iv/start (:interval (first transitions)))
        _ (assert (every? #(= t (iv/start (:interval %))) transitions)
                  "All transitions must have same start time")
        ;_ (println "Transitioning" transitions)
        ; simultaneously transition all the HAs that can transition.
        [ha-vals tr-caches] (reduce
                              (fn [[ha-vals tr-caches] transition]
                                (follow-single-transition ha-defs ha-vals tr-caches transition))
                              [ha-vals tr-caches]
                              transitions)]
    [ha-vals (recalculate-dirtied-edges ha-defs ha-vals tr-caches transitions t)]))

(defn init-has [ha-defs ha-val-seq]
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
        start-interval (iv/interval 0 time-unit)]
    (set! ha/memo-hit 0)
    (set! ha/guard-check 0)
    ; got to let every HA enter its current (initial) state to set up state invariants like
    ; pending required and optional transitions
    (let [[objs tr-caches] (follow-transitions ha-defs
                                               ha-vals
                                               tr-caches
                                               (map (fn [[id hav]]
                                                      {:interval   start-interval
                                                       :id         id
                                                       :transition {:target (:state hav)}})
                                                    ha-vals))]
      [objs tr-caches])))

(defn update-config [ha-defs config now inputs bailout-limit bailout]
  (assert (<= bailout bailout-limit) "Recursed too deeply in update-config")
  (let [qthen (ha/floor-time (:entry-time config) time-unit)
        qnow (ha/floor-time now time-unit)
        valid-interval (iv/interval (+ qthen time-unit) now)]
    (if (= qthen qnow)
      ; do nothing if no delta
      config
      (let [has (:objects config)
            tr-caches (:tr-caches config)
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
                                        (map #(next-transition ha-defs % (get tr-caches (:id %)) inputs)
                                             (vals has)))
            config' (if (and (< min-t Infinity)
                             (<= min-t qnow))
                      (let [[has tr-caches] (follow-transitions ha-defs has tr-caches transitions)]
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
          config'
          (update-config ha-defs
                         config'
                         now
                         (if (= inputs :inert)
                           :inert
                           [(iv/interval min-t (+ min-t frame-length)) (assoc (second inputs) :pressed #{} :released #{})])
                         bailout-limit
                         (inc bailout)))))))
