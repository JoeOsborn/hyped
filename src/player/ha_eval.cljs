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

(defn enter-state [has ha state update-dict now]
  (println "enter state" (:id ha) [(:x ha) (:y ha) (:v/x ha) (:v/y ha)] (:state ha) "->" state now)
  (let [ha (ha/enter-state ha state update-dict now time-unit precision)
        ha (assoc ha :upcoming-transitions []
                     :required-transitions []
                     :optional-transitions [])
        has (assoc has (:id ha) ha)
        ha (reduce (fn [ha ei] (recalculate-edge has ha ei now))
                   ha
                   (range (count (:edges (ha/current-state ha)))))
        reqs (:required-transitions ha)
        simultaneous-reqs (filter #(= (iv/start-time (:interval %))
                                      (iv/start-time (:interval (first reqs))))
                                  reqs)]
    #_(println "RC:" (count reqs) "SRC:" (count simultaneous-reqs))
    (soft-assert (<= (count simultaneous-reqs) 1)
                   "More than one required transition is available!" simultaneous-reqs)
    (println "New required transitions" (transition-intervals has
                                                              ha
                                                              Infinity
                                                              (ha/required-transitions ha)))
    (println "New optional transitions" (transition-intervals has
                                                              ha
                                                              Infinity
                                                              (ha/optional-transitions ha)))
    (assert (or (nil? (first reqs)) (>= (iv/start-time (:interval (first reqs))) now))
            "Can't transition until later than entry time")
    ha))

(defn init-has [ha-seq]
  (let [obj-ids (map :id ha-seq)
        obj-dict (zipmap obj-ids ha-seq)]
    ; got to let every HA enter its current (initial) state to set up state invariants like
    ; pending required and optional transitions
    (into {} (map (fn [[k ha]]
                    [k (enter-state obj-dict ha (:state ha) nil 0)])
                  obj-dict))))

(defn next-transition [_has ha then inputs]
  (ha/pick-next-transition ha then inputs
                           (:required-transitions ha)
                           (:optional-transitions ha)))

(defn follow-transitions [has transitions]
  (let [t (iv/start-time (:interval (first transitions)))
        _ (assert (every? #(= t (iv/start-time (:interval %))) transitions)
                  "All transitions must have same start time")
        ;_ (println "Transitioning" transitions)
        ; simultaneously transition all the HAs that can transition.
        transitioned-has (map (fn [{id :id {target :target update-dict :update} :transition}]
                                #_(println "transitioning state-change" id
                                           (:entry-time (get has id)) "->"
                                           t (:state (get has id)) "->" target)
                                (enter-state has (get has id) target update-dict t))
                              transitions)
        transitioned-ids (into #{} (map :id transitioned-has))
        ;_ (println "changed" transitioned-ids)
        ; merge into HAS. note that their intervals may not be correct right now due to ordering sensitivity!
        has (merge has (zipmap (map :id transitioned-has) transitioned-has))
        ; get dependencies of transitioned HAs.
        ; note that these may include some of the transitioned HAs: given the ordering sensitivity
        ; mentioned above, they might have calculated their new intervals based on stale information.
        ; calculating intervals is idempotent and has no second-order effects so it is fine to do it repeatedly
        ; and it also suffices to do it a single time once all the HAs are updated with new times, values and flows.
        ; todo: cache these?
        deps (filter (fn [[_id _idx deps]]
                       #_(println "accept?" [_id _idx deps]
                                  "of" transitioned-ids ":"
                                  (some transitioned-ids deps))
                       (some transitioned-ids deps))
                     (mapcat #(ha/ha-dependencies %)
                             (vals has)))
        ;_ (println "deps" deps)
        ; No need to worry about ordering effects here, recalculating edges will not change any behaviors
        ; or entry times so there's no problem with doing it in any order.
        has (reduce (fn [has [id idx _deps]]
                      (let [ha (get has id)]
                        #_(println "T recalc" id)
                        (assoc has id (recalculate-edge has ha idx t))))
                    has
                    deps)]
    #_(println "next transitions" #_reenter-has (transition-intervals has
                                                                      (second reenter-has)
                                                                      Infinity
                                                                      (required-transitions (second reenter-has))))
    has))

(defn update-scene [scene now inputs bailout]
  (assert (<= bailout 100) "Recursed too deeply in update-scene")
  (let [qthen (ha/floor-time (:now scene) time-unit)
        qnow (ha/floor-time now time-unit)
        has (:objects scene)
        [min-t transitions] (reduce (fn [[min-t transitions] {intvl :interval :as trans}]
                                      (let [intvl (iv/intersection intvl [qthen now])
                                            start (iv/start-time intvl)]
                                        (cond
                                          (iv/empty-interval? intvl) [min-t transitions]
                                          (nil? trans) [min-t transitions]
                                          (< start min-t) [start [trans]]
                                          (= start min-t) [min-t (conj transitions trans)]
                                          :else [min-t transitions])))
                                    [Infinity []]
                                    (map #(next-transition has % qthen inputs) (vals has)))]
    #_(println "recur" bailout "now" now qnow "then" qthen "mt" min-t "tr" transitions)
    (cond
      ; this also handles the min-t=Infinity case
      (> min-t qnow) (assoc scene :now now)
      (= min-t qnow) (do #_(println "clean border")
                       (assoc scene :now now
                                    :objects (follow-transitions has transitions)))
      :else (do #_(println "messy border overflow" (- now min-t))
              (update-scene (assoc scene :now min-t
                                         :objects (follow-transitions has transitions))
                            now
                            ; clear pressed and released instant stuff
                            (assoc inputs :pressed #{} :released #{})
                            (inc bailout)))
      )))
