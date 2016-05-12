(ns player.explore-service
  (:require [ha.ha :as ha]
            [player.seen-viz :as seen-viz]
            [ha.rollout :as roll]
            [servant.core :as servant]
            [servant.worker :as worker]
            [cljs.core.async :as a]
            [cognitect.transit :as transit])
  (:require-macros [cljs.core.async.macros :refer [go]]
                   [servant.macros :refer [defservantfn]]))


(def worker-count 4)
(def worker-script "/js/compiled/explore_service.js")

(declare worker-explore-fn)

(when-not (servant/webworker?)
  (def servant-channel (servant/spawn-servants worker-count worker-script))
  (defn worker-explore [ha-defs newest
                        unroll-limit explore-rolled-out? explore-roll-limit
                        report-fn]
    #_(.setTimeout js/window #(report-fn #{} {}) 0)
    (let [channel (servant/servant-thread servant-channel servant/standard-message
                                          worker-explore-fn
                                          (transit/write (ha/transit-writer)
                                                         [ha-defs newest
                                                          unroll-limit explore-rolled-out? explore-roll-limit]))]
      (go
        ;(println "start waiting" channel newest)
        (let [result (a/<! channel)
              ;_ (println "got" result)
              [explored seen-polys] (transit/read (ha/transit-reader) result)]
          (report-fn explored seen-polys))))))

(defservantfn worker-explore-fn [transit-args]
              (let [[ha-defs newest
                     unroll-limit explore-rolled-out? explore-roll-limit] (transit/read (ha/transit-reader) transit-args)
                    _ (println "roll" (count newest) (map :entry-time newest))
                    focused-objects #{}
                    [rolled-playout _seen-configs] (time (roll/inert-playout ha-defs (last newest) unroll-limit #{}))
                    rolled-playout (concat newest rolled-playout)
                    _ (println "explore" (count rolled-playout))
                    [playouts explored] (time (roll/explore-nearby ha-defs
                                                                   (if explore-rolled-out?
                                                                     rolled-playout
                                                                     newest)
                                                                   explore-roll-limit))
                    _ (assert (every? map? rolled-playout))
                    _ (assert (every? map? (apply concat playouts)))
                    playouts (filter #(not (empty? %))
                                     (conj playouts rolled-playout))
                    _ (println "explore playouts" (count playouts) (map count playouts))
                    ;todo: try not collecting all the seen polys and just drawing new stuff into the canvas regardless. let the canvas be the buffer.
                    _ (println "merge-in")
                    seen (time
                           (reduce
                             (fn [seen playout]
                               (assert (seqable? playout))
                               (let [final-config (last playout)]
                                 (assert (map? final-config) (str "Final config:" final-config "configs:" (str playout)))
                                 (reduce
                                   (fn [seen [prev-config next-config]]
                                     (assert (map? prev-config))
                                     (assert (map? next-config))
                                     (reduce
                                       (fn [seen {id         :id
                                                  ha-type    :ha-type
                                                  state      :state
                                                  entry-time :entry-time
                                                  :as        prev-ha}]
                                         (if (or (empty? focused-objects)
                                                 (contains? focused-objects id))
                                           (let [{next-state :state :as next-ha} (get-in next-config [:objects id])
                                                 next-time (if (= next-config final-config)
                                                             (:entry-time next-config)
                                                             (:entry-time next-ha))]
                                             (if (or (not= state next-state)
                                                     (not= entry-time next-time))
                                               (let [seen-for-ha (get seen id #{})
                                                     seen-for-ha' (seen-viz/merge-seen-poly seen-for-ha
                                                                                            (get ha-defs ha-type)
                                                                                            prev-ha
                                                                                            next-time)]
                                                 (assoc seen id seen-for-ha'))
                                               seen))
                                           seen))
                                       seen
                                       (vals (:objects prev-config))))
                                   seen
                                   (ha/pair (butlast playout)
                                            (rest playout)))))
                             {}
                             playouts))]
                (println "newest:" (count newest) (map :entry-time newest))
                (transit/write (ha/transit-writer) [explored seen])))

(when (servant/webworker?)
  (enable-console-print!)
  (worker/bootstrap))

