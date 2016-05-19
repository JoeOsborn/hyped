(ns ha.services
  (:require [cognitect.transit :as transit]
            [ha.ha :as ha]
            [ha.rollout :as roll]
            [clojure.java.io :as jio]
            [clojure.string :as string]
            [ha.intervals :as iv]
            [ha.eval :as heval]
            [ha.z3 :as z3])
  (:use [ring.middleware
         params
         keyword-params
         nested-params
         reload])
  (:import (java.io ByteArrayOutputStream)))

#_(defremote
    symx-1 [transit-args]
    (let [[ha-defs ha-vals] (transit/read (transit/reader transit-args
                                                          :json
                                                          (ha/transit-reader)))]
      (transit/write (ha/transit-writer nil) [])))

#_(def services (-> rpc/wrap-rpc
                    wrap-keyword-params
                    wrap-nested-params
                    wrap-params
                    ))

(defn rpc-handler [req]
  (when (= (:uri req)
           "/rpc/explore")
    (println "req" req)
    (let [read-params (clojure.data.json/read (jio/reader (:body req)))
          read-method (get read-params "method")
          read-args (transit/read (ha/transit-reader (jio/input-stream (.getBytes (get read-params "arguments") "UTF-8"))))
          out-stream (ByteArrayOutputStream.)]
      (case read-method
        "symx-1"
        ; OK, let's do this. We want to know the one-step reachable regions, ie
        ; the reached pseudomodes of each successor state.
        (let [zeno-limit 5                                  ; how many intermediate transitions do we allow when trying to flow out to a required transition?
              quiescence-limit 5                            ; how many inert successor transitions do we reach forward to constrain t0?
              [ha-defs config] read-args
              ha-vals (:objects config)
              [_reqs opts] (roll/next-transitions config)
              ; so for each optional transition available
              times (doall
                      (for [{intvl                     :interval
                             {target :target :as edge} :transition
                             ha-id                     :id :as o} opts
                            :let
                            [tS (iv/start intvl)
                             tE (iv/end intvl)
                             ha (get-in config [:objects ha-id])
                             ha-type (.-ha-type ha)
                             ha-def (get ha-defs ha-type)
                             src-state (ha/current-state ha-def ha)
                             dest-state (get-in ha-def [:states target])
                             ; solve for values of t0 in tS...tE.
                             worlds (z3/with-solver
                                      (z3/->z3 ha-defs)
                                      (fn [z3]
                                        ; * assert current values of all HA variables
                                        (z3/assert-valuation! z3 ha-vals [:t 0])
                                        ; * note that we really want to do the following via depth-first traversal through dest states of r. but for now we'll do just one level.
                                        ; * assert a jump at t0 that does edge
                                        (let [t0-cs [[:geq [:t 1] tS]
                                                     [:leq [:t 1] tE]]
                                              next-reqs (filter ha/required-transition? (:edges dest-state))
                                              _ (z3/assert-all! z3 t0-cs)
                                              ; * Do a flow-jump by tS time along edge "edge" as well as any other edges that must be followed. Asserts that no other transition of HA or any other HA happened before t0, that HA has no higher priority transitions at t0, that no other HA transitions before t0, that all other HAs with required transitions at t0 take the highest priority such ones.
                                              z3 (z3/assert-flow-jump! z3 ha-id src-state edge [:t 1] zeno-limit)]
                                          (assert (= :sat (z3/check! z3)))
                                          (doall
                                            (for [r next-reqs]
                                              (do
                                                (z3/push! z3)
                                                (let [z3 (z3/assert-flow-jump! z3
                                                                               ha-id
                                                                               dest-state
                                                                               r
                                                                               [:t 2]
                                                                               zeno-limit)
                                                      ret (if (= :sat (z3/check! z3))
                                                            [(z3/min-value z3 [:t 1])
                                                             (z3/max-value z3 [:t 1])]
                                                            :invalid)]
                                                  (z3/pop! z3)
                                                  ret)))))))
                             worlds (disj (set worlds) :invalid)
                             sorted-worlds (sort-by first worlds)]]
                        [o (map first sorted-worlds)]))]
          (transit/write (ha/transit-writer out-stream)
                         times)))
      {:status  200
       :headers {"Content-Type" "application/json"}
       :body    (str "\"" (string/escape (.toString out-stream) {\" "\\\""}) "\"")})))

(def handler
  (-> #'rpc-handler
      (wrap-reload)
      wrap-keyword-params
      wrap-nested-params
      wrap-params))

#_(defonce server (rs/serve services {:port 4445 :join false}))

;(defn start [] nil)
;(defn stop [] nil)

#_(defn start [] (.start server))
#_(defn stop [] (.stop server))
