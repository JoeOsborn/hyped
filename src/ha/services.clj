(ns ha.services
  (:require [cognitect.transit :as transit]
            [ha.ha :as ha]
            [ha.rollout :as roll]
            [clojure.java.io :as jio]
            [clojure.string :as string]
            [ha.intervals :as iv]
            [ha.eval :as heval]
            [ha.z3 :as z3]
            [ha.desugar :as desugar])
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
        (let [unroll-limit 5                                ; how many inert successor transitions do we reach forward to constrain t0?
              lookahead-time 1000
              [ha-defs ha-vals] read-args
              z3 (z3/->z3 ha-defs)
              ; we need guards to be convex in order for the tS...t0 split to make sense! Later, use
              ; quantifier instantiation where possible and forbid
              ; <state sequence, quantifier choice sequence> pairs from the model
              ha-defs (desugar/guard-disjunctions-to-transitions ha-defs)
              ha-defs (desugar/simplify-guards ha-defs z3)
              z3 (z3/update-ha-defs z3 ha-defs)
              _ (assert (:ha-defs z3))
              entry-time (apply max (map :entry-time (vals ha-vals)))
              [ha-vals tr-caches] (heval/init-has ha-defs (vals ha-vals) entry-time)
              config {:objects ha-vals
                      :entry-time entry-time
                      :tr-caches tr-caches
                      :inputs #{}}
              _ (println "vals" ha-vals config)
              [_reqs opts] (roll/next-transitions config)
              _ (println "trs" (count _reqs) (count opts))
              ; so for each optional transition available
              times (doall
                      (for [{intvl                    :interval
                             {target :target
                              index  :index :as edge} :transition
                             ha-id                    :id :as o} opts
                            :let
                            [tS (iv/start intvl)
                             tE (iv/end intvl)
                             _ (println "opt" index tS tE)
                             ha (get-in config [:objects ha-id])
                             ha-type (.-ha-type ha)
                             _ (assert (:ha-defs z3))
                             ; solve for values of t0 in tS...tE.
                             worlds (z3/with-solver
                                      z3
                                      (fn [z3]
                                        (assert (or (:solver z3) (:optimizer z3)))
                                        (assert (:ha-defs z3))
                                        (let [z3 (z3/assert-valuation! z3 (:objects config) "t00")
                                              _ (assert (:has z3))
                                              _ (assert (or (:solver z3) (:optimizer z3)))
                                              _ (assert (:ha-defs z3))
                                              z3 (z3/assert-flow-jump! z3 ha-id edge "t0")
                                              _ (assert (or (:solver z3) (:optimizer z3)))
                                              z3 (z3/assert-all! z3 [[:gt "t0" "t00"]
                                                                     [:geq "t0" tS]
                                                                     [:leq "t0" (min tE (+ tS lookahead-time))]])
                                              _ (assert (or (:solver z3) (:optimizer z3)))
                                              status (z3/check! z3)
                                              _ (assert (= status :sat))
                                              [z3 time-steps] (z3/symx! z3 1)
                                              found-intervals
                                              (loop [found-intervals #{}
                                                     z3 z3]
                                                (assert (:has z3))
                                                (if (= :sat (ha/spy "constraint set ok?" found-intervals (z3/check! z3)))
                                                  ; add this interval and then forbid the particular trace
                                                  (let [z3 (z3/push! z3)
                                                        _ (assert (:has z3))
                                                        z3 (z3/assert-all! z3
                                                                           [(z3/path-constraints z3 time-steps)])
                                                        tmin (z3/min-value z3 "t0")
                                                        tmax (z3/max-value z3 "t0")
                                                        z3 (z3/pop! z3)
                                                        _ (println "tmin" tmin "tmax" tmax)
                                                        t-i (ha/spy "found interval" (iv/interval tmin tmax))
                                                        z3 (z3/assert-all!
                                                             z3
                                                             [[:not (z3/path-constraints z3 time-steps)]])
                                                        ;find minimal splits of t0 wrt existing splits
                                                        ; if this new split does not overlap any splits, just add it.
                                                        overlapping-intervals (sort-by :start (filter #(iv/intersection t-i %) found-intervals))]
                                                    (recur (conj found-intervals t-i) z3))
                                                  found-intervals))]
                                          ;break up found-intervals?
                                          found-intervals)))
                             sorted-worlds (sort-by :start (set worlds))]]
                        [o sorted-worlds]))]
          (transit/write (ha/transit-writer out-stream)
                         (ha/spy "ret" times))))
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
