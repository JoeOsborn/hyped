(ns ha.services
  (:require [cognitect.transit :as transit]
            [fipp.edn :as fipp]
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
    bmc-1 [transit-args]
    (let [[ha-defs ha-vals] (transit/read (transit/reader transit-args
                                                          :json
                                                          (ha/transit-reader)))]
      (transit/write (ha/transit-writer nil) [])))

#_(def services (-> rpc/wrap-rpc
                    wrap-keyword-params
                    wrap-nested-params
                    wrap-params))


(def z3-lock 1)

(defn rpc-handler [req]
  (println "handle" req)
  (cond
    (= (:uri req)
       "/rpc/check")
    (do
      (let [read-params (clojure.data.json/read (jio/reader (:body req)))
            read-args (transit/read (ha/transit-reader (jio/input-stream (.getBytes (get read-params "arguments") "UTF-8"))))
            out-stream (ByteArrayOutputStream.)
            [ha-defs ha-vals target-state bound] read-args
            ;todo: remove hack once the arg parsing/sending actually works right
            bound 20
            witness (ha/spy "overall time"
                            (time (locking z3-lock
                                    (ha/spy "interior time"
                                            (time (z3/model-check ha-defs ha-vals [target-state] bound))))))]
        (transit/write (ha/transit-writer out-stream)
                       (ha/spy "ret" witness))
        {:status  200
         :headers {"Content-Type" "application/json"}
         :body    (str "\"" (string/escape (.toString out-stream) {\" "\\\""}) "\"")}))))
    ;(= (:uri req)
    ;   "/rpc/explore")
    ;(do
    ;  (let [read-params (clojure.data.json/read (jio/reader (:body req)))
    ;        read-method (get read-params "method")
    ;        read-args (transit/read (ha/transit-reader (jio/input-stream (.getBytes (get read-params "arguments") "UTF-8"))))
    ;        out-stream (ByteArrayOutputStream.)]
    ;    (case read-method
    ;      "symx-1"
    ;      ; OK, let's do this. We want to know the one-step reachable regions, ie
    ;      ; the reached pseudomodes of each successor state.
    ;      (locking z3-lock
    ;        (let [unroll-limit 5                            ; how many inert successor transitions do we reach forward to constrain t0?
    ;              lookahead-time 1000
    ;              [ha-defs ha-vals] read-args
    ;              _ (assert (nil? ha.eval/guard-memo))
    ;              z3 (z3/->z3 ha-defs {})
    ;              ; we need guards to be convex in order for the tS...t0 split to make sense! Later, use
    ;              ; quantifier instantiation where possible and forbid
    ;              ; <state sequence, quantifier choice sequence> pairs from the model
    ;              orig-defs ha-defs
    ;              ha-defs (desugar/set-initial-labels ha-defs)
    ;              ha-defs (desugar/guard-optionals-on-not-required ha-defs)
    ;              ha-defs (z3/simplify-guards ha-defs z3)
    ;              ha-defs (desugar/guard-disjunctions-to-transitions ha-defs)
    ;              ha-defs (z3/simplify-guards ha-defs z3)
    ;              z3 (z3/update-ha-defs z3 ha-defs)
    ;              _ (assert (:ha-defs z3))
    ;              entry-time (apply max (map :entry-time (vals ha-vals)))
    ;              _ (assert (nil? ha.eval/guard-memo))
    ;              [ha-vals tr-caches] (heval/init-has ha-defs (vals ha-vals) entry-time)
    ;              _ (assert (nil? ha.eval/guard-memo))
    ;              config {:objects    ha-vals
    ;                      :entry-time entry-time
    ;                      :tr-caches  tr-caches
    ;                      :inputs     #{}}
    ;              _ (println "defs" ha-defs)
    ;              _ (println "vals" ha-vals config)
    ;              [_reqs opts] (roll/next-transitions config)
    ;              _ (println "trs" (count _reqs) (count opts))
    ;              ; so for each optional transition available
    ;              times (doall
    ;                      (for [{intvl                    :interval
    ;                             {target :target
    ;                              index  :index :as edge} :transition
    ;                             ha-id                    :id :as o} opts
    ;                            :let
    ;                            [tS (iv/start intvl)
    ;                             tE (iv/end intvl)
    ;                             _ (println "opt" index tS tE)
    ;                             ha (get-in config [:objects ha-id])
    ;                             state (:state ha)
    ;                             ha-type (.-ha-type ha)
    ;                             _ (assert (:ha-defs z3))
    ;                             ; solve for values of t0 in tS...tE.
    ;                             worlds (z3/with-solver
    ;                                      z3
    ;                                      (fn [z3]
    ;                                        (assert (or (:solver z3) (:optimizer z3)))
    ;                                        (assert (:ha-defs z3))
    ;                                        (let [z3 (z3/assert-valuation! z3 (:objects config) "t00")
    ;                                              _ (assert (:has z3))
    ;                                              _ (assert (or (:solver z3) (:optimizer z3)))
    ;                                              _ (assert (:ha-defs z3))
    ;                                              z3 (z3/assert-flow-jump! z3 ha-id state edge "t0")
    ;                                              _ (assert (or (:solver z3) (:optimizer z3)))
    ;                                              z3 (z3/assert-all! z3 [[:gt "t0" "t00"]
    ;                                                                     [:geq "t0" [:+ "t00" heval/time-unit]]
    ;                                                                     [:geq "t0" tS]
    ;                                                                     [:leq "t0" (min tE (+ tS lookahead-time))]])
    ;                                              _ (assert (or (:solver z3) (:optimizer z3)))
    ;                                              base-model (z3/check! z3)
    ;                                              _ (assert (z3/model? base-model))
    ;                                              [z3 time-steps] (z3/bmc! z3 (:objects config) 1 nil)
    ;                                              time-steps (concat ["t00" "t0"] time-steps)
    ;                                              found-paths
    ;                                              (loop [found-paths []
    ;                                                     z3 z3
    ;                                                     count 0]
    ;                                                (assert (:has z3))
    ;                                                (println "constraint set ok?" found-paths count)
    ;                                                (let [here-model (ha/spy "status:" (z3/check! z3))]
    ;                                                  ; add this interval and then forbid the particular trace
    ;                                                  (if (z3/model? here-model)
    ;                                                    (let [[pcs times moves] (z3/path-constraints z3 time-steps)
    ;                                                          z3 (z3/push! z3)
    ;                                                          z3 (z3/assert-all! z3 [pcs])
    ;                                                          ;cull nogood paths from symx by checking a rollout
    ;                                                          moves (map (fn [m1 [_t-nom t]]
    ;                                                                       (assoc m1 0 t))
    ;                                                                     (butlast moves) (rest times))
    ;                                                          ;moves is a list of [time, [ha-move*]] tuples, where ha-move is [ha-id, edge] for each HA that transitions besides self-transitions
    ;                                                          _ (fipp/pprint ["rollout" moves] {:print-level 6})
    ;                                                          [status playout] (roll/fixed-playout ha-defs config moves (fn [_ _ t] t))]
    ;                                                      (if (not= :ok status)
    ;                                                        (let [;[fail-status failed-out-t ha-moves] status
    ;                                                              _a 0
    ;                                                              #_bad-step-sequence #_(map second
    ;                                                                                         (take-while (fn [[t _ts]]
    ;                                                                                                       (< t failed-out-t))
    ;                                                                                                     (zipmap time-steps move-times)))]
    ;                                                          (fipp/pprint ["spurious" status playout] {:print-level 4})
    ;                                                          ; (fipp/pprint ["bad steps" bad-step-sequence])
    ;                                                          (z3/pop! z3)
    ;                                                          ;todo: forbid the path up to and including the failed part of status.
    ;                                                          ; use bad-step-sequence!
    ;                                                          (recur found-paths
    ;                                                                 (z3/assert-all! z3 [[:not pcs]])
    ;                                                                 (inc count)))
    ;                                                        ; if it's feasible, assert the path constraints and get min/max times for each transition. have to use lex-min/max because we want to maintain the later constraints too
    ;                                                        (let [min-ts (z3/lex-min z3 (rest time-steps) 0)
    ;                                                              max-ts (z3/lex-max z3 (rest time-steps) (+ tE lookahead-time))
    ;                                                              real-moves
    ;                                                              (map (fn [m]
    ;                                                                     (assoc m
    ;                                                                       1
    ;                                                                       (map
    ;                                                                         (fn [[ha-id cur-state out-edge]]
    ;                                                                           (let [ha-type (:ha-type (get (:objects config) ha-id))]
    ;                                                                             [ha-id cur-state (get-in orig-defs [ha-type :states cur-state :edges (:initial-index out-edge)])]))
    ;                                                                         (second m))))
    ;                                                                   moves)]
    ;                                                          (println "tmin" min-ts "tmax" max-ts)
    ;                                                          (z3/pop! z3)
    ;                                                          (recur (conj found-paths [real-moves min-ts max-ts])
    ;                                                                 (z3/assert-all! z3 [[:not pcs]])
    ;                                                                 (inc count)))))
    ;                                                    found-paths)))]
    ;                                          ;break up found-intervals?
    ;                                          found-paths)))]]
    ;                        [o worlds]))]
    ;          (transit/write (ha/transit-writer out-stream)
    ;                         (ha/spy "ret" times)))))
    ;    {:status  200
    ;     :headers {"Content-Type" "application/json"}
    ;     :body    (str "\"" (string/escape (.toString out-stream) {\" "\\\""}) "\"")}))))


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
