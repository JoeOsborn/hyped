(ns ha.services
  (:require [cognitect.transit :as transit]
            [ha.ha :as ha]
            [ha.rollout :as roll]
            [clojure.java.io :as jio]
            [clojure.string :as string]
            [ha.intervals :as iv]
            [ha.eval :as heval])
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
        (let [[ha-defs config] read-args
              [reqs opts] (roll/next-transitions config)
              req-t (if (empty? reqs)
                      Double/POSITIVE_INFINITY
                      (iv/start (:interval (first reqs))))
              ; so for each optional transition available
              (for [{intvl                    :interval
                     {target :target
                      guard  :guard
                      label  :label :as edge} :transition
                     ha-id                    :id :as o} opts
                    :let [tS (iv/start intvl)
                          tE (iv/end intvl)
                          ha (get-in config [:objects ha-id])
                          ha-def (get ha-defs (.-ha-type ha))
                          src-state (ha/current-state ha-def ha)
                          dest-state (get-in ha-def [:states target])]]
                ; solve for values of t0 in tS...tE
                (range tS tE heval/frame-length)
                )]
          (transit/write (ha/transit-writer out-stream)
                         read-args)))
      {:status  200
       :headers {"Content-Type" "application/json"}
       :body    (str "\"" (string/escape (.toString out-stream) {\" "\\\""}) "\"")}))))

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
