(ns ha.services
  (:require [ring.adapter.jetty :as jetty]
            [castra.core :refer [defrpc]]
            [castra.middleware :as cmw]))

(defn fallback [_req]
  {:status 404 :body "not found"})

(def services (-> fallback (cmw/wrap-castra 'ha.services)))

(defonce server (jetty/run-jetty #'services {:join? false :port 4445}))

(defn start [] (.start server))
(defn stop  [] (.stop server))
