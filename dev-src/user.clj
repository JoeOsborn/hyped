(ns user
  (:require [figwheel-sidecar.repl-api :refer :all]
            [com.georgejahad.difform :refer [difform]]
            [clj-ns-browser.sdoc :refer [sdoc]]
            [spyscope.core]
            [ha.services :as ha-serv]))

(def figwheel-config
  {:figwheel-options {:css-dirs ["resources/public/css"]}   ;; <-- figwheel server config goes here
   :build-ids        ["dev"]                                ;; <-- a vector of build ids to start autobuilding
   :all-builds                                              ;; <-- supply your build configs here
                     [{:id       "dev"
                       :source-paths ["src"]
                       :figwheel {:on-jsload "player.core/reload!"}
                       :compiler {:main                 "player.core"
                                  :asset-path           "js/compiled/out"
                                  :output-to            "resources/public/js/compiled/player.js"
                                  :output-dir           "resources/public/js/compiled/out"
                                  :source-map-timestamp true
                                  :static-fns           true
                                  }}
                      {:id       "devcards"
                       :source-paths ["src"]
                       :figwheel {:on-jsload "player.core/reload!"
                                  :devcards  true}
                       :compiler {:main                 "player.core"
                                  :asset-path           "js/compiled/devcards_out"
                                  :output-to            "resources/public/js/compiled/player_devcards.js"
                                  :output-dir           "resources/public/js/compiled/devcards_out"
                                  :source-map-timestamp true
                                  :static-fns           true
                                  }}]})

(start-figwheel! figwheel-config)

(ha-serv/start)