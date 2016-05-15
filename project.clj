(defproject hyped "0.1.0-SNAPSHOT"
  :description "FIXME: write this!"
  :url "http://example.com/FIXME"
  :license {:name "MIT License"
            :url  "https://opensource.org/licenses/MIT"}
  ; :pedantic? :abort
  :dependencies [[org.clojure/clojure "1.8.0"]
                 [org.clojure/clojurescript "1.8.51"]
                 [devcards "0.2.1-6"]
                 [cljsjs/react "0.14.3-0"]
                 [cljsjs/react-dom "0.14.3-1"]
                 [sablono "0.3.4"]
                 [org.clojure/math.combinatorics "0.1.1"]
                 [com.microsoft/z3 "4.4.3-SNAPSHOT"]
                 [com.microsoft/z3-native "4.4.3-SNAPSHOT"]
                 [org.clojure/test.check "0.9.0"]
                 [binaryage/devtools "0.5.2"]
                 [compojure "1.5.0"]
                 [ring "1.4.0"]
                 [ring-server "0.4.0"]
                 [org.clojure/core.async "0.2.374"]
                 [com.cognitect/transit-clj "0.8.285"]
                 [com.cognitect/transit-cljs "0.8.237"]
                 [servant "0.1.5"]
                 [cljs-http "0.1.40"]
                 #_[org.omcljs/om "0.8.8"]
                 #_[reagent "0.5.0"]]

  :source-paths ["src"]

  :profiles {:dev  {:dependencies [[figwheel-sidecar "0.5.3-1"]
                                   [com.cemerick/piggieback "0.2.1"]
                                   [difform "1.1.2"]]
                    :source-paths ["src"]}
             :repl {:plugins      [[cider/cider-nrepl "0.10.1"]]
                    :source-paths ["src" "dev-src"]}}

  :repl-options {:nrepl-middleware [cemerick.piggieback/wrap-cljs-repl]}

  :plugins [[lein-cljsbuild "1.1.3"]
            [lein-localrepo "0.5.3"]
            [lein-figwheel "0.5.3-1" :exclusions [org.clojure/clojure]]
            [lein-ring "0.9.7" :exclusions [org.clojure/clojure]]]

  :ring {:handler ha.services/services}

  :clean-targets ^{:protect false} ["resources/public/js/compiled"
                                    "target"]

  :cljsbuild {:builds [{:id           "dev"
                        :source-paths ["src"]
                        :compiler     {:main                 "player.core"
                                       :static-fns           true
                                       :asset-path           "js/compiled/out"
                                       :output-to            "resources/public/js/compiled/player.js"
                                       :output-dir           "resources/public/js/compiled/out"
                                       :source-map-timestamp true}}
                       {:id           "services-dev"
                        :source-paths ["src"]
                        :compiler     {:main                 "player.explore-service"
                                       :pretty-print false
                                       :optimizations :simple
                                       :static-fns           true
                                       :asset-path           "js/compiled/explore_service_out"
                                       :output-to            "resources/public/js/compiled/explore_service.js"
                                       :output-dir           "resources/public/js/compiled/explore_service_out"
                                       :source-map-timestamp true}}
                       {:id           "prod"
                        :source-paths ["src"]
                        :compiler     {:main          "player.core"
                                       :static-fns    true
                                       :asset-path    "js/compiled/out"
                                       :output-to     "resources/public/js/compiled/player.js"
                                       :optimizations :advanced}}]})
