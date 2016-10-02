(defproject hyped "0.2.0-SNAPSHOT"
  :description "FIXME: write this!"
  :url "http://example.com/FIXME"
  :license {:name "MIT License"
            :url  "https://opensource.org/licenses/MIT"}
  ; :pedantic? :abort
  :dependencies [[org.clojure/clojure "1.9.0-alpha13"]
                 [org.clojure/clojurescript "1.9.229"]
                 [fipp "0.6.6"]
                 [devcards "0.2.2"]
                 [cljsjs/react "15.3.1-0"]
                 [cljsjs/react-dom "15.3.1-0"]
                 [sablono "0.7.4"]
                 [org.clojure/math.combinatorics "0.1.3"]
                 ;lein localrepo install .../z3/bin/com.microsoft.z3.jar com.microsoft/z3 4.4.2-SNAPSHOT
                 ;cp .../z3/bin/{libz3java.dylib,libz3.dylib,libz3.a} native/macosx/x86_64/
                 ;jar -cMf com.microsoft.z3-native.jar native
                 ;lein localrepo install .../z3/bin/com.microsoft.z3-native.jar com.microsoft/z3-native 4.4.2-SNAPSHOT
                 [com.microsoft/z3 "4.4.2-SNAPSHOT"]
                 [com.microsoft/z3-native "4.4.2-SNAPSHOT"]
                 [org.clojure/test.check "0.9.0"]
                 [binaryage/devtools "0.8.2"]
                 [compojure "1.5.1"]
                 [ring "1.5.0"]
                 [ring-server "0.4.0"]
                 [org.clojure/core.async "0.2.391"]
                 [com.cognitect/transit-clj "0.8.290"]
                 [com.cognitect/transit-cljs "0.8.239"]
                 [servant "0.1.5"]
                 [cljs-http "0.1.41"]]

  :source-paths ["src"]

  :profiles {:dev  {:dependencies [[figwheel-sidecar "0.5.8"]
                                   [com.cemerick/piggieback "0.2.1"]
                                   [difform "1.1.2"]]
                    :source-paths ["src"]}
             :repl {:plugins      [[cider/cider-nrepl "0.13.0"]]
                    :source-paths ["src" "dev-src"]}}

  :repl-options {:nrepl-middleware [cemerick.piggieback/wrap-cljs-repl]}

  :plugins [[lein-cljsbuild "1.1.4"]
            [lein-localrepo "0.5.3"]
            [lein-figwheel "0.5.8" :exclusions [org.clojure/clojure]]
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
