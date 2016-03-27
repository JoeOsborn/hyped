(defproject hyped "0.1.0-SNAPSHOT"
  :description "FIXME: write this!"
  :url "http://example.com/FIXME"
  :license {:name "MIT License"
            :url  "https://opensource.org/licenses/MIT"}

  :dependencies [[org.clojure/clojure "1.7.0"]
                 [org.clojure/clojurescript "1.7.170"]
                 [devcards "0.2.1-6"]
                 [sablono "0.3.4"]
                 [org.clojure/math.combinatorics "0.1.1"]
                 [com.microsoft/z3 "4.4.3-SNAPSHOT"]
                 [com.microsoft/z3-native "4.4.3-SNAPSHOT"]
                 [org.clojure/test.check "0.9.0"]
                 [binaryage/devtools "0.5.2"]
                 [cljsjs/react "0.14.3-0"]
                 [cljsjs/react-dom "0.14.3-1"]
                 #_[org.omcljs/om "0.8.8"]
                 #_[reagent "0.5.0"]]

  :source-paths ["src"]

  :profiles {:dev {:dependencies [[figwheel-sidecar "0.5.0-1"]
                                  [com.cemerick/piggieback "0.2.1"]
                                  [spyscope "0.1.4"]
                                  [difform "1.1.2"]
                                  [clj-ns-browser "1.3.1"]]
                   :source-paths ["dev-src"]}
             :repl {:plugins [[cider/cider-nrepl "0.10.1"]] }}

  :repl-options {:nrepl-middleware [cemerick.piggieback/wrap-cljs-repl]}

  :plugins [[lein-cljsbuild "1.1.1"]
            [lein-figwheel "0.5.0-4"]
            [lein-localrepo "0.5.3"]]

  :clean-targets ^{:protect false} ["resources/public/js/compiled"
                                    "target"]

  :cljsbuild {:builds [{:id       "dev"
                        :compiler {:main                 "player.core"
                                   :static-fns           true
                                   :asset-path           "js/compiled/out"
                                   :output-to            "resources/public/js/compiled/player.js"
                                   :output-dir           "resources/public/js/compiled/out"
                                   :source-map-timestamp true}}
                       {:id       "prod"
                        :compiler {:main          "player.core"
                                   :static-fns    true
                                   :asset-path    "js/compiled/out"
                                   :output-to     "resources/public/js/compiled/player.js"
                                   :optimizations :advanced}}]})
