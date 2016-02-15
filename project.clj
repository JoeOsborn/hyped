(defproject hyped "0.1.0-SNAPSHOT"
  :description "FIXME: write this!"
  :url "http://example.com/FIXME"
  :license {:name "MIT License"
            :url  "https://opensource.org/licenses/MIT"}

  :dependencies [[org.clojure/clojure "1.7.0"]
                 [org.clojure/clojurescript "1.7.28"]
                 [devcards "0.2.0-3"]
                 [sablono "0.3.4"]
                 [org.clojure/math.combinatorics "0.1.1"]
                 [com.microsoft/z3 "4.4.3-SNAPSHOT"]
                 [com.microsoft/z3-native "4.4.3-SNAPSHOT"]
                 [org.clojure/test.check "0.9.0"]
                 #_[org.omcljs/om "0.8.8"]
                 #_[reagent "0.5.0"]]

  :plugins [[lein-cljsbuild "1.1.0"]
            [lein-figwheel "0.4.0"]
            [lein-localrepo "0.5.3"]]

  :clean-targets ^{:protect false} ["resources/public/js/compiled"
                                    "target"]

  :source-paths ["src"]

  :cljsbuild {
              :builds [{:id           "devcards"
                        :source-paths ["src"]
                        :figwheel     {:devcards true :on-jsload "player.core/reload!"}
                        :compiler     {:main                 "player.core"
                                       :asset-path           "js/compiled/devcards_out"
                                       :output-to            "resources/public/js/compiled/player_devcards.js"
                                       :output-dir           "resources/public/js/compiled/devcards_out"
                                       :source-map-timestamp true}}
                       {:id           "dev"
                        :source-paths ["src"]
                        :figwheel     {:on-jsload "player.core/reload!"}
                        :compiler     {:main                 "player.core"
                                       :asset-path           "js/compiled/out"
                                       :output-to            "resources/public/js/compiled/player.js"
                                       :output-dir           "resources/public/js/compiled/out"
                                       :source-map-timestamp true}}
                       {:id           "prod"
                        :source-paths ["src"]
                        :compiler     {:main          "player.core"
                                       :asset-path    "js/compiled/out"
                                       :output-to     "resources/public/js/compiled/player.js"
                                       :optimizations :advanced}}]}

  :figwheel {:css-dirs ["resources/public/css"]})
