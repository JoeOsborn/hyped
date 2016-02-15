(ns player.core
  (:require
    #_[om.core :as om :include-macros true]
    [clojure.string :as string]
    #_[clojure.walk :as walk]
    [sablono.core :as sab :include-macros true]
    [ha.intervals :as iv]
    [player.ha-eval :as heval]
    [ha.ha :as ha :refer [make-ha make-state make-edge
                          make-paired-states kw
                          bumping-transitions
                          unsupported-guard non-bumping-guard]]
    [player.ha-rollout :as roll]
    [player.util :as util])
  (:require-macros
    [devcards.core :refer [defcard deftest]]
    [player.macros :refer [soft-assert]]))

(enable-console-print!)

(declare reset-world!)
(defn reload! [_]
  (reset-world!))

(defn debug-shown-transitions [ha]
  [(first (:required-transitions ha))])

(set! heval/frame-length (/ 1 30))
(set! heval/time-units-per-frame 10000)
(set! heval/time-unit (/ heval/frame-length heval/time-units-per-frame))
(set! heval/precision 0.01)

(defonce world (atom {}))
(defonce last-time nil)

(defn make-world [] (let [ids #{
                                  :ga :gb :gc :gd :ge
                                  :m
                                  }
                            walls #{[0 0 256 8]
                                    [0 8 8 16]
                                    [96 8 8 16]
                                    [160 8 8 16]}
                            objects [
                                     (util/goomba :ga 8 8 16 :right ids walls)
                                     (util/goomba :gb 32 8 16 :right ids walls)
                                     (util/goomba :gc 12 35 16 :falling-right ids walls)
                                     (util/goomba :gd 64 8 16 :left ids walls)
                                     (util/goomba :ge 96 32 16 :right ids walls)
                                     (util/mario :m 200 64 (kw :falling :right) ids walls)]
                            obj-dict (heval/init-has objects)]
                      {:now             0
                       :playing         false
                       :pause-on-change false
                       :configs         [{:entry-time 0 :inputs #{} :objects obj-dict}]
                       :walls           walls}))

(defn current-config [world]
  (last (:configs world)))

(defn world-append [world config]
  (let [new-configs (if (>= (:entry-time config) (:entry-time (current-config world)))
                      (conj (:configs world) config)
                      (vec (concat (filter (fn [c] (<= (:entry-time c) (:entry-time config)))
                                           (:configs world))
                                   [config])))]
    (assoc world :configs new-configs
                 :now (:entry-time config))))

(defn ha-states [world]
  (let [has (sort-by :id (vals (:objects (current-config world))))]
    (map (fn [ha] [(:id ha) (:state ha)]) has)))

(def key-states (atom {:on       #{}
                       :pressed  #{}
                       :released #{}}))

(defn reset-world! []
  (swap! key-states (fn [_] {:on #{} :pressed #{} :released #{}}))
  (swap! world (fn [_]
                   (make-world))))

(def keycode->keyname
  {37 :left
   39 :right
   38 :up
   40 :down
   90 :run
   88 :jump})

(defn key-handler [evt]
  (let [key (keycode->keyname (.-keyCode evt))
        down? (= (.-type evt) "keydown")]
    (when key
      (println "KH" (.-keyCode evt) key down?)
      (.preventDefault evt)
      (.-stopPropagation evt)
      (swap! key-states (fn [{prev-on :on pressed :pressed released :released :as k}]
                          ; need the extra contains? check so key-repeat doesn't confuse things.
                          (let [just-pressed? (and down?
                                                   (not (contains? prev-on key)))]
                            (assoc k :on (if down? (conj prev-on key)
                                                   (disj prev-on key))
                                     :pressed (if just-pressed?
                                                (conj pressed key)
                                                pressed)
                                     :released (if down?
                                                 released
                                                 (conj released key)))))))))

(set! (.-onkeydown js/window) key-handler)
(set! (.-onkeyup js/window) key-handler)

(defn tick-frame [t]
  (when-not last-time (set! last-time t))
  (assert (>= t last-time) "Non-monotonic time?")
  (let [old-last-time last-time]
    (set! last-time t)
    (.requestAnimationFrame js/window tick-frame)
    (when (:playing @world)
      (swap! world
             (fn [w] (let [c (current-config w)
                           new-now (+ (:now w) (/ (- t old-last-time) 1000))
                           new-c (heval/update-config c
                                                      new-now
                                                      ; assume all keys held now were held since "then"
                                                      [[(:now w) new-now] @key-states]
                                                      100
                                                      0)
                           new-w (if (not= c new-c)
                                   (world-append w new-c)
                                   w)
                           new-w (assoc new-w :now new-now)]
                       (swap! key-states (fn [ks] (assoc ks :pressed #{} :released #{})))
                       (if (and (:pause-on-change new-w)
                                (not= c new-c))
                         (assoc new-w :playing false)
                         new-w)))))))

(when (= @world {})
  (.requestAnimationFrame js/window tick-frame)
  (reset-world!))

(def show-transition-thresholds true)

(defn world-widget [world _owner]
  (let [scale 2
        view-h (str (* scale 240) "px")
        has (:objects (current-config @world))
        ct (count has)
        line-h (/ (* scale 240) ct)]
    (sab/html [:div {:style {:backgroundColor "blue"
                             :width           (str (* scale 320) "px")
                             :height          view-h
                             :position        "relative"
                             :overflow        "hidden"}}
               (when show-transition-thresholds
                 (map (fn [{w :w h :h :as ha}]
                        (when (not (empty? (:required-transitions ha)))
                          [:div
                           (map (fn [trans]
                                  (let [[s _e] (iv/first-subinterval (:interval trans))
                                        ha-s (ha/extrapolate ha s)
                                        sx (* scale (:x ha-s))
                                        sy (* scale (:y ha-s))]
                                    [:div {:style {:width           (str (* scale w) "px") :height (str (* scale h) "px")
                                                   :borderRadius    (str (* scale w) "px")
                                                   :backgroundColor "rgba(165,42,42,0.5)"
                                                   :position        "absolute"
                                                   :left            (str sx "px")
                                                   :bottom          (str sy "px")}}]))
                                (debug-shown-transitions ha))]))
                      (vals has)
                      (range 0 ct))) (map (fn [[x y w h]]
                                            [:div {:style {:width           (str (* scale w) "px") :height (str (* scale h) "px")
                                                           :backgroundColor "white"
                                                           :position        "absolute"
                                                           :left            (str (* scale x) "px")
                                                           :bottom          (str (* scale y) "px")}}])
                                          (:walls @world))
               (map (fn [{x :x y :y w :w h :h :as ha}]
                      [:div
                       [:div {:style {:width           (str (* scale w) "px") :height (str (* scale h) "px")
                                      :borderRadius    (str (* scale w) "px")
                                      :backgroundColor "brown"
                                      :position        "absolute"
                                      :color           "lightgray"
                                      :left            (str (* scale x) "px")
                                      :bottom          (str (* scale y) "px")}}
                        [:div {:style {:width "200px"}}
                         (str (:id ha) " " (:state ha))]]])
                    (map #(ha/extrapolate % (:now @world)) (vals has)))
               (when show-transition-thresholds
                 (map (fn [ha]
                        [:div
                         (when (not (empty? (:required-transitions ha)))
                           (map (fn [trans]
                                  (let [[s e] (iv/first-subinterval (:interval trans))
                                        ha-s (ha/extrapolate ha s)
                                        ha-e (ha/extrapolate ha e)
                                        sx (* scale (:x ha-s))
                                        ex (* scale (:x ha-e))
                                        sy (* scale (:y ha-s))
                                        ey (* scale (:y ha-e))]
                                    [:div {:style {:height          (.max js/Math (.abs js/Math (- sy ey)) 8)
                                                   :width           (.max js/Math (.abs js/Math (- sx ex)) 8)
                                                   :bottom          (.min js/Math sy ey)
                                                   :left            (.min js/Math sx ex)
                                                   :position        "absolute"
                                                   :backgroundColor "grey"
                                                   :pointerEvents   "none"}}
                                     [:div {:style {:position        "absolute"
                                                    :width           "200px"
                                                    :backgroundColor "rgba(255,255,255,0.5)"
                                                    :pointerEvents   "none"}}
                                      (str (:id ha) "-" (:target (:transition trans)))]
                                     [:div {:style {:height          "100%"
                                                    :width           "2px"
                                                    :position        "absolute"
                                                    :left            (if (< sx ex) "0%" "100%")
                                                    :backgroundColor "green"
                                                    :pointerEvents   "none"}}]
                                     [:div {:style {:height          "100%"
                                                    :width           "2px"
                                                    :position        "absolute"
                                                    :left            (if (< sx ex) "100%" "0%")
                                                    :backgroundColor "red"
                                                    :pointerEvents   "none"}}]]))
                                (debug-shown-transitions ha)))])
                      (vals has)
                      (range 0 ct)))
               [:button {:onClick #(swap! world (fn [w] (assoc w :playing (not (:playing w)))))}
                (if (:playing @world) "PAUSE" "PLAY")]
               [:span {:style {:backgroundColor "lightgrey"}} "Pause on state change?"
                [:input {:type     "checkbox"
                         :checked  (:pause-on-change @world)
                         :onChange #(swap! world (fn [w] (assoc w :pause-on-change (.-checked (.-target %)))))}]]
               [:button {:onClick #(reset-world!)} "RESET"]
               [:button {:onClick #(swap! world (fn [w] (let [new-configs (butlast (:configs w))
                                                              c (last new-configs)]
                                                          (assoc w :now (:entry-time c)
                                                                   :configs new-configs))))
                         :disabled (= 1 (count (:configs @world)))}
                "BACK"]
               [:button {:onClick #(swap! world (fn [w] (let [[configs m] (roll/random-playout (current-config w) 1)
                                                              c (last configs)]
                                                          (println "random move:" m)
                                                          (world-append w c))))}
                "RANDOM MOVE"]
               [:span {:style {:backgroundColor "lightgrey"}} (str (:now @world))]])))

(defcard draw-world
         world-widget
         world)

(defonce last-world nil)

(defn rererender [target]
  (when (not= @world last-world)
    (js/React.render (world-widget world nil) target))
  (.requestAnimationFrame js/window #(rererender target)))

(defn main []
  ;; conditionally start the app based on whether the #main-app-area
  ;; node is on the page
  (if-let [node (.getElementById js/document "main-app-area")]
    (.requestAnimationFrame js/window #(rererender node))))

(main)
