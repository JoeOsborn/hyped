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

(declare reset-scene-a!)
(defn reload! [_]
  (reset-scene-a!))

(defn debug-shown-transitions [ha]
  [(first (:required-transitions ha))])

(set! heval/frame-length (/ 1 30))
(set! heval/time-units-per-frame 10000)
(set! heval/time-unit (/ heval/frame-length heval/time-units-per-frame))
(set! heval/precision 0.01)

(defonce scene-a (atom {}))
(defonce last-time nil)



(defn make-scene-a [] (let [ids #{
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
                         :then            0
                         :playing         false
                         :pause-on-change false
                         :objects         obj-dict
                         :walls           walls}))

(defn ha-states [scene]
  (let [has (sort-by :id (vals (:objects scene)))]
    (map (fn [ha] [(:id ha) (:state ha)]) has)))

(def key-states (atom {:on       #{}
                       :pressed  #{}
                       :released #{}}))

(defn reset-scene-a! []
  (swap! key-states (fn [_] {:on #{} :pressed #{} :released #{}}))
  (swap! scene-a (fn [_]
                   (make-scene-a))))

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
    (when (:playing @scene-a)
      (swap! scene-a
             (fn [s] (let [new-now (+ (:now s) (/ (- t old-last-time) 1000))
                           new-s (heval/update-scene s
                                                     new-now
                                                     ; assume all keys held now were held since "then"
                                                     @key-states
                                                     100
                                                     0)]
                       (swap! key-states (fn [ks] (assoc ks :pressed #{} :released #{})))
                       (if (and (:pause-on-change new-s)
                                (not= (ha-states s) (ha-states new-s)))
                         (assoc new-s :playing false)
                         new-s)))))))

(when (= @scene-a {})
  (.requestAnimationFrame js/window tick-frame)
  (reset-scene-a!))

#_(defcard sample-time
           "What are the current values of the variables of object a?"
           (fn [scene _owner]
             [(:now @scene)
              (extrapolate (get-in @scene [:objects :a]) (get-in @scene [:now]))])
           scene-a)

#_(defcard ha-deps
           (fn [scene _owner]
             [(ha-dependencies (get-in @scene [:objects :a])) (ha-dependencies (get-in @scene [:objects :b]))])
           scene-a)

#_(defcard interval-list-ops
           (fn [data-atom _]
             (let [{data :data good :good text :text} @data-atom]
               (sab/html [:div
                          [:input {:type      "text"
                                   :style     {:background-color (if good "inherit" "red")
                                               :width            "100%"}
                                   :value     text
                                   :on-change #(swap! data-atom (fn [d]
                                                                  (let [new-text (.-value (.-target %))
                                                                        d (assoc d :text new-text)
                                                                        new-data (try (reader/read-string new-text)
                                                                                      (catch :default _e nil))]
                                                                    (if new-data
                                                                      (assoc d :data new-data :good true)
                                                                      (assoc d :good false)))))}]
                          [:br]
                          (when good
                            [:div
                             [:label (str "Intersections: " (map (fn [di]
                                                                   (map (fn [dj]
                                                                          (str di "," dj ":" (intersection di dj)))
                                                                        data))
                                                                 data))]
                             [:br]
                             [:label (str "Intersect: " (intersect-all data))]
                             [:br]
                             [:label (str "Union: " (union-all data))]])])))
           {:data [[0 1] [2 3]]
            :text "[[0 1] [2 3]]"
            :good true})


#_(defcard ha-states-card
           (fn [scene _owner]
             (ha-states @scene))
           scene-a)

(def show-transition-thresholds true)

(defn scene-widget [scene _owner]
  (let [scale 2
        view-h (str (* scale 240) "px")
        ct (count (:objects @scene))
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
                      (vals (:objects @scene))
                      (range 0 ct))) (map (fn [[x y w h]]
                                            [:div {:style {:width           (str (* scale w) "px") :height (str (* scale h) "px")
                                                           :backgroundColor "white"
                                                           :position        "absolute"
                                                           :left            (str (* scale x) "px")
                                                           :bottom          (str (* scale y) "px")}}])
                                          (:walls @scene))
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
                    (map #(ha/extrapolate % (:now @scene)) (vals (:objects @scene))))
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
                      (vals (:objects @scene))
                      (range 0 ct)))
               [:button {:onClick #(swap! scene (fn [s] (assoc s :playing (not (:playing s)))))}
                (if (:playing @scene) "PAUSE" "PLAY")]
               [:span {:style {:backgroundColor "lightgrey"}} "Pause on state change?"
                [:input {:type     "checkbox"
                         :checked  (:pause-on-change @scene)
                         :onChange #(swap! scene (fn [s] (assoc s :pause-on-change (.-checked (.-target %)))))}]]
               [:button {:onClick #(reset-scene-a!)} "RESET"]
               [:button {:onClick #(swap! scene (fn [s] (let [[scenes m] (roll/random-playout s 1)
                                                              s (last scenes)]
                                                          (println "random move:" m)
                                                          s)))}
                "RANDOM MOVE"]
               [:span {:style {:backgroundColor "lightgrey"}} (str (:now @scene))]])))

(defcard draw-scene
         scene-widget
         scene-a)

#_(defcard ha-data
           (fn [scene _owner]
             (let [objs (:objects @scene)
                   cleanup (fn [t-int]
                             (update t-int
                                     :transition
                                     (fn [t]
                                       (dissoc t :update :guard))))
                   desc (map (fn [[id ha]]
                               [:div
                                (str id)
                                [:div "Required transitions:" (str (map cleanup
                                                                        (transition-intervals
                                                                          objs
                                                                          ha
                                                                          Infinity
                                                                          (required-transitions ha))))]
                                [:div "Optional transitions:" (str (map cleanup
                                                                        (transition-intervals
                                                                          objs
                                                                          ha
                                                                          Infinity
                                                                          (optional-transitions ha))))]])
                             objs)]
               (sab/html [:div desc])))
           scene-a)

#_(defcard next-transition
           "When and what is the next transition of object a?"
           (fn [scene owner]
             (next-transition-ha (get-in @scene [:objects :a]) (get-in @scene [:then])))
           scene-a)

(defonce last-scene-a nil)

(defn rererender [target]
  (when (not= @scene-a last-scene-a)
    (js/React.render (scene-widget scene-a nil) target))
  (.requestAnimationFrame js/window #(rererender target)))

(defn main []
  ;; conditionally start the app based on whether the #main-app-area
  ;; node is on the page
  (if-let [node (.getElementById js/document "main-app-area")]
    (.requestAnimationFrame js/window #(rererender node))))

(main)
