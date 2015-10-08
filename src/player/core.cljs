(ns player.core
  (:require
    #_[om.core :as om :include-macros true]
    [sablono.core :as sab :include-macros true])
  (:require-macros
    [devcards.core :as dc :refer [defcard deftest]]))

(enable-console-print!)

(defn now [] (/ (.now js/Date) 1000))

(defn next-transition-ha [obj then]
  {:time Infinity})

(defn sample-ha [ha then now]
  (let [nt (next-transition-ha ha then)
        t-now (:time nt)]
    (if (>= now t-now)
      ;for correctness, would have to transition and then sample the result
      {:jumped nt}

      (let [s (:state ha)
            flows (:flows (get ha s))
            delta (- now then)
            new-vals (map (fn [[variable flow]]
                            [variable (+ (get ha variable) (* flow delta))])
                          flows)]
        (apply assoc ha (flatten new-vals))))))

#_(defn next-transition-ha [ha then]
    (let [s (:state ha)
          flows (:flows (get ha s))
          guards (map)
          new-vals (map (fn [[variable flow]]
                          )
                        flows)]
      (apply assoc ha new-vals)))

(defn make-ha [id init & states]
  (merge (assoc {:id id} :entry-time (now))
         init
         (zipmap (map :id states) states)))

; edge label is a set containing :required | button masks
(defn make-edge [target guard label]
  (assert (every? #(#{:gt :geq :leq :lt} (first %)) guard) "Guard must be a list of difference formulae.")
  {:target target :guard guard :label label})

(defn invert-guard [g]
  (case (first g)
    :gt (assoc g 0 :leq)
    :geq (assoc g 0 :lt)
    :leq (assoc g 0 :gt)
    :lt (assoc g 0 :geq)))

(defn make-state [id flows & edges]
  (let [edge-guards (map :guard (filter #(:required (:label %)) edges))]
    ; invariant is a disjunction of negated guards
    {:id id :flows flows :edges edges :invariant (map #(map invert-guard %) edge-guards)}))

(defonce scene-a (atom {}))
(defonce playing false)
(defonce last-time nil)
(defn reset-scene-a! []
  (swap! scene-a (fn [_] {:now     (now)
                          :then    (now)
                          :playing false
                          :objects [(make-ha :a             ;id
                                             {:x     8 :y 8 ;init
                                              :w     16 :h 16
                                              :state :right}
                                             (make-state :right ;name
                                                         {:x 1} ;flows
                                                         ;edges
                                                         (make-edge :left [[:geq :x 64]] #{:required}))
                                             (make-state :left ;name
                                                         {:x -1} ;flows
                                                         ;edges
                                                         (make-edge :right [[:leq :x 8]] #{:required})))]})))
(defn tick-frame [t]
  (when-not last-time (set! last-time t))
  (when (:playing @scene-a)
    (swap! scene-a
           (fn [s] (update s :now (fn [old-now]
                                    (+ old-now (/ (- t last-time) 1000)))))))
  (set! last-time t)
  (.requestAnimationFrame js/window tick-frame))
(when (= @scene-a {})
  (.requestAnimationFrame js/window tick-frame)
  (reset-scene-a!)
  )

; add reset button and sample button

(defcard draw-scene
         (fn [scene owner]
           (sab/html [:div {:style {:backgroundColor "blue" :width "320px" :height "240px" :position "relative"}}
                      (map (fn [{x :x y :y w :w h :h}]
                             [:div {:style {:width           (str w "px") :height (str h "px") :borderRadius (str w "px")
                                            :backgroundColor "brown"
                                            :position        "absolute" :left (str x "px") :bottom (str y "px")}}])
                           (map #(sample-ha % (:then @scene) (:now @scene)) (:objects @scene)))
                      [:button {:onClick #(do (swap! scene (fn [s] (assoc s :playing (not (:playing s))))) true)} (if (:playing @scene) "PAUSE" "PLAY")]
                      [:button {:onClick #(reset-scene-a!)} "RESET"]]))
         scene-a)

(defcard sample-time
         "What are the current values of the variables of object a?"
         (fn [scene owner]
           [(:then @scene)
            (:now @scene)
            (sample-ha (get-in @scene [:objects 0]) (get-in @scene [:then]) (get-in @scene [:now]))])
         scene-a)

#_(defcard next-transition
           "When and what is the next transition of object a?"
           (fn [scene owner]
             (next-transition-ha (get-in @scene [:objects :a]) (get-in @scene [:then])))
           scene-a)

(defn main []
  ;; conditionally start the app based on wether the #main-app-area
  ;; node is on the page
  (if-let [node (.getElementById js/document "main-app-area")]
    (js/React.render (sab/html [:div "This is working"]) node)))

(main)

;; remember to run lein figwheel and then browse to
;; http://localhost:3449/cards.html

