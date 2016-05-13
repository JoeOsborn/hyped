(ns player.seen-viz-ui
  (:require [clojure.set :as sets]
            [sablono.core :as sab]
            [ha.ha :as ha]))

(defn clip [a b c]
  (max a (min b c)))

(defn path-str [h [_ha-id _ha-state {x :x y :y :as v0} flow duration]]
  ; poly-spec is an ha ID, an initial valuation, a flow, and a duration
  (let [{x' :x y' :y} (ha/extrapolate-flow v0 flow [:x :y] duration)
        cx (clip -1000 (+ x 8) 1000)
        cy (clip -1000 (- h (+ y 8)) 1000)
        cx' (clip -1000 (+ x' 8) 1000)
        cy' (clip -1000 (- h (+ y' 8)) 1000)]
    (str "M " cx "," cy " L " cx' "," cy')))

(defn clear-canvas [c]
  (let [ctx (.getContext c "2d")]
    (.clearRect ctx 0 0 (.-width c) (.-height c))))

(defn redraw-polys [canvas h polys]
  (println "redraw polys" (count polys))
  (let [ctx (.getContext canvas "2d")]
    (set! (.-strokeStyle ctx) "rgb(200,255,200)")
    (set! (.-lineWidth ctx) 16)
    (.beginPath ctx)
    (doseq [[_ha-id _ha-state v0 flow duration] polys
            :let [points [0 0.25 0.5 0.75 1.0]
                  xyi (map #(ha/extrapolate-flow v0 flow [:x :y] (* duration %)) points)
                  cxyi (map (fn [{x :x y :y}]
                              {:x (clip -1000 (+ x 8) 1000)
                               :y (clip -1000 (- h (+ y 8)) 1000)})
                            xyi)]]
      (.moveTo ctx (:x (first cxyi)) (:y (first cxyi)))
      (doseq [{x :x y :y} cxyi]
        (.lineTo ctx x y)))
    (.stroke ctx)))

(def seen-viz
  (let [props (fn [this] (aget (.-props this) "args"))
        draw-new (fn [prev-props _prev-state]
                   (this-as this
                     (let [canvas (.getDOMNode this)
                           [world-w world-h _ _ polys-per-ha] (props this)
                           [old-world-w old-world-h _ _ old-polys-per-ha] (aget (or prev-props
                                                                                    #js [nil nil nil nil {}])
                                                                                "args")]
                       (println "draw new")
                       (when (or (not= world-w old-world-w)
                                 (not= world-h old-world-h)
                                 (not= (keys polys-per-ha) (keys old-polys-per-ha))
                                 (< (reduce + 0 (map count (vals polys-per-ha)))
                                    (reduce + 0 (map count (vals old-polys-per-ha)))))
                         (clear-canvas canvas))
                       (doseq [[id polys] polys-per-ha
                               :let [old-polys (get old-polys-per-ha id)
                                     pset (set polys)
                                     opset (set old-polys)
                                     new-ones (sets/difference pset opset)]
                               :when (not (empty? new-ones))]
                         (redraw-polys canvas world-h new-ones)))))
        c
        (.createClass js/React
                      #js {:shouldComponentUpdate
                           (fn [next-props _next-state]
                             (this-as this
                               (not= (props this) (aget next-props "args"))))
                           :componentDidMount
                           draw-new
                           :componentDidUpdate
                           draw-new
                           :render
                           (fn []
                             (this-as this
                               (let [[world-w world-h x-scale y-scale _polys] (props this)]
                                 (sab/html [:canvas {:width world-w :height world-h
                                                     :style {:position "absolute"
                                                             :left     0 :top 0
                                                             :width (* world-w x-scale) :height (* world-h y-scale)
                                                             :opacity 0.5}}]))))})
        f (.createFactory js/React c)]
    (fn [& args]
      (f #js {:args args}))))

#_(defn seen-viz [world-h polys]
    [:g {:key "seen-viz"}
     (map (fn [poly]
            [:path {:key   (str poly)
                    :d     (path-str world-h poly)
                    :style {:strokeWidth 16 :stroke "rgba(200,255,200,0.25)"}}])
          polys)])
