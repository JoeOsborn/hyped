(ns player.ui
  (:require [sablono.core :as sab]))

(def segmented-control
  (let [props (fn [this] (aget (.-props this) "args"))
        c
        (.createClass js/React
                      #js {:shouldComponentUpdate
                           (fn [next-props _next-state]
                             (this-as this
                               (not= (aget next-props "args") (props this))))
                           :render
                           (fn []
                             (this-as this
                               (let [[label options selected-key on-change] (props this)]
                                 (sab/html [:div
                                            [:p label]
                                            (map
                                              (fn [{name :name type :type key :key prototype :prototype :as o}]
                                                [:button
                                                 {:style   {:backgroundColor (if (= selected-key key)
                                                                               "#4479BA"
                                                                               "#CCCCCC")}
                                                  :onClick (fn [_evt]
                                                             (println type prototype)
                                                             (on-change o))}
                                                 name])
                                              options)]))))})
        f (.createFactory js/React c)]
    (fn [& args]
      (f #js {:args args}))))


(defn input-changer [atm label key update-fn! itype value-reader get-fn]
  (let [keyp (if (coll? key)
               key
               [key])
        keywordy? (and atm (keyword? (get-in @atm keyp)))]
    (sab/html
      [:div {:style {:width 170 :display "inline-block" :fontSize "12px"}}
       [:label {:key   (str keyp "-label")
                :style {:width "95%"}} label]
       [:input {:type        itype
                :style       {:width "95%"}
                :key         (str keyp "-field")
                :disabled    (nil? atm)
                :value       (when atm
                               (let [v (get-fn @atm keyp)]
                                 (if keywordy?
                                   (name v)
                                   v)))
                :onChange    (fn [evt]
                               (when atm
                                 (let [new-v (.-value (.-target evt))]
                                   (update-fn! atm keyp (value-reader (if keywordy?
                                                                        (keyword new-v)
                                                                        new-v))))))
                :placeholder (when (nil? atm)
                               "---")}]])))

(defn text-changer
  ([atm label key update-fn!] (text-changer atm label key update-fn! get-in))
  ([atm label key update-fn! get-fn]
   (input-changer atm label key update-fn! "text" identity get-fn)))

(defn num-changer
  ([atm label key update-fn!] (num-changer atm label key update-fn! get-in))
  ([atm label key update-fn! get-fn]
   (input-changer atm label key update-fn! "number" (fn [v] (.parseInt js/window v)) get-fn)))