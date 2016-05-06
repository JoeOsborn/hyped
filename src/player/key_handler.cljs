(ns player.key-handler)

(def key-states- (atom {}))

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
      ;(println "KH" (.-keyCode evt) key down?)
      (.preventDefault evt)
      (.stopPropagation evt)
      (swap! key-states- (fn [{prev-on :on pressed :pressed released :released :as k}]
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

(defn key-states []
  @key-states-)

(defn clear-keys! []
  (reset! key-states- {:on #{} :pressed #{} :released #{}}))

(defn clear-pressed! []
  (swap! key-states- (fn [ks]
                       (assoc ks :pressed #{} :released #{}))))

(def handlers-installed false)

(defn install-handlers! []
  (when-not handlers-installed
    (set! handlers-installed true)
    (set! (.-onkeydown js/window) key-handler)
    (set! (.-onkeyup js/window) key-handler)))