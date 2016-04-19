(ns player.worlds
  [:require [ha.ha :as ha]
            [player.util :as util]
            [player.ha-rollout :as roll]
            [player.ha-eval :as heval]])


(defn current-config [world]
  (last (:configs world)))

(defn world-append [world config]
  (let [new-configs (if (>= (:entry-time config)
                            (:entry-time (current-config world)))
                      (conj (:configs world) config)
                      (vec (concat (filter (fn [c]
                                             (<= (:entry-time c) (:entry-time config)))
                                           (:configs world))
                                   [config])))
        new-seen (roll/see-config (:seen-configs world) config)]
    (assoc world :configs new-configs
                 :seen-configs new-seen
                 :explored #{}
                 :now (:entry-time config))))

(defn reset-world [params w]
  (let [world-desc (:desc w)
        defs (:ha-defs w)
        [obj-dict tr-caches] (heval/init-has
                               defs
                               (map (fn [[id {state :state :as ha-desc}]]
                                      (let [v0 (dissoc ha-desc :id :type :state)]
                                        (ha/init-ha (get defs id)
                                                    id
                                                    state
                                                    0
                                                    v0)))
                                    (:objects world-desc))
                               0)
        init-config {:entry-time 0
                     :inputs     #{}
                     :objects    obj-dict
                     :tr-caches  tr-caches}
        _ (assert (not (empty? (:required-transitions (:m tr-caches)))))]
    (reduce world-append
            (assoc w :now 0
                     :playing (:play-on-start params)
                     :configs [init-config]
                     :seen-configs (roll/see-config (:seen-configs w) init-config))
            [
             #_(roll/next-config defs init-config)
             ]
            #_(first (roll/stabilize-config init-config))
            #_(first (roll/fixed-playout init-config
                                         [[:m :jumping-right 0.5]
                                          [:m :moving-right 3.0]
                                          [:m :idle-right 3.75]
                                          [:m :jumping-right 6.0]
                                          #_[:m :moving-right 10.0]])))))

(defn make-world [params world-desc]
  (let [ids (set (keys (:objects world-desc)))
        walls (set (map (fn [[_k {x :x y :y w :w h :h}]]
                          [x y w h])
                        (:walls world-desc)))
        defs (ha/define-has
               (map (fn [[id {type :type}]]
                      (case type
                        :goomba (util/goomba id 16 ids walls)
                        :mario (util/mario id ids walls)
                        :simple-camera (util/goomba id 16 ids walls)))
                    (:objects world-desc)))]
    (reset-world params
                 (merge {:playing         false
                         :pause-on-change false}
                        params
                        {:desc          world-desc
                         :ha-defs       defs
                         :now           0
                         :configs       []
                         :seen-configs  #{}
                         :seen-polys    {}
                         :scroll-x      (:scroll-x world-desc)
                         :scroll-y      (:scroll-y world-desc)
                         :camera-width  (:camera-width world-desc)
                         :camera-height (:camera-height world-desc)
                         :view-width    320
                         :view-height   240
                         :width         (:width world-desc)
                         :height        (:height world-desc)
                         :walls         walls}))))

; remake ha defs from desc, then translate old valuations into new world def.
; we need to translate all the old configs into the new domain, which will be
; lossy but may be convenient. the seen configs/polys/regions/etc will still be
; wrong, so it's not clear how helpful it is, except for stuff like "try
; something, change the level, go back, try again". which is definitely a useful
; case! so let's do that.
(defn update-object-vals [old-defs new-defs
                          old-init
                          old-vals new-vals
                          t]
  (into {}
        (map
          (fn [[k v]]
            (let [v (assoc v :entry-time t)
                  new-type (.-ha-type v)
                  old-val (get old-vals k)
                  old-init (get old-init k)
                  old-type (when old-val
                             (.-ha-type old-val))
                  old-def (when old-val
                            (get old-defs old-type))
                  old-val (when old-val
                            (ha/extrapolate old-def old-val t))
                  old-at-init? (if old-val
                                 (= (.-v0 old-val)
                                    (.-v0 old-init))
                                 true)
                  ; if the old val was at the initial valuation,
                  ; then moving the initial valuation should update the old val.
                  old-val (if old-at-init?
                            nil
                            old-val)
                  old-state (when old-val
                              (.-state old-val))
                  new-def (get new-defs new-type)
                  relevant-vals (when old-val
                                  (select-keys (.-v0 old-val)
                                               (keys (.-v0 v))))]
              [k (cond
                   ; if no old val, leave it alone
                   (nil? old-val)
                   v
                   ; if the old val's state is still valid in the new desc,
                   ; copy over the state and the v0
                   (and (= old-type new-type)
                        (contains? (.-states new-def) old-state))
                   (assoc v :v0 (merge (.-v0 v) relevant-vals)
                            :state old-state)
                   ; if the old val's state is no longer valid or if the
                   ; type has changed, try to copy over the valuation
                   :else
                   (assoc v :v0 (merge (.-v0 v) relevant-vals)))]))
          new-vals)))

(defn reenter-current-config [w]
  (let [now (ha/floor-time (:now w) heval/time-unit)
        defs (:ha-defs w)
        reenter-config (update
                         (assoc (current-config w) :entry-time now)
                         :objects
                         (fn [os]
                           (into
                             {}
                             (map (fn [[k v]]
                                    [k (ha/extrapolate (get defs (.-ha-type v))
                                                       v
                                                       now)])
                                  os))))]
    (if (not= reenter-config (current-config w))
      (world-append w (assoc reenter-config :tr-caches nil))
      w)))

(defn world-update-desc [w desc]
  (if (= desc (:desc w))
    w
    (let [w (reenter-current-config w)
          old-defs (:ha-defs w)
          new-world (make-world {} desc)
          new-defs (:ha-defs new-world)
          new-vals (:objects (current-config new-world))
          old-init-vals (:objects (first (:configs w)))
          _ (println "world-update-desc")
          w (assoc w :ha-defs new-defs
                     :desc desc
                     :walls (:walls new-world)
                     :seen-polys {}
                     :explored #{}
                     :seen-configs #{}
                     :width (:width desc)
                     :height (:height desc))
          w (update w
                    :configs
                    (fn [cfgs]
                      (mapv
                        (fn [{old-vals :objects t :entry-time :as cfg}]
                          (assoc cfg :objects (update-object-vals old-defs
                                                                  new-defs
                                                                  old-init-vals
                                                                  old-vals
                                                                  new-vals
                                                                  t)
                                     :tr-caches nil))
                        cfgs)))]
      (world-append (update w :configs #(subvec % 0 (dec (count %))))
                    (heval/recache-trs new-defs (current-config w))))))

