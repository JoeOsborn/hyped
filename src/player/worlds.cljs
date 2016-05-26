(ns player.worlds
  [:require [ha.ha :as ha]
            [ha.desugar :as desugar]
            [ha.sample-has :as sample-has]
            [ha.rollout :as roll]
            [ha.eval :as heval]])


(defn current-config [world]
  (last (:configs world)))

(defn world-append [world config]
  (let [new-configs (if (>= (:entry-time config)
                            (:entry-time (current-config world)))
                      (conj (:configs world) config)
                      (vec (concat (filter (fn [c]
                                             (<= (:entry-time c) (:entry-time config)))
                                           (:configs world))
                                   [config])))]
    (assoc world :configs new-configs
                 :now (:entry-time config))))

(defn reset-world [params w]
  (let [init-config (heval/recache-trs (:ha-defs w)
                                       (first (:configs w)))]
    (reduce world-append
            (assoc w :now 0
                     :playing (:play-on-start params)
                     :configs [init-config])
            #_(first (roll/stabilize-config init-config))
            []
            #_(roll/fixed-moves-playout (:ha-defs w)
                                       init-config
                                       [[:m :moving-left heval/time-unit]
                                        [:m :moving-right (* 20 heval/time-unit)]
                                        [:m :idle-right (* 60 heval/time-unit)]
                                        #_[:m :moving-right 10.0]]))))

(defn make-world [params world-desc]
  (let [wall-colliders (into {}
                             (map (fn [[k wall-desc]]
                                    [k (assoc wall-desc :type #{:wall}
                                                        :owner :wall)])
                                  (:walls world-desc)))
        defs (ha/define-has
               (map (fn [[id {type :type}]]
                      (case type
                        :goomba (sample-has/goomba id 16)
                        :mario (sample-has/mario id)
                        :flappy (sample-has/flappy id)
                        :simple-camera (sample-has/goomba id 16)))
                    (:objects world-desc)))
        ; this assumes one HA per HA-def
        defs (desugar/expand-collision-guards defs wall-colliders)
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
                     :tr-caches  tr-caches}]
    (reset-world params
                 (merge {:playing         false
                         :pause-on-change false}
                        params
                        {:desc          world-desc
                         :ha-defs       defs
                         :scroll-x      (:scroll-x world-desc)
                         :scroll-y      (:scroll-y world-desc)
                         :camera-width  (:camera-width world-desc)
                         :camera-height (:camera-height world-desc)
                         :width         (:width world-desc)
                         :height        (:height world-desc)
                         :now           0
                         :configs       [init-config]
                         :seen-polys    {}
                         :seen-configs  #{}
                         :view-width    320
                         :view-height   240}))))

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

(defn world->desc [w]
  (let [ha-defs (:ha-defs w)
        walls (:walls (:desc w))
        now (:now w)
        ha-vals (map (fn [[_ v]]
                       (ha/extrapolate (get ha-defs (.-ha-type v))
                                       v
                                       now))
                     (:objects (current-config w)))]
    (merge (select-keys w [:scroll-x :scroll-y
                           :camera-width :camera-height
                           :width :height])
           {:objects (into {}
                           (map (fn [{type  :ha-type
                                      id    :id
                                      state :state
                                      v0    :v0}]
                                  [id (merge
                                        {:type  type
                                         :state state}
                                        v0)])
                                ha-vals))
            :walls   walls})))