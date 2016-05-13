(ns ha.sample-has
  [:require [ha.ha :as ha
             :refer [make-ha make-state make-edge negate-guard kw
                     make-paired-states]]])

(defn flappy [id]
  (let [fall-acc 200
        terminal-velocity -800
        jump-speed 150
        x-speed 48]
    (make-ha id
             {:default {0 {:type     #{:player}
                           :collides #{:wall}
                           :x        0 :y 0
                           :w        16 :h 16}}}
             {:x   0 :y 0
              :v/x 0 :v/y 0}
             :falling
             (make-state
               :falling
               :default
               nil
               {:x   x-speed :y :v/y
                :v/y [(- fall-acc) terminal-velocity]}
               (make-edge :dead
                          [:colliding :any :any :any]
                          #{:required})
               (make-edge :flapping
                          nil
                          #{[:on #{:jump}]}))
             (make-state :dead :default {:v/x 0 :v/y 0} {})
             (make-state
               :flapping
               :default
               nil
               {:x x-speed :y jump-speed}
               (make-edge :dead
                          [:colliding :any :any :any]
                          #{:required})
               (make-edge :falling
                          nil
                          #{[:off #{:jump}]})))))

(defn goomba [id speed]
  (let [fall-speed 32]
    (make-ha id                                             ;type
             {:default {0 {:type     #{:enemy}              ;collision info
                           :collides #{:wall :enemy}
                           :touches  #{:player}
                           :w        16 :h 16 :x 0 :y 0}}}
             {:x 0 :y 0}                                    ;init
             :right                                         ;start-state
             (make-state :stop :default nil {})
             ; ground movement pair
             (make-paired-states
               :left {:x (- 1)}
               :right {:x 1}
               #(make-state
                 %1                                         ;name
                 :default                                   ;colliders
                 nil                                        ;on-entry update
                 {:x speed}                                 ;flows
                 ;edges
                 (make-edge %2
                            [:colliding :any %1 :any]
                            #{:required})                   ;[:colliding my-collider my-side types]
                 (make-edge (kw :falling %1)
                            [:and
                             [:not-touching :any :bottom :wall]
                             [:not-touching :any :bottom :enemy]]
                            #{:required})))                 ;[:not-touching my-collider my-side types]
             ; air movement pair
             (make-paired-states
               :left {:x (- 1)}
               :right {:x 1}
               #(make-state
                 (kw :falling %1)                           ;name
                 :default                                   ;colliders
                 nil                                        ;on-entry update
                 {:x speed                                  ;flows
                  :y (- fall-speed)}
                 ;edges
                 (make-edge %1
                            [:colliding :any :bottom :any]
                            #{:required})
                 (make-edge (kw :falling %2)
                            [:colliding :any %1 :any]
                            #{:required}))))))

(def clear-timers {:jump-timer 0})

(defn mario [id]
  (let [fall-speed 80
        jump-speed 144
        move-speed 32
        jump-time 0.5
        min-jump-time 0.1
        ground-move-acc (/ move-speed 0.5)
        brake-acc (/ move-speed 0.5)
        air-move-acc (/ ground-move-acc 2)
        fall-acc (/ fall-speed 0.2)
        jump-gravity (/ fall-acc 2)]
    (make-ha id
             {:default {0 {:type     #{:player}
                           :collides #{:wall}
                           :touches  #{:enemy}
                           :x        0 :y 0 :w 16 :h 16}}}
             {:x          0 :y 0
              :v/x        0 :v/y 0
              :jump-timer 0}
             :idle-right
             ; ground movement and idling pairs
             (make-paired-states
               :left {:v/x -1}                              ; when used with accel states, applied to the acceleration and to the limit
               :right {}
               (fn [dir opp]
                 (vector
                   (make-state
                     (kw :idle dir)
                     :default
                     (merge clear-timers {:v/y 0})
                     {:x   :v/x
                      :v/x [(- brake-acc) 0]}
                     ;todo: look into memoizing with a key like {guard, ha1-val, ha2-val} and not throwing out memo between recalcs? maybe too much trouble.
                     ;todo: look into outputting wall-collider-choices as an OR and HA-collider-choices as a new transition (grouped by ha? or not?)
                     ; might still have some velocity in idle state, must self-transition and nix velocity in that case
                     (make-edge (kw :idle dir)
                                [:or
                                 [:colliding :any dir :wall]
                                 [:colliding :any opp :wall]]
                                #{:required}
                                {:v/x 0})
                     ;idle -> jumping in dir
                     (make-edge
                       (kw :jumping :moving dir)
                       [:and
                        [:not-touching :any dir :wall]
                        [:not-touching :any :top :wall]]
                       #{[:on #{dir :jump}]}
                       {:v/y jump-speed :jump-timer 0})
                     ;idle -> jumping in opposite dir
                     (make-edge
                       (kw :jumping :moving opp)
                       [:and
                        [:not-touching :any opp :wall]
                        [:not-touching :any :top :wall]]
                       #{[:on #{opp :jump}]}
                       {:v/y jump-speed :jump-timer 0})
                     ;idle -> jumping (ascend controlled)
                     (make-edge
                       (kw :jumping dir)
                       [:not-touching :any :top :any]
                       #{[:on #{:jump}]}
                       {:v/y jump-speed :jump-timer 0})
                     ;idle -> moving in dir
                     (make-edge
                       (kw :moving dir)
                       [:not-touching :any dir :wall]
                       #{[:on #{dir}]})
                     ;idle -> moving in opposite dir
                     (make-edge
                       (kw :moving opp)
                       [:not-touching :any opp :wall]
                       #{[:on #{opp}]})
                     ;idle -> falling
                     (make-edge
                       (kw :falling dir)
                       [:not-touching :any :bottom :wall]
                       #{:required}))
                   (make-state
                     (kw :moving dir)
                     :default
                     {:v/y 0}
                     {:x   :v/x
                      :v/x [ground-move-acc move-speed]}
                     ;moving -> stopped
                     (make-edge
                       (kw :idle dir)
                       [:or
                        [:colliding :any dir :wall]
                        [:colliding :any opp :wall]]
                       #{:required}
                       {:v/x 0})
                     ;moving -> other dir
                     (make-edge
                       (kw :moving opp)
                       [:not-touching :any opp :wall]
                       #{[:off #{dir}] [:on #{opp}]})
                     ;moving -> braking
                     (make-edge
                       (kw :idle dir)
                       nil
                       #{[:off #{dir}]})
                     ;moving -> jumping
                     (make-edge
                       (kw :jumping :moving dir)
                       nil
                       #{[:on #{:jump dir}]}
                       {:v/y jump-speed :jump-timer 0})
                     ;moving -> falling
                     (make-edge
                       (kw :falling :moving dir)
                       [:not-touching :any :bottom :wall]
                       #{:required}))
                   ; jumping
                   (make-state
                     (kw :jumping :moving dir)
                     :default
                     nil
                     {:x          :v/x
                      :v/x        [air-move-acc move-speed]
                      :y          :v/y
                      :v/y        [(- jump-gravity) 0]
                      :jump-timer 1}
                     ; hit side wall
                     (make-edge
                       (kw :jumping dir)
                       [:colliding :any dir :wall]
                       #{:required}
                       {:v/x 0})
                     ; -> falling because head bump
                     (make-edge
                       (kw :falling :moving dir)
                       [:colliding :any :top :wall]
                       #{:required}
                       {:v/y 0})
                     ;  -> falling at apex
                     (make-edge
                       (kw :falling :moving dir)
                       [:geq :jump-timer jump-time]
                       #{:required})
                     ; -> falling because of button release
                     (make-edge
                       (kw :falling :moving dir)
                       [:geq :jump-timer min-jump-time]
                       #{[:off #{:jump}]})
                     ; -> accelerate other direction
                     (make-edge
                       (kw :jumping :moving opp)
                       [:not-touching :any opp :wall]
                       #{[:off #{dir}] [:on #{opp}]})
                     ; -> stop v/x accel
                     (make-edge
                       (kw :jumping dir)
                       nil
                       #{[:off #{dir opp}]}))
                   (make-state
                     (kw :jumping dir)
                     :default
                     nil
                     {:x          :v/x
                      :v/x        0
                      :y          :v/y
                      :v/y        [(- jump-gravity) 0]
                      :jump-timer 1}
                     ; hit side wall
                     (make-edge
                       (kw :jumping dir)
                       [:colliding :any dir :wall]
                       #{:required}
                       {:v/x 0})
                     ; -> falling because head bump
                     (make-edge
                       (kw :falling dir)
                       [:colliding :any :top :wall]
                       #{:required}
                       {:v/y 0})
                     ;  -> falling at apex
                     (make-edge
                       (kw :falling dir)
                       [:geq :jump-timer jump-time]
                       #{:required})
                     ; -> falling because of button release
                     (make-edge
                       (kw :falling dir)
                       [:geq :jump-timer min-jump-time]
                       #{[:off #{:jump}]})
                     ; -> accelerate direction
                     (make-edge
                       (kw :jumping :moving dir)
                       [:not-touching :any dir :wall]
                       #{[:off #{opp}] [:on #{dir}]})
                     ; -> accelerate other direction
                     (make-edge
                       (kw :jumping :moving opp)
                       [:not-touching :any opp :wall]
                       #{[:off #{dir}] [:on #{opp}]}))
                   (make-state
                     (kw :falling :moving dir)
                     :default
                     nil
                     {:x   :v/x
                      :v/x [air-move-acc move-speed]
                      :y   :v/y
                      :v/y [(- fall-acc) (- fall-speed)]}
                     ; falling -> landed
                     (make-edge
                       (kw :moving dir)
                       [:colliding :any :bottom :wall]
                       #{:required}
                       {:v/y 0})
                     ; falling while rising -> bumped head
                     (make-edge
                       (kw :falling :moving dir)
                       [:colliding :any :top :wall]
                       #{:required}
                       {:v/y 0})
                     ; falling -> bumped wall
                     (make-edge
                       (kw :falling dir)
                       [:or
                        [:colliding :any dir :wall]
                        [:colliding :any opp :wall]]
                       #{:required}
                       {:v/x 0})
                     ; falling -> move other dir
                     (make-edge
                       (kw :falling :moving opp)
                       [:not-touching :any opp :wall]
                       #{[:off #{dir}] [:on #{opp}]})
                     ; falling -> stop moving
                     (make-edge
                       (kw :falling dir)
                       nil
                       #{[:off #{dir opp}]}))
                   (make-state
                     (kw :falling dir)
                     :default
                     nil
                     {:x   :v/x
                      :v/x 0
                      :y   :v/y
                      :v/y [(- fall-acc) (- fall-speed)]}
                     ; falling -> landed
                     (make-edge
                       (kw :idle dir)
                       [:colliding :any :bottom :wall]
                       #{:required}
                       {:v/y 0})
                     ; falling while rising -> bumped head
                     (make-edge
                       (kw :falling dir)
                       [:colliding :any :top :wall]
                       #{:required}
                       {:v/y 0})
                     ; falling -> bumped wall (may have residual velocity, so self-transition
                     (make-edge
                       (kw :falling dir)
                       [:or
                        [:colliding :any dir :wall]
                        [:colliding :any opp :wall]]
                       #{:required}
                       {:v/x 0})
                     ; falling -> move dir/opp
                     (make-edge
                       (kw :falling :moving dir)
                       [:not-touching :any dir :wall]
                       #{[:off #{opp}] [:on #{dir}]})
                     (make-edge
                       (kw :falling :moving opp)
                       [:not-touching :any opp :wall]
                       #{[:off #{dir}] [:on #{opp}]}))))))))