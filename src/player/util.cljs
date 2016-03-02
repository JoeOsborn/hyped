(ns player.util
  [:require [ha.ha :as ha :refer [make-ha make-state make-edge
                                  make-paired-states kw
                                  bumping-transitions
                                  unsupported-guard non-bumping-guard]]
            [player.ha-eval :as heval]])

(defn goomba [id speed others walls]
  (let [others (disj others id :m)
        fall-speed 16]
    (make-ha id                                             ;type
             {:x     0 :y 0                                 ;init
              :w     16 :h 16}
             :right
             (make-state :stop nil {})
             ; ground movement pair
             (make-paired-states
               :left {:x (- 1)}
               :right {:x 1}
               #(make-state
                 %1                                         ;name
                 nil                                        ;on-entry update
                 {:x speed}                                 ;flows
                 ;edges
                 (bumping-transitions id %2 %2 nil walls others heval/precision)
                 ; If nobody is under my new position, enter falling-right
                 #_(make-edge
                   (kw :falling %1)
                   (unsupported-guard 16 16 walls others)
                   #{:required})))
             ; air movement pair
             (make-paired-states
               :left {:x (- 1)}
               :right {:x 1}
               #(make-state
                 (kw :falling %1)                           ;name
                 nil                                        ;on-entry update
                 {:x speed :y (- fall-speed)}               ;flows
                 ;edges
                 (bumping-transitions id :top %1 nil walls others heval/precision)
                 (bumping-transitions id %2 (kw :falling %2) nil walls others heval/precision)
                 (bumping-transitions id %2 :top %2 nil walls others heval/precision)
                 )))))

(def clear-timers {:jump-timer 0})

(defn mario [id others walls]
  (let [stand-others #{} #_(disj others id)
        wall-others #{}
        fall-speed 80
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
             {:x          0 :y 0
              :v/x        0 :v/y 0
              :w          16 :h 16
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
                     (merge clear-timers {:v/y 0})
                     {:x   :v/x
                      :v/x [(- brake-acc) 0]}
                     ; might still have some velocity in idle state, must self-transition and nix velocity in that case
                     (bumping-transitions id dir (kw :idle dir)
                                          (if (= dir :left)
                                            [:gt :v/x 0]
                                            [:lt :v/x 0])
                                          walls wall-others
                                          heval/precision)
                     (bumping-transitions id opp (kw :idle dir)
                                          (if (= dir :left)
                                            [:lt :v/x 0]
                                            [:gt :v/x 0])
                                          walls wall-others
                                          heval/precision)
                     ;idle -> jumping in dir
                     (make-edge
                       (kw :jumping :moving dir)
                       (non-bumping-guard opp walls wall-others heval/precision)
                       #{[:on #{dir :jump}]}
                       {:v/y jump-speed :jump-timer 0})
                     ;idle -> jumping in opposite dir
                     (make-edge
                       (kw :jumping :moving opp)
                       (non-bumping-guard dir walls wall-others heval/precision)
                       #{[:on #{opp :jump}]}
                       {:v/y jump-speed :jump-timer 0})
                     ;idle -> jumping (ascend controlled)
                     (make-edge
                       (kw :jumping dir)
                       nil
                       #{[:on #{:jump}]}
                       {:v/y jump-speed :jump-timer 0})
                     ;idle -> moving in dir
                     (make-edge
                       (kw :moving dir)
                       (non-bumping-guard opp walls wall-others heval/precision)
                       #{[:on #{dir}]})
                     ;idle -> moving in opposite dir
                     (make-edge
                       (kw :moving opp)
                       (non-bumping-guard dir walls wall-others heval/precision)
                       #{[:on #{opp}]})
                     ;idle -> falling
                     (make-edge
                       (kw :falling dir)
                       (unsupported-guard 16 16 walls stand-others)
                       #{:required}))
                   (make-state
                     (kw :moving dir)
                     {:v/y 0}
                     {:x   :v/x
                      :v/x [ground-move-acc move-speed]}
                     ;moving -> stopped
                     (bumping-transitions id dir (kw :idle dir)
                                          (if (= dir :left)
                                            [:gt :v/x 0]
                                            [:lt :v/x 0])
                                          walls wall-others
                                          heval/precision)
                     (bumping-transitions id opp (kw :idle dir)
                                          (if (= dir :left)
                                            [:lt :v/x 0]
                                            [:gt :v/x 0])
                                          walls wall-others
                                          heval/precision)
                     ;moving -> other dir
                     (make-edge
                       (kw :moving opp)
                       nil
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
                       (unsupported-guard 16 16 walls stand-others)
                       #{:required}))
                   ; jumping
                   (make-state
                     (kw :jumping :moving dir)
                     nil
                     {:x          :v/x
                      :v/x        [air-move-acc move-speed]
                      :y          :v/y
                      :v/y        [(- jump-gravity) 0]
                      :jump-timer 1}
                     ; hit side wall
                     (bumping-transitions id dir (kw :jumping dir)
                                          (if (= dir :left)
                                            [:gt :v/x 0]
                                            [:lt :v/x 0])
                                          walls wall-others
                                          heval/precision)
                     (bumping-transitions id opp (kw :jumping dir)
                                          (if (= dir :left)
                                            [:lt :v/x 0]
                                            [:gt :v/x 0])
                                          walls wall-others
                                          heval/precision)
                     ; -> falling because head bump
                     (bumping-transitions id :bottom (kw :falling :moving dir)
                                          nil
                                          walls wall-others
                                          heval/precision)
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
                       (non-bumping-guard dir walls wall-others heval/precision)
                       #{[:off #{dir}] [:on #{opp}]})
                     ; -> stop v/x accel
                     (make-edge
                       (kw :jumping dir)
                       nil
                       #{[:off #{dir opp}]}))
                   (make-state
                     (kw :jumping dir)
                     nil
                     {:x          :v/x
                      :v/x        0
                      :y          :v/y
                      :v/y        [(- jump-gravity) 0]
                      :jump-timer 1}
                     ; hit side wall
                     (bumping-transitions id dir (kw :jumping dir)
                                          (if (= dir :left)
                                            [:gt :v/x 0]
                                            [:lt :v/x 0])
                                          walls wall-others
                                          heval/precision)
                     (bumping-transitions id opp (kw :jumping dir)
                                          (if (= dir :left)
                                            [:lt :v/x 0]
                                            [:gt :v/x 0])
                                          walls wall-others
                                          heval/precision)
                     ; -> falling because head bump
                     #_(bumping-transitions id :bottom (kw :falling dir) nil walls wall-others)
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
                       (non-bumping-guard opp walls wall-others heval/precision)
                       #{[:off #{opp}] [:on #{dir}]})
                     ; -> accelerate other direction
                     (make-edge
                       (kw :jumping :moving opp)
                       (non-bumping-guard dir walls wall-others heval/precision)
                       #{[:off #{dir}] [:on #{opp}]}))
                   (make-state
                     (kw :falling :moving dir)
                     nil
                     {:x   :v/x
                      :v/x [air-move-acc move-speed]
                      :y   :v/y
                      :v/y [(- fall-acc) (- fall-speed)]}
                     ; falling -> landed
                     (bumping-transitions id :top (kw :moving dir)
                                          nil
                                          walls wall-others
                                          heval/precision)
                     ; falling while rising -> bumped head
                     (bumping-transitions id :bottom (kw :falling :moving dir)
                                          nil
                                          walls wall-others
                                          heval/precision)
                     ; falling -> bumped wall
                     (bumping-transitions id :left (kw :falling dir)
                                          [:gt :v/x 0]
                                          walls wall-others
                                          heval/precision)
                     (bumping-transitions id :right (kw :falling dir)
                                          [:lt :v/x 0]
                                          walls wall-others
                                          heval/precision)
                     ; falling -> move other dir
                     (make-edge
                       (kw :falling :moving opp)
                       (non-bumping-guard dir walls wall-others heval/precision)
                       #{[:off #{dir}] [:on #{opp}]})
                     ; falling -> stop moving
                     (make-edge
                       (kw :falling dir)
                       nil
                       #{[:off #{dir opp}]}))
                   (make-state
                     (kw :falling dir)
                     nil
                     {:x   :v/x
                      :v/x 0
                      :y   :v/y
                      :v/y [(- fall-acc) (- fall-speed)]}
                     ; falling -> landed
                     (bumping-transitions id :top (kw :idle dir)
                                          nil
                                          walls wall-others
                                          heval/precision)
                     ; falling while rising -> bumped head
                     (bumping-transitions id :bottom (kw :falling dir)
                                          nil
                                          walls wall-others
                                          heval/precision)
                     ; falling -> bumped wall (may have residual velocity, so self-transition
                     (bumping-transitions id :left (kw :falling dir)
                                          [:gt :v/x 0]
                                          walls wall-others
                                          heval/precision)
                     (bumping-transitions id :right (kw :falling dir)
                                          [:lt :v/x 0]
                                          walls wall-others
                                          heval/precision)
                     ; falling -> move dir/opp
                     (make-edge
                       (kw :falling :moving dir)
                       (non-bumping-guard opp walls wall-others heval/precision)
                       #{[:off #{opp}] [:on #{dir}]})
                     (make-edge
                       (kw :falling :moving opp)
                       (non-bumping-guard dir walls wall-others heval/precision)
                       #{[:off #{dir}] [:on #{opp}]}))))))))