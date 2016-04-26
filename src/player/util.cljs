(ns player.util
  [:require [ha.ha :as ha :refer [make-ha make-state make-edge negate-guard kw]]
            [ha.ha-eval :as heval]])

(defn pair [a b]
  (map (fn [ai bi] [ai bi]) a b))

(declare make-paired-states bumping-transitions unsupported-guard non-bumping-guard)

(defn goomba [id speed]
  (let [fall-speed 16]
    (make-ha id                                             ;type
             {:default {0 {:type     #{:enemy}              ;collision info
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
                            [:not-colliding :any :bottom :any]
                            #{:required})))                 ;[:not-colliding my-collider my-side types]
             ; air movement pair
             (make-paired-states
               :left {:x (- 1)}
               :right {:x 1}
               #(make-state
                 (kw :falling %1)                           ;name
                 :default                                   ;colliders
                 nil                                        ;on-entry update
                 {:x speed :y (- fall-speed)}               ;flows
                 ;edges
                 (make-edge %1
                            [:colliding :any :bottom :any]
                            #{:required})
                 (make-edge (kw :falling %2)
                            [:colliding :any %2 :any]
                            #{:required}))))))

(def clear-timers {:jump-timer 0})

(defn mario [id walls]
  (let [stand-others #{}
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
             {:default {0 {:type     #{:player}
                           :x        0 :y 0 :w 0 :h 0}}}
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
                     :default
                     (merge clear-timers {:v/y 0})
                     {:x   :v/x
                      :v/x [(- brake-acc) 0]}
                     ; might still have some velocity in idle state, must self-transition and nix velocity in that case
                     (bumping-transitions id dir (kw :idle dir)
                                          nil
                                          walls wall-others
                                          heval/precision)
                     (bumping-transitions id opp (kw :idle dir)
                                          nil
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
                     :default
                     {:v/y 0}
                     {:x   :v/x
                      :v/x [ground-move-acc move-speed]}
                     ;moving -> stopped
                     (bumping-transitions id dir (kw :idle dir)
                                          nil
                                          walls wall-others
                                          heval/precision)
                     (bumping-transitions id opp (kw :idle dir)
                                          nil
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
                     :default
                     nil
                     {:x          :v/x
                      :v/x        [air-move-acc move-speed]
                      :y          :v/y
                      :v/y        [(- jump-gravity) 0]
                      :jump-timer 1}
                     ; hit side wall
                     (bumping-transitions id dir (kw :jumping dir)
                                          nil
                                          walls wall-others
                                          heval/precision)
                     (bumping-transitions id opp (kw :jumping dir)
                                          nil
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
                     :default
                     nil
                     {:x          :v/x
                      :v/x        0
                      :y          :v/y
                      :v/y        [(- jump-gravity) 0]
                      :jump-timer 1}
                     ; hit side wall
                     (bumping-transitions id dir (kw :jumping dir)
                                          nil
                                          walls wall-others
                                          heval/precision)
                     (bumping-transitions id opp (kw :jumping dir)
                                          nil
                                          walls wall-others
                                          heval/precision)
                     ; -> falling because head bump
                     (bumping-transitions id :bottom (kw :falling dir)
                                          nil
                                          walls wall-others
                                          heval/precision)
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
                     :default
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
                                          nil
                                          walls wall-others
                                          heval/precision)
                     (bumping-transitions id :right (kw :falling dir)
                                          nil
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
                     :default
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
                                          nil
                                          walls wall-others
                                          heval/precision)
                     (bumping-transitions id :right (kw :falling dir)
                                          nil
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

(defn moving-inc [vbl width other-ha]
  [:and
   [:lt vbl [other-ha vbl] (+ (- width) (/ 16 4))]
   [:geq vbl [other-ha vbl] (- width)]])

(defn moving-dec [vbl width other-ha]
  [:and
   ; vbl > o.vbl
   ; vbl - o.vbl > 0
   [:gt vbl [other-ha vbl] (/ width 4)]
   ; vbl <= o.vbl + ow
   ; vbl - o.vbl <= ow
   [:leq vbl [other-ha vbl] width]])

(defn between-c [vbl min max]
  [:and
   ; vbl >= min --> vbl >= min
   [:geq vbl min]
   ; vbl <= max --> vbl <= max
   [:leq vbl max]])

(defn between [vbl dim other-ha other-dim]
  ; vbl  >= other-ha.vbl - dim && vbl < other-ha.vbl + other-dim
  ; vbl - other-ha.vbl >= - dim && vbl - other-ha.vbl < other-dim
  [:and
   [:geq vbl [other-ha vbl] (list '- dim)]
   [:leq vbl [other-ha vbl] other-dim]])

(defn conj-if-some [v elt]
  (if (some? elt)
    (conj v elt)
    v))

(defn bumping-guard [dir other precision consider-velocity?]
  (let [main-vbl (case dir (:left :right) :x (:top :bottom) :y)
        vel (keyword "v" (name main-vbl))
        sub-vbl (case main-vbl :x :y :y :x)
        increasing? (case dir (:left :bottom) true (:right :top) false)
        const? (not (keyword? other))
        width 16
        height 16
        [ox oy ow oh] (if const? other [[other :x] [other :y] width height])
        dim (case main-vbl :x width :y height)
        omain (case main-vbl :x ox :y oy)
        osub (case sub-vbl :x ox :y oy)
        odim (case main-vbl :x ow :y oh)
        sub-dim (case sub-vbl :x width :y height)
        sub-odim (case sub-vbl :x ow :y oh)]
    (cond
      (and const? increasing?)
      (conj-if-some
        [:and
         (between-c main-vbl (- omain dim) (- omain (* dim 0.75)))
         (between-c sub-vbl (- osub sub-dim (- precision)) (+ osub sub-odim (- precision)))]
        (when consider-velocity? [:gt vel 0]))
      increasing?
      (conj-if-some
        [:and
         (moving-inc main-vbl width other)
         (between sub-vbl (- sub-dim precision) other (- sub-odim precision))]
        (when consider-velocity? [:gt vel 0]))
      const?
      (conj-if-some
        [:and
         (between-c main-vbl (+ omain (* odim 0.75)) (+ omain odim))
         (between-c sub-vbl (- osub sub-dim (- precision)) (+ osub sub-odim (- precision)))]
        (when consider-velocity? [:lt vel 0]))
      :else
      (conj-if-some
        [:and
         (moving-dec main-vbl width other)
         (between sub-vbl (- sub-dim precision) other (- sub-odim precision))]
        (when consider-velocity? [:lt vel 0])))))

(defn bumping-transitions
  ([id dir next-state extra-guard walls other-has precision]
   (map (fn [other]
          (let [bump-guard (bumping-guard dir other precision true)
                guard (if extra-guard
                        [:and bump-guard extra-guard]
                        bump-guard)]
            (make-edge next-state guard
                       #{:required [:this id] [:other other]}
                       {(case dir (:left :right) :v/x (:top :bottom) :v/y) 0})))
        (concat walls other-has)))
  ([id dir1 dir2 next-state extra-guard walls other-has precision]
   (mapcat (fn [o1 o2]
             (if (= o1 o2)
               []
               (let [b1 (bumping-guard dir1 o1 precision true)
                     b2 (bumping-guard dir2 o2 precision true)
                     guard (if extra-guard
                             [:and b1 b2 extra-guard]
                             [:and b1 b2])]
                 [(make-edge next-state guard
                             #{:required [:this id] [:other o1] [:other o2]}
                             {:v/x 0 :v/y 0})])))
           (concat walls other-has)
           (concat walls other-has))))

(defn unsupported-guard [w h walls others]
  (apply vector :and
         (concat
           ; currently unsupported
           (map (fn [other]
                  (if (keyword? other)
                    (let [ow w
                          oh h]
                      [:or
                       ; position.x + width < other.x
                       ; i.e. x+w < ox i.e. x - ox < - w
                       [:leq :x [other :x] (- w)]
                       ; position.x is > other.x + other.w
                       ; i.e. x > ox+ow i.e. x - ox > ow
                       [:geq :x [other :x] ow]
                       ; position.y + height is < other.y
                       [:leq :y [other :y] (- h)]
                       ; position.y is > other.y + other.h
                       [:gt :y [other :y] oh]])
                    (let [[ox oy ow oh] other]
                      [:or
                       ; position.x + width < other.x
                       ; i.e. x+w < ox i.e. x < ox - w
                       [:leq :x (- ox w)]
                       ; position.x is > other.x + other.w
                       ; i.e. x > ox+ow i.e. x > ox+ow
                       [:geq :x (+ ox ow)]
                       ; position.y + height is < other.y --> position.y < other.y - h
                       [:leq :y (- oy h)]
                       ; position.y is > other.y + other.h
                       [:gt :y (+ oy oh)]])))
                (concat walls others)))))

(defn non-bumping-guard [dir walls others precision]
  (negate-guard
    (apply vector :or (map (fn [o] (bumping-guard dir o precision false))
                           (concat walls others)))))

(defn scale-flows [states multipliers]
  (map (fn [state]
         (update state :flows
                 (fn [flow]
                   (if (empty? multipliers)
                     flow
                     (reduce (fn [flow [k v]]
                               (update flow
                                       k
                                       (if (ha/deriv-var? k)
                                         (fn [old-acc]
                                           (cond
                                             (nil? old-acc) 0
                                             (vector? old-acc) (mapv #(* %1 v) old-acc)
                                             :else (* old-acc v)))
                                         (fn [old-acc]
                                           (* old-acc v)))))
                             flow
                             multipliers)))))
       states))

(defn make-paired-states [a af b bf func]
  (let [a-states (flatten [(func a b)])
        a-states (scale-flows a-states af)
        b-states (flatten [(func b a)])
        b-states (scale-flows b-states bf)]
    (println "flipped" af (map :flows a-states) bf (map :flows b-states))
    (apply vector (concat a-states b-states))))