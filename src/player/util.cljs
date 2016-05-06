(ns player.util
  [:require [ha.ha :as ha :refer [make-ha make-state make-edge negate-guard kw]]
            [clojure.set :as sets]])

(defn pair [a b]
  (map (fn [ai bi] [ai bi]) a b))

(declare make-paired-states)

(defn flappy [id]
  (let [fall-acc 200
        terminal-velocity -800
        jump-speed 150
        x-speed 48]
    (make-ha id
             {:default {0 {:type #{:player}
                           :collides #{:wall}
                           :x 0 :y 0
                           :w 16 :h 16}}}
             {:x 0 :y 0
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
  (let [fall-speed 16]
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

(defn all-collider-defs [ha-def]
  (mapcat (fn [[set-id set-defs]]
            (map (fn [[cid cdef]]
                   (assoc cdef :owner (.-ha-type ha-def)
                               :collider-id cid
                               :collider-set set-id
                               :valid-states (set (keep (fn [[state-id sdef]]
                                                          (when (= (.-collider-set sdef)
                                                                   set-id)
                                                            state-id))
                                                        (.-states ha-def)))))
                 set-defs))
          (:collider-sets ha-def)))

;cartesian-product from Mark Engelberg's clojure/math.combinatorics
(defn cartesian-product
  "All the ways to take one item from each sequence"
  [& seqs]
  (let [v-original-seqs (vec seqs)
        step
        (fn step [v-seqs]
          (let [increment
                (fn [v-seqs]
                  (loop [i (dec (count v-seqs)), v-seqs v-seqs]
                    (if (= i -1) nil
                                 (if-let [rst (next (v-seqs i))]
                                   (assoc v-seqs i rst)
                                   (recur (dec i) (assoc v-seqs i (v-original-seqs i)))))))]
            (when v-seqs
              (cons (map first v-seqs)
                    (lazy-seq (step (increment v-seqs)))))))]
    (when (every? seq seqs)
      (lazy-seq (step v-original-seqs)))))


(defn split-guard [g defs wall-colliders colliders]
  ; :colliding/touching my-col-type my-side your-col-type
  ; :not-colliding/not-touching my-col-type my-side your-col-type
  ; for now, split into a disjunction over my-col, over my-side (if :any), over each member of each type in all collider sets of defs

  ; if g is an inequality, yield [g]
  ; if g is an and/or, yield (map #(apply vector :and %) (map #(split-guard % defs colliders) (rest g)))
  ; if g is a collision guard:
  (case (first g)
    ; each disjunct is recursively split, and the results are all concatenated into one set of splits
    ;  if a disjunct is not split in this way, it will still be packaged in a [] per above
    (:colliding :not-colliding
      :touching :not-touching)
    (let [[gtype my-col-type my-side your-col-type] g
          negated? (case gtype
                     (:colliding :touching) false
                     (:not-colliding :not-touching) true)
          lefty-righty? (case my-side
                          (:left :right :any) true
                          false)
          bottomy-toppy? (case my-side
                           (:bottom :top :any) true
                           false)
          all-other-colliders (sets/union (set (mapcat all-collider-defs (vals defs)))
                                          (set (vals wall-colliders)))
          my-colliders (if (= my-col-type :any)
                         (vals colliders)
                         (vals (filter #(contains? (:type %) my-col-type) colliders)))
          colliding? (case gtype
                       (:colliding :not-colliding) true
                       (:touching :not-touching) false)
          appropriate? (fn [my-coll your-type]
                         (some (sets/union (:collides my-coll)
                                           (if colliding?
                                             #{}
                                             (:touches my-coll)))
                               your-type))
          other-colliders-per-mine (into {}
                                         (if (= your-col-type :any)
                                           ; for each of my colliders, all of the other colliders
                                           (map (fn [my-coll]
                                                  [my-coll (filter #(appropriate? my-coll (:type %))
                                                                   all-other-colliders)])
                                                my-colliders)
                                           (map (fn [my-coll]
                                                  [my-coll (filter #(and (appropriate? my-coll (:type %))
                                                                         (contains? (:type %) your-col-type))
                                                                   all-other-colliders)])
                                                my-colliders)))
          collision-guards
          (vec (for [my-col (keys other-colliders-per-mine)
                     your-col (get other-colliders-per-mine my-col)]
                 (let [other (:owner your-col)
                       not-wall? (and (not= other :wall)
                                      (some? other))
                       ;narrow these tolerances based on side. if it's "my left side", pull in my right. etc.
                       pull-in 0.8
                       width-off (* (:w my-col) pull-in)
                       height-off (* (:h my-col) pull-in)
                       your-width-off (* (:w your-col) pull-in)
                       your-height-off (* (:h your-col) pull-in)
                       [left-offset right-offset bottom-offset top-offset]
                       (case my-side
                         :any [0 0 0 0]
                         :left [0 width-off 0 0]
                         :right [width-off 0 0 0]
                         :bottom [0 0 0 height-off]
                         :top [0 0 height-off 0])
                       [your-left-offset your-right-offset your-bottom-offset your-top-offset]
                       (case my-side
                         :any [0 0 0 0]
                         :left [your-width-off 0 0 0]
                         :right [0 your-width-off 0 0]
                         :bottom [0 0 your-height-off 0]
                         :top [0 0 0 your-height-off])
                       l1 [[:$self :x] (:x my-col) left-offset]
                       r1 [[:$self :x] (:x my-col) (:w my-col) (- right-offset)]
                       b1 [[:$self :y] (:y my-col) bottom-offset]
                       t1 [[:$self :y] (:y my-col) (:h my-col) (- top-offset)]
                       l2 [(when not-wall?
                             [other :x])
                           (:x your-col)
                           your-left-offset]
                       r2 [(when not-wall?
                             [other :x])
                           (:x your-col)
                           (:w your-col)
                           (- your-right-offset)]
                       b2 [(when not-wall?
                             [other :y])
                           (:y your-col)
                           your-bottom-offset]
                       t2 [(when not-wall?
                             [other :y])
                           (:y your-col)
                           (:h your-col)
                           (- your-top-offset)]
                       overlapping [:and
                                    ; mright >= oleft
                                    ; (sx+mx+mw) - (ox+yx) >= 0 -> sx-ox >= yx-mx-mw
                                    [(if lefty-righty? :geq :gt)
                                     (first r1) (first l2)
                                     (- (apply + (rest l2)) (apply + (rest r1)))]
                                    ; oright >= mleft
                                    [(if lefty-righty? :geq :gt)
                                     (first r2) (first l1)
                                     (- (apply + (rest l1)) (apply + (rest r2)))]
                                    ; mtop >= obot
                                    [(if bottomy-toppy? :geq :gt)
                                     (first t1) (first b2)
                                     (- (apply + (rest b2)) (apply + (rest t1)))]
                                    ; otop >= mbot
                                    [(if bottomy-toppy? :geq :gt)
                                     (first t2) (first b1)
                                     (- (apply + (rest b1)) (apply + (rest t2)))]]]
                   (ha/easy-simplify [:and
                                      (when not-wall?
                                        [:in-state other (:valid-states your-col)])
                                      (case my-side
                                        :any overlapping
                                        :left [:and
                                               (when colliding?
                                                 [:lt
                                                  ;vx - ovx < 0 -> vx < ovx
                                                  [:$self :v/x]
                                                  (when not-wall?
                                                    [other :v/x])
                                                  0])
                                               overlapping]
                                        :right [:and
                                                (when colliding?
                                                  [:gt
                                                   ;vx - ovx > 0 -> vx > ovx
                                                   [:$self :v/x]
                                                   (when not-wall?
                                                     [other :v/x])
                                                   0])
                                                overlapping]
                                        :bottom [:and
                                                 (when colliding?
                                                   [:lt
                                                    ;vy - ovy < 0
                                                    [:$self :v/y]
                                                    (when not-wall?
                                                      [other :v/y])
                                                    0])
                                                 overlapping]
                                        :top [:and
                                              (when colliding?
                                                [:gt
                                                 [:$self :v/y]
                                                 (when not-wall?
                                                   [other :v/y])
                                                 0])
                                              overlapping])]))))]
      (if-not negated?
        ; one guard per different collider
        collision-guards
        ; one guard containing the negation of OR any-collision
        [(ha/negate-guard (apply vector :or collision-guards))]))
    ; each conjunct is recursively split, yielding alternatives for each guard
    ;  build a new conjunction with each element of the cartesian product of seq-of-alternatives
    (:and :or :debug) (let [inner-splits (map (fn [gi] (split-guard gi defs wall-colliders colliders))
                                              (rest g))]
                        (map (fn [comb] (apply vector (first g) comb))
                             (apply cartesian-product inner-splits)))
    ; leave relations alone, wrap them in a [] to survive mapcat
    [g]))

(defn maybe-split-transition [id {g :guard :as tr} defs wall-colliders colliders]
  (let [guards (map (fn [gi] (ha/guard-replace-self-vars gi id))
                    (split-guard g defs wall-colliders colliders))]
    (map #(assoc tr :guard %) guards)))

; assumes one ha instance per ha def wiht same id and ha type
(defn expand-collision-guards [ha-defs wall-colliders]
  (ha/map-defs (fn [def]
                 (let [collider-sets (:collider-sets def)]
                   (assoc def
                     :states
                     (ha/map-states
                       (fn [state]
                         (let [colliders (get collider-sets (:collider-set state))]
                           (ha/map-transitions
                             (fn [t]
                               ; yields transition or (seq transition)
                               (maybe-split-transition (.-ha-type def)
                                                       t
                                                       (dissoc ha-defs (.-ha-type def))
                                                       wall-colliders
                                                       colliders))
                             state)))
                       def))))
               ha-defs))