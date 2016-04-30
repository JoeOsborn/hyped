(ns player.util
  [:require [ha.ha :as ha :refer [make-ha make-state make-edge negate-guard kw]]
            [ha.ha-eval :as heval]
            [clojure.set :as sets]])

(defn pair [a b]
  (map (fn [ai bi] [ai bi]) a b))

(declare make-paired-states bumping-transitions unsupported-guard non-bumping-guard)

(defn goomba [id speed]
  (let [fall-speed 16]
    (make-ha id                                             ;type
             {:default {0 {:type     #{:enemy}              ;collision info
                           :collides #{:wall :enemy}
                           :overlaps #{:player}
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
                            [:colliding :any %1 :any]
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
             {:default {0 {:type #{:player}
                           :x    0 :y 0 :w 0 :h 0}}}
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
  ; :colliding/overlapping my-col-type my-side your-col-type
  ; :not-colliding/not-overlapping my-col-type my-side your-col-type
  ; for now, split into a disjunction over my-col, over my-side (if :any), over each member of each type in all collider sets of defs

  ; if g is an inequality, yield [g]
  ; if g is an and/or, yield (map #(apply vector :and %) (map #(split-guard % defs colliders) (rest g)))
  ; if g is a collision guard:
  (case (first g)
    ; each disjunct is recursively split, and the results are all concatenated into one set of splits
    ;  if a disjunct is not split in this way, it will still be packaged in a [] per above
    (:colliding :not-colliding
      :overlapping :not-overlapping)
    (let [[gtype my-col-type my-side your-col-type] g
          negated? (case gtype
                     (:colliding :overlapping) false
                     (:not-colliding :not-overlapping) true)
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
          useful-key (case gtype
                       (:colliding :not-colliding) :collides
                       (:overlapping :not-overlapping) :overlaps)
          other-colliders-per-mine (into {}
                                         (if (= your-col-type :any)
                                           ; for each of my colliders, all of the other colliders
                                           (map (fn [my-coll]
                                                  [my-coll (filter #(some (get my-coll useful-key)
                                                                          (:type %))
                                                                   all-other-colliders)])
                                                my-colliders)
                                           (map (fn [my-coll]
                                                  [my-coll (filter #(and (some (get my-coll useful-key)
                                                                               (:type %))
                                                                         (contains? (:type %)
                                                                                    your-col-type))
                                                                   all-other-colliders)])
                                                my-colliders)))
          collision-guards
          (vec (for [my-col (keys other-colliders-per-mine)
                     your-col (get other-colliders-per-mine my-col)]
                 (let [other (:owner your-col)
                       not-wall? (and (not= other :wall)
                                      (some? other))
                       ;narrow these tolerances based on side. if it's "my left side", pull in my right. etc.
                       width-off (* (:w my-col) 0.75)
                       height-off (* (:h my-col) 0.75)
                       your-width-off (* (:w your-col) 0.75)
                       your-height-off (* (:h your-col) 0.75)
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
                                               [:or
                                                [:leq [:$self :v/x] 0]
                                                (when not-wall?
                                                  [:geq [other :v/x] 0])]
                                               overlapping]
                                        :right [:and
                                                [:or
                                                 [:geq [:$self :v/x] 0]
                                                 (when not-wall?
                                                   [:leq [other :v/x] 0])]
                                                overlapping]
                                        :bottom [:and
                                                 [:or
                                                  [:leq [:$self :v/y] 0]
                                                  (when not-wall?
                                                    [:geq [other :v/y] 0])]
                                                 overlapping]
                                        :top [:and
                                              [:or
                                               [:geq [:$self :v/y] 0]
                                               (when not-wall?
                                                 [:leq [other :v/y] 0])]])]))))]
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