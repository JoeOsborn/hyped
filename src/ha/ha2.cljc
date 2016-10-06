(ns ha.ha2
  (:require [clojure.spec :as s]
            [clojure.spec.gen :as gen]
            [clojure.string :as string]
            [clojure.set :as sets]
            [clojure.walk :as walk]))

;;todo: function make-ha that takes a ha spec, conforms it, and then produces records(?)

(defn ident-string-gen []
  ;;todo this is to avoid generating variables named :- or whatever, and hopefully not :input or something
  (gen/bind (gen/tuple (gen/char-alpha)
                       (gen/string))
            #(gen/return (str (first %) (second %)))))
(defn name-gen []
  (gen/fmap keyword (ident-string-gen)))
(defn var-name-gen []
  (gen/bind (ident-string-gen)
            #(gen/one-of [(gen/return (keyword %))
                          (gen/return (keyword (str % "'")))
                          (gen/return (keyword (str % "''")))])))
(s/def ::var-name (s/with-gen simple-keyword? var-name-gen))
(s/def ::var-lookup (s/and
                     (s/or
                      ::var ::var-name
                      ::ref (s/cat ::ref ::var-name
                                   ::var ::var-name))
                     (s/conformer
                      (fn [[t v]]
                        (if (= t ::var)
                          {::ref ::self
                           ::var v}
                          v))
                      (fn [{ref ::ref var ::var}]
                        (if (= ref ::self)
                          var
                          [ref var])))))

(s/def ::var (s/or
              ::lookup ::var-lookup
              ::local (s/and keyword?
                             #(= (namespace %) :?))))

(s/def ::relation #{:< :<= := :>= :>})
(s/def ::input-name keyword?)
(s/def ::input-guard
  (s/cat ::op #{:input}
         ::input ::input-name
         ::input-state
         (s/or ::button #{:on :off :pressed :released}
               ::axis (s/cat ::rel ::relation
                             ::threshold (s/and number?
                                                #(<= -1 % 1))))))
(s/def ::body-tag simple-keyword?)
(defn normal? [[x y]]
  (== (+ (* x x) (* y y)) 1.0))
(defn rect-normal-gen []
  (s/gen #{[-1 0] [1 0] [0 1] [0 -1]}))
(defn unit-vector [dir]
  [(Math/cos dir) (Math/sin dir)])
(defn free-normal-gen []
  (gen/fmap #(unit-vector %)
            (s/double-in :min 0
                         :max (* 2 Math/PI)
                         :NaN? false
                         :infinite? false)))
(s/def ::collision-normal
  (s/with-gen
    (s/and (s/tuple number? number?)
           normal?)
    rect-normal-gen))
(s/def ::collision-guard
  (s/cat ::op #{:touching}
         ::a-tag ::body-tag
         ::normal (s/? ::collision-normal)
         ::b-tag ::body-tag))
(s/def ::arith-exprs
  ;;todo: get a good generator for this and for arith-expr
  (s/and (s/+ ::arith-expr)
         #(<= 2 (count %))))
(s/def ::simple-arith
  (s/or
   ::constant number?
   ::var ::var))
(s/def ::arith-expr
  (s/or
   ::basic ::simple-arith
   ::unary (s/cat ::op #{:-}
                  ::expr ::arith-expr)
   ::binary (s/cat ::op #{:/}
                   ::left ::arith-expr
                   ::right ::arith-expr)
   ::n-ary (s/cat ::op #{:+ :- :*}
                  ::exprs ::arith-exprs)))
(s/def ::rel-guard (s/cat ::rel ::relation
                          ::exprs ::arith-exprs))
(s/def ::state-name (s/with-gen
                      simple-keyword?
                      name-gen))
(s/def ::state-guard (s/or
                      ::state ::state-path
                      ::remote (s/cat ::ref ::var
                                      ::state ::state-path)
                      ))
(s/def ::unlink-guard (s/cat ::op #{:unlink}
                             ::ref ::var-lookup))
(s/def ::boolean-guard (s/or
                        ::agg (s/cat ::op #{:and :or}
                               ::formulae (s/+ ::guard))
                        ::neg (s/cat ::op #{:not}
                                     ::formula ::guard)))
(s/def ::sync-guard (s/cat ::op #{:sync} ::state ::state-guard ::event #{:entered :exited}))
;;todo: most/least and local qvar collapsing guards
;;todo: when conforming a collision, input, state, or _todo_ least/most/any/all/... guard, tag the local qvar with type info
;;todo: note that we don't need to do all that now. just focus on flappy at the moment, do the minimum possible for that.
(s/def ::guard (s/or ::input-guard ::input-guard
                     ::collision-guard ::collision-guard
                     ::state-guard ::state-guard
                     ::sync-guard ::sync-guard
                     ::rel-guard ::rel-guard
                     ::unlink-guard ::unlink-guard
                     ::boolean-guard ::boolean-guard))

(s/def ::target ::state-path)
(s/def ::update (s/map-of ::var-name ::arith-expr))
(s/def ::transition (s/keys :req-un [::target ::guard] :opt-un [::update]))
(s/def ::flows (s/map-of ::var-name ::arith-expr))
(s/def ::name (s/with-gen simple-keyword? var-name-gen))
(defn kw-prepend [k & args]
  (keyword (str (apply str (map name args)) (name k))))
(defn walk-child-modes [fun mode]
  (let [modes (:modes mode)]
    (update mode
            :modes
            #(map
              (fn [mode-set]
                (map
                 (fn [inner-mode]
                   (walk-child-modes fun (fun inner-mode)))
                 mode-set))
              %))))
(defn qualify-child-names [mode]
  (let [n (:name mode)]
    (walk-child-modes #(update % :name kw-prepend n ".") mode)))
(defn kw-pop-dot-prefix [k]
  (let [parts (string/split (name k) #"\.")
        [before [_dropped last]] (split-at parts (- (count parts) 2))]
    (keyword (string/join "." (concat before [last])))))
(defn unqualify-child-names [mode]
  (walk-child-modes #(update % :name kw-pop-dot-prefix) mode))
;;todo: ensure all modes in the set have unique names
(defn add-child-indices [mode-sets]
  (map
   #(map-indexed (fn [i m] (assoc m :child-index i)) %)
   mode-sets))
(defn remove-child-indices [mode-sets]
  (map
   #(map (fn [m] (dissoc m :child-index)) %)
   mode-sets))
(s/def ::modes
  (s/and
   (s/coll-of (s/coll-of ::mode))
   (s/conformer add-child-indices remove-child-indices)))
(s/def ::mode
  (s/and
   (s/keys :req-un [::name]
           :opt-un [::flows ::modes ::transitions])
   (s/conformer qualify-child-names unqualify-child-names)))
(s/def ::params (s/map-of ::var-name ::var-domain))
(s/def ::prim (s/cat ::shape #{:rect}
                     ::x ::arith-expr
                     ::y ::arith-expr
                     ::w ::arith-expr
                     ::h ::arith-expr))
(s/def ::tag (s/with-gen simple-keyword? var-name-gen))
(s/def ::tags (s/coll-of ::tag))
(s/def ::body (s/keys :req-un [::prim ::tags]))
(s/def ::bodies (s/coll-of ::body))
(s/def ::var-domain (s/cat ::init number? ::domain #{:real :int}))
(s/def ::var-decls (s/map-of ::var-name ::var-domain))
(defn add-implicit-cvars [decls]
  (let [simple-domain {::domain :real ::init 0}
        all-basic-vars (merge {:x simple-domain
                               :y simple-domain} decls)
        all-derivs (mapcat #(vector (keyword (str (name %) "'"))
                                    (keyword (str (name %) "''"))
                                    (keyword (str (name %) "'''")))
                           (filter #(not= (last (name %)) \')
                                   (keys all-basic-vars)))]
    (merge (zipmap all-derivs (repeat simple-domain)) all-basic-vars)))
(defn remove-implicit-cvars [decls]
  (into {} (keep #(let [[k v] %]
                    (when-not
                        (and
                         ;;drop xy and *'
                         (or
                          (#{:x :y} (first %))
                          (= \' (last (name %))))
                         ;;but only if non-standard domain is defined
                         (not= v {::domain :real ::init 0}))
                      [k [(::init v) (::domain v)]]))
                 decls)))
(s/def ::cvars (s/and ::var-decls
                      (s/conformer add-implicit-cvars
                                   remove-implicit-cvars)))
(s/def ::dvars ::var-decls)
(s/def ::ha-desc
  ;;conform cvars and flows to include the defaults, and add params, dvars, etc lists
  (s/and
   (s/keys :req-un [::name ::bodies ::flows ::modes]
           :opt-un [::params ::cvars ::dvars ::tags])
   (s/conformer
    #(merge {:params {}
             :cvars (s/conform ::cvars {})
             :dvars {}
             :tags []}
            %)
    #(into {} (keep (fn [[k v]] (when-not (empty? v)
                                  (s/unform k v)))
                    %)))))
;;todo: a conformer for this that checks inter-HA stuff, ensures everyone has a unique name, etc
(s/def ::ha-descs
  (s/and (s/coll-of ::ha-desc)
         (s/conformer #(zipmap (map :name %) %)
                      vals)))
;;todo: a ha-schema spec that takes ha-descs and metadata and checks everything together.

(def flappy
  {:name :flappy
   :params {:flap-speed [40 :real] :move-speed [10 :real]}
   :bodies [{:prim [:rect 0 0 16 16] :tags [:body]}]
   :flows {:y' -10}
   :modes
   [[{:name :alive
      :flows {:x' :move-speed}
      :transitions [{:guard [:touching :body :wall]
                     :target :dead}]
      :modes
      [[{:name :falling
         :transitions [{:guard [:input :flap :on]
                        :target :alive.flapping}]}
        {:name :flapping
         :flows {:y' :flap-speed}
         :transitions [{:guard [:input :flap :off]
                        :target :alive.falling}]}]]}
     {:name :dead
      :flows {:x' 0 :y' 0}}]]})

(s/def ::out-files (s/map-of string? string?))

(defn join-code [iolist]
  (string/join "\n" (flatten iolist)))

(defn ha-type-coll [type]
  (str (name type) "TypeHAs"))
(defn ha-tag-coll [tag]
  (str (name tag) "TagHAs"))
(defn body-tag-coll [tag]
  (str (name tag) "Bodies"))

(defn all-body-tags [ha-desc]
  (apply sets/union
         (map :tags (:bodies ha-desc))))

(defn constructor-name [type]
  (str "HA" type))

(defn degree [vbl]
  (let [vn (name vbl)]
    (cond
      (.endsWith vn "'''") 3
      (.endsWith vn "''") 2
      (.endsWith vn "'") 1
      :else 0)))

(defn var-name->js [k]
  (let [n (name k)]
    (case (degree k)
      0 n
      1 (str "v" n)
      2 (str "a" n)
      3 (str "da" n))))

(defn decls->json [var-decls]
  (str "{"
       (string/join ", "
                    (map (fn [[k decl]]
                           (str (var-name->js k)
                                ":"
                                ;;todo: handle other stuff
                                (get decl ::init)))
                         var-decls))
       "}"))

(defn default-assign [target nom dict default]
  [:if [:in dict nom]
   [:assign [:deref target nom] [:deref dict nom]]
   [:assign [:deref target nom] default]])

(defn flatten-modes [mode-sets]
  (into {}
        (map-indexed
         (fn [i m]
           [(:name m) (assoc m :index i)])
         (tree-seq #(some? (ffirst (:modes %)))
                   #(flatten (:modes %))
                   mode-sets))))

(defn initial-modes [mode-sets]
  (concat (map ffirst mode-sets)
          (mapcat initial-modes (map (comp :modes ffirst) mode-sets))))

(defn enter-mode [ha-desc mode game-var ha-var]
  [:block
   (for [[u v] (:enter mode)]
     [:assign [:deref ha-var u] v])
   [:def :mode-val [:deref [:deref ha-var :modes] (:name mode)]]
   [:assign [:deref :mode-val :active] true]
   [:assign [:deref :mode-val :entered] true]
   (if (some? (ffirst (:modes mode)))
     (map #(enter-mode ha-desc % game-var ha-var) (map ffirst (:modes mode)))
     [])])
(defn exit-mode [ha-desc mode game-var ha-var]
  [:block
   ;;recursively exit modes
   [:def :mode-val [:deref [:deref ha-var :modes] (:name mode)]]
   (for [[u v] (:exit mode)]
     [:assign [:deref ha-var u] v])
   [:assign [:deref :mode-val :active] false]
   [:assign [:deref :mode-val :exited] true]
   (if (some? (ffirst (:modes mode)))
     (for [m (apply concat (:modes mode))]
       [:if [:deref [:deref [:deref ha-var :modes] (:name mode)] :active]
        (exit-mode ha-desc m game-var ha-var)
        []])
     [])
   ])

(defn follow-transition [ha-desc flat-modes n u t game-var ha-var guard-result-var]
  [:block
   (let [old (get flat-modes n)
         new (get flat-modes t)]
     (exit-mode ha-desc n game-var ha-var)
     (for [[action & params] u]
       (case action
         ;; :create [:call :make-ha (into [game-var]
         ;;                               (select-keys )
         ;;                               [nil :x :y :other-cvars :other-dvars :other-params])]
         ;; ;;todo: a registry of destroyed HAs?
         ;; :destroy [:call :destroy-ha game-var ha-var]
         ;;todo: handle refs specially, track them, etc, or else check them every discrete step.
         :assign [:assign
                  [:deref ha-var (second params)]
                  (last params)]))
     (enter-mode ha-desc t game-var ha-var)
     )])

(defn sort-primes-descending [vbls]
  (reverse (sort-by degree vbls)))

(defn prime [vbl]
  (if (= (degree vbl) 3)
    nil
    (keyword (str (name vbl) "'"))))

(defn higher-primes [vbl]
  (if (= (degree vbl) 3)
    []
    (conj (higher-primes (prime vbl)) (prime vbl))))

(defn jsify [suffix opts hlcode]
  (for [[nom dfn] hlcode]
    (case (first dfn)
      :setup-fn
      :defn)))

(defn phaserize [ha-desc opts]
  (let [{:keys [name bodies cvars dvars params flows modes tags]
         :as ha-desc} (s/conform ::ha-desc ha-desc)
        flat-modes (flatten-modes (:modes ha-desc))]
    (jsify (:name ha-desc) opts
     {:setup-fn
      [:setup-fn
       :make-container-fn
       :destroy-container-fn
       :make-body-fn
       :activate-body-fn
       :deactivate-body-fn
       :get-collisions-fn
       :get-has-fn]
      :guard-satisfied
      [:defn [:game :ha :g]
       ;;todo
       ]
      :update-bodies
      [:defn [:game :ha]
       ;;todo: update collider positions based on my xy?
       (for [[bi {g :guard}] (zipmap
                              (range 0 (inc (count bodies)))
                              bodies)]
         [:if [:call :guard-satisfied [:game :ha g]]
          [:call :activate-body-fn [:game :ha [:deref :ha.bodies bi]]]
          [:call :deactivate-body-fn [:game :ha [:deref :ha.bodies bi]]]])]
      :make-ha
      [:defn [:game :name :x :y :other-cvars :other-dvars :other-params]
       [:def :group [:call :make-container-fn [:game name tags :name :x :y]]]
       [:assign :group.modes
        (for [[name _] flat-modes]
          [:dict {:name name :active false
                  :entering false :exiting false}])]
       (for [[nom {domain ::domain init ::init}] (dissoc cvars :x :y)]
         (default-assign :group nom :other-cvars init))
       (for [[nom {domain ::domain init ::init}] dvars]
         (default-assign :group nom :other-dvars init))
       (for [[nom {domain ::domain init ::init}] params]
         (default-assign :group nom :other-params init))
       [:assign :group.bodies [:list []]]
       [:assign :group.next [:dict {}]]
       (for [{prim :prim tags :tags} bodies
             ;;todo: support non-constant keys
             :let [[x y w h] (map #(get-in % [::basic ::constant])
                                  (select-keys prim [:x :y :w :h]))]]
         [:call :group.bodies.push
          [:call
           :make-body-fn
           [:game :group tags (::shape prim) [x y w h]]]])
       ]
      :init-ha
      [:defn [:game :ha]
       ;;...
       (for [m (initial-modes (:modes ha-desc))]
         (enter-mode ha-desc m :game :ha))
       [:call :update-bodies [:game :ha]]]
      :destroy-ha
      [:defn [:game :ha]
       (for [[bi {g :guard :as b}] (zipmap
                                    (range 0 (inc (count bodies)))
                                    bodies)]
         [:call :destroy-body-fn [:game :ha [:deref :ha.bodies bi]]])
       [:call :destroy-container-fn [name tags :ha :ha.bodies]]]
      :before-steps
      [:defn [:game :ha]
       (for [[n _] flat-modes]
         [:block
          [:assign [:deref [:deref :ha.modes n] :entered] false]
          [:assign [:deref [:deref :ha.modes n] :exited] false]])]
      :discrete-step-early
      [:defn [:game :ha]
       [:assign :ha.contacts [:call :get-collisions-fn [:game :ha]]]
       ;;todo: nested ifs to avoid some extra checks?
       (for [[n {trs :transitions}] flat-modes]
         [:block
          [:assign [:deref [:deref :ha.modes n] :transition] 0]
          [:if [:deref [:deref :ha.modes n] :active]
           [:breakable-block
            (for [[ti {g :guard t :target u :update}] (zipmap
                                                       (range 0 (dec (count trs)))
                                                       trs)]
              [:block
               [:def :guard-result [:call :guard-satisfied [:game :ha g]]]
               [:if :guard-result
                [:block
                 [:assign [:deref [:deref :ha.modes n] :transition] ti]
                 [:assign [:deref [:deref :ha.modes n] :transition-guard-result] :guard-result]
                 [:break]]
                []]])]
           []]])]
      :discrete-step-late
      [:defn [:game :ha]
       ;;todo: nested ifs to avoid some extra checks?
       ;;todo: what about refs that became null or unlinked due to destruction? at any rate destruction can't happen instantaneously it's too weird. here seems like the best option to deal with them, but what if the HA with the unlinked transition already transitioned earlier in the frame?
       (for [[n {trs :transitions}] flat-modes]
         [:if [:deref [:deref :ha.modes n] :active]
          (for [[ti {g :guard t :target u :update}] (zipmap
                                                     (range 0 (dec (count trs)))
                                                     trs)]
            [:if [:= [:deref [:deref :ha.modes n] :transition] ti]
             [:block
              [:def :guard-result [:deref [:deref :ha.modes n] :transition-guard-result]]
              (follow-transition ha-desc flat-modes n u t :game :ha :guard-result)]
             []])
          []])]
      :continuous-step
      [:defn
       [:game :ha :dt]
       ;;even though flows could be updated just on state changes, this way we can
       ;; more easily handle state changes of ref'd HAs.
       ;;todo:nested ifs?
       (for [[n {fs :flows}] flat-modes]
         [:if [:deref [:deref :ha.modes n] :active]
          (for [[vbl flow] fs]
            ;;fill in all explicit flows
            ;;todo: detect conflicts
            [:block
             [:assign [:deref :ha.next vbl] flow]
             (for [higher-prime (higher-primes vbl)]
               [:assign [:deref :ha.next higher-prime] 0])])
          []])
       ;;update accelerations, then update velocities, then update positions. new position depends on old position and _new_ velocity, new velocity depends on old velocity and new acceleration, etc.
       (for [v (sort-primes-descending (keys (:cvars ha-desc)))]
         (if (some? (higher-primes v))
           [:assign
            [:deref :ha.next v]
            [:+ [:deref :ha v] [:* [:deref :ha.next (prime v)] :dt]]]
           []))
       [:call :update-bodies [:game :ha]]]
      :stop-movement
      [:defn [:game :ha :dim]
       (into [:case :dim]
             (for [v (keys (:cvars ha-desc))
                   :let [ps (higher-primes v)]]
               [v [(for [pi ps]
                     [:assign [:deref :ha pi] 0])]]))]})))

;; (defn phaserize- [ha-descs opts]
;;   ;;todo: should the conformer do the good normalization etc, and ensure variables are ok, etc?
;;   (let [ha-descs (s/conform ::ha-descs ha-descs)
;;         ha-types (keys ha-descs)
;;         js-code
;;         [[:def :game [:new
;;                       :Phaser.game
;;                       [800 600 :Phaser.AUTO ""
;;                        {:preload :preload
;;                         :create :create
;;                         :update :update}]]]
;;          (map (fn [t]
;;                 (vector :def
;;                         (ha-type-coll t)
;;                         [:array]))
;;               ha-types)
;;          (map (fn [t]
;;                 (vector :def
;;                         (ha-tag-coll t)
;;                         [:array]))
;;               (apply sets/union
;;                      (map :tags (vals ha-descs))))
;;          [:defn :preload [] []]
;;          (map (fn [type]
;;                 (let [desc (get ha-descs type)
;;                       n (name type)
;;                       type-array (ha-type-coll type)
;;                       constructor (constructor-name type)
;;                       ha-base-params (str "baseParams" n)
;;                       ha-base-cvars (str "baseCVars" n)
;;                       ha-base-dvars (str "baseDVars" n)]
;;                   [ ;;set up ha-base-params, cvars, dvars
;;                    [:def ha-base-params (zipmap (keys (:params desc))
;;                                                 (map ::init (vals (:params desc))))]
;;                    [:def ha-base-cvars (zipmap (keys (:cvars desc))
;;                                                (map ::init (vals (:cvars desc))))]
;;                    [:def ha-base-dvars (zipmap (keys (:dvars desc))
;;                                                (map ::init (vals (:dvars desc))))]
;;                    [:def-constructor type [:params :cvars :dvars]
;;                     [:super
;;                      :Phaser.group.call
;;                      [:this :game :game.world [:concat
;;                                                [:str n]
;;                                                [:deref type-array :length]]]]
;;                     ;;todo: need something that lets type declarations work
;;                     [:merge-into :this ha-base-params :params]
;;                     [:merge-into :this ha-base-cvars :cvars]
;;                     [:merge-into :this ha-base-dvars :dvars]
;;                     [:push type-array :this]
;;                     (map #(vector :push :this)
;;                          (:tags desc))
;;                     (map (fn [{{x :x y :y w :w h :h} ts :tags}]
;;                            ;;todo handle vars as well as constants
;;                            (let [[_ [_ x]] x
;;                                  [_ [_ y]] y
;;                                  [_ [_ w]] w
;;                                  [_ [_ h]] h]
;;                              ;;todo handle bodies that can turn on and off
;;                              [:def :b [:call :game.make.sprite [x y type]]]
;;                              [:assign :b.width w]
;;                              [:assign :b.height h]
;;                              (map (fn [t]
;;                                     [:push (body-tag-coll t) :b])
;;                                   ts)
;;                              [:call :this.add :b])
;;                            )
;;                          (get desc :bodies))]]))
;;                 ha-types)
;;          ]]
;;     ;;todo: more standardizations/transformations/etc
;;     ;;todo: more data oriented
;;     #_{"game.js"
;;      (join-code
;;       [(map (fn [type]
;;               )
;;             ha-types)
;;        "function create() {"
;;        ;;...?
;;        "}"
;;        "function update() {"
;;        "  var haI = 0;"
;;        "  //go through each ha type array"
;;        "  for(haI = 0; haI < flappyTypeHAs.length; haI++) {"
;;        "    //do any available input or collision (?) transitions"
;;        "  }"
;;        "  //other HA types"
;;        "  //go through each ha type array"
;;        "  for(haI = 0; haI < flappyTypeHAs.length; haI++) {"
;;        "    //update flows and move things"
;;        "  }"
;;        "  //other HA types"
;;        "  var contacts = findAllCollisions()"
;;        "  //go through each ha type array"
;;        "    //handle collisions"
;;        "  //go through each ha type array"
;;        "    //do any available collision transitions?"
;;        "}"
;;        "function inputButton(inpName, test) {"
;;        "  if(inpName == 'flap') { return game.input.keyboard.isDown(Phaser.KeyCode.SPACEBAR); }"
;;        "  return false;"
;;        "}"
;;        ])}
;;     ;;todo: do it as a sequence of transformations between languages!!

;;   ))

