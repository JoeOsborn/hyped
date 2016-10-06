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
(defn qualify-child-names [mode]
  (let [[msort mode-set] (:modes mode)
        n (:name mode)]
    (assoc mode
           :modes
           (walk/prewalk #(if (and (map? %)
                                   (:name %))
                            (update % :name kw-prepend n ".")
                            %)
                         (:modes mode)))))
(defn kw-pop-dot-prefix [k]
  (let [parts (string/split (name k) #"\.")
        [before [_dropped last]] (split-at parts (- (count parts) 2))]
    (keyword (string/join "." (concat before [last])))))
(defn unqualify-child-names [mode]
  (let [[msort mode-set] (:modes mode)
        n (:name mode)]
    (assoc mode
           :modes
           (walk/prewalk #(if (and (map? %)
                                   (:name %))
                            (update % :name kw-pop-dot-prefix)
                            %)
                         (:modes mode)))))
;;todo: ensure all modes in the set have unique names
(s/def ::modes
  (s/or
   ::parallel (s/cat ::par #{:par} ::par-mode-sets (s/+ (s/coll-of ::mode)))
   ::simple (s/coll-of ::mode)))
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
             :tags #{}}
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
   [{:name :alive
     :flows {:x' :move-speed}
     :transitions [{:guard [:touching :body :wall]
                    :target :dead}]
     :modes
     [{:name :falling
       :transitions [{:guard [:input :flap :on]
                      :target :alive.flapping}]}
      {:name :flapping
       :flows {:y' :flap-speed}
       :transitions [{:guard [:input :flap :off]
                      :target :alive.falling}]}]}
    {:name :dead
     :flows {:x' 0 :y' 0}}]})

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

(defn define-mode [{:keys [name _flows _transitions _modes] :as mode}]
  [mode
   [:dict {:name name
           :active false
           ;;and debug info like entry or exit times or whatever
           }]])

(defn define-modes [modes]
  (loop [mode-list []
         mode-q [modes]
         mode-i 0]
    (if (>= mode-i (count mode-q))
      mode-list
      (do
        (println mode-i mode-q)
        (let [[mode-sort mode-set] (nth mode-q mode-i)]
          (case mode-sort
            nil (recur mode-list mode-q (inc mode-i))
            ::parallel
            (recur mode-list
                   (into mode-q (map (partial vector ::simple)
                                     (::par-mode-sets mode-set)))
                   (inc mode-i))
            ::simple
            (let [h (define-mode (first mode-set))
                  t (map define-mode (rest mode-set))
                  child-modes (map :modes mode-set)
                  h (assoc-in h [1 :active] true)]
              (recur (into mode-list (cons h t))
                     (into mode-q child-modes)
                     (inc mode-i)))))))))

(defn default-assign [target nom dict default]
  [:if [:in dict nom]
   [:assign [:deref target nom] [:deref dict nom]]
   [:assign [:deref target nom] default]])

(defn initial-active-modes [modes]
  [:list
   ;;[{name:blah, modes:blar}, {name:bleh, modes:blah}] fine for now
   (if (= (first modes) ::parallel)
     (for [mode-set (::par-mode-sets (second modes))
           :let [init (first mode-set)
                 ms (:modes init)]]
       (if (empty? ms)
         [:dict {:name (:name init)}]
         [:dict {:name (:name init)
                 :modes (initial-active-modes ms)}])))])

(defn phaserize [ha-desc opts]
  (let [{:keys [name bodies cvars dvars params flows modes tags]
         :as ha-desc} (s/conform ::ha-desc ha-desc)]
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
                     (for [[bi {g :guard}] (zipmap
                                            (range 0 (inc (count bodies)))
                                            bodies)]
                       [:if [:call :guard-satisfied [:game :ha g]]
                        [:call :activate-body-fn [:game :ha [:deref :ha.bodies bi]]]
                        [:call :deactivate-body-fn [:game :ha [:deref :ha.bodies bi]]]])]
     :make-ha
     [:defn [:game :name :x :y :other-cvars :other-dvars :other-params]
               [:def :group [:call :make-container-fn [:game name tags :name :x :y]]]
               (for [[nom {domain ::domain init ::init}] (dissoc cvars :x :y)]
                 (default-assign :group nom :other-cvars init))
               (for [[nom {domain ::domain init ::init}] dvars]
                 (default-assign :group nom :other-dvars init))
               (for [[nom {domain ::domain init ::init}] params]
                 (default-assign :group nom :other-params init))
               [:assign :group.bodies [:list []]]
               (for [{prim :prim tags :tags} bodies
                     ;;todo: support non-constant keys
                     :let [[x y w h] (map #(get-in % [::basic ::constant])
                                          (select-keys prim [:x :y :w :h]))]]
                 [:call :group.bodies.push
                  [:call
                   :make-body-fn
                   [:game :group tags (::shape prim) [x y w h]]]])
               [:assign :group.modes (define-modes modes)]
               ]
     :init-ha
     [:defn [:game :ha]
               ;;...
               [:call :update-bodies [:game :ha]]]
     :destroy-ha
     [:defn [:ha]
                  (for [[bi {g :guard :as b}] (zipmap
                                               (range 0 (inc (count bodies)))
                                               bodies)]
                    [:call :destroy-body-fn [:game :ha [:deref :ha.bodies bi]]])
                  [:call :destroy-container-fn [name tags :ha :ha.bodies]]]
     :transition-ha
     [:defn [:game :ha]
      ;;todo: perform update, make sure each state is appropriately alive
                     ]
     :flow-ha [:defn
               [:game :ha]
               ;;todo: 
               [:call :update-colliders [:game :ha]]]
     }))

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

