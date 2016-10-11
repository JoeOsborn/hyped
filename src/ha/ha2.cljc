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
         ::a-tags (s/coll-of ::body-tag)
         ::normals (s/? (s/coll-of ::collision-normal))
         ::b-tags (s/coll-of ::body-tag)))
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

(s/def ::target ::state-name)
(s/def ::update (s/map-of ::var-name ::arith-expr))
(s/def ::transition (s/keys :req-un [::target ::guard] :opt-un [::update]))
(s/def ::transitions (s/coll-of ::transition))
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
;;todo: __ is maybe not a great choice. \. is definitely not.
(defn qualify-child-names [mode]
  (let [n (:name mode)]
    (walk-child-modes #(update % :name kw-prepend n "__") mode)))
(defn kw-pop-dot-prefix [k]
  (let [parts                    (string/split (name k) #"__")
        [before [_dropped last]] (split-at parts (- (count parts) 2))]
    (keyword (string/join "__" (concat before [last])))))
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
  (let [simple-domain  {::domain :real ::init 0}
        all-basic-vars (merge {:x simple-domain
                               :y simple-domain} decls)
        all-derivs     (mapcat #(vector (keyword (str (name %) "'"))
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
             :cvars  (s/conform ::cvars {})
             :dvars  {}
             :tags   []}
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
  {:name   :flappy
   :params {:flap-speed [-40 :real] :move-speed [20 :real]}
   :bodies [{:prim [:rect 0 0 16 16] :tags [:body]}]
   :flows  {:y'' 40 :x' 0}
   :modes
   [[{:name        :alive
      :flows       {:x' :move-speed}
      :transitions [{:guard  [:touching #{:body} #{:wall}]
                     :target :dead}]
      :modes
      [[{:name        :falling
         :transitions [{:guard  [:input :flap :on]
                        ;;todo: need nicer state nesting character. "." is ideal
                        ;; but the code will need to be careful to rename targets appropriately. Maybe a name-or-a-list of simple names?
                        :target :alive__flapping}]}
        {:name        :flapping
         :flows       {:y' :flap-speed}
         :transitions [{:guard  [:input :flap :off]
                        :target :alive__falling}]}]]}
     {:name  :dead
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
      (.endsWith vn "''")  2
      (.endsWith vn "'")   1
      :else                0)))

(defn var-name->js [k]
  (let [n (-> (name k)
              (string/replace #"-" "_"))
        n (case (degree k)
            0 n
            1 (str "v" n)
            2 (str "a" n)
            3 (str "da" n))]
    (string/replace n #"\'" "")))

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
  [:if [:contains-key dict nom]
   [:assign [:deref target nom] [:deref dict nom]]
   [:assign [:deref target nom] default]])

(defn flatten-modes [mode-sets]
  (into {}
        (map-indexed
         (fn [i m]
           [(:name m) (assoc m :index i)])
         ;;gotta put in a faux root and then drop it for uniform handling of all levels.
         (rest
          (tree-seq #(some? (ffirst (:modes %)))
                    #(flatten (:modes %))
                    {:modes mode-sets :name :$root})))))

(defn initial-modes [mode-sets]
  (concat (map first mode-sets)
          (mapcat initial-modes (map (comp :modes first) mode-sets))))

(defn enter-mode [ha-desc mode game-var ha-var]
  (assert (and mode (:name mode)))
  [:block
   (for [[u v] (:enter mode)]
     [:assign [:deref ha-var u] v])
   [:def :mode-val [:deref [:deref ha-var :modes] (:name mode)]]
   [:assign [:deref :mode-val :active] true]
   [:assign [:deref :mode-val :entered] true]
   (if (some? (ffirst (:modes mode)))
     (map #(enter-mode ha-desc % game-var ha-var) (map first (:modes mode)))
     [])])
(defn exit-mode [ha-desc mode game-var ha-var]
  (assert (and mode (:name mode)))
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
  (let [old (get flat-modes n)
        new (get flat-modes t)]
    [:block
     (exit-mode ha-desc (get flat-modes n) game-var ha-var)
     (for [[action & params] u]
       (case action
         ;; :create [:call :make-char (into [game-var]
         ;;                               (select-keys )
         ;;                               [nil :x :y :other-cvars :other-dvars :other-params])]
         ;; ;;todo: a registry of destroyed HAs?
         ;; :destroy [:call :destroy-char game-var ha-var]
         ;;todo: handle refs specially, track them, etc, or else check them every discrete step.
         :assign [:assign
                  [:deref ha-var (second params)]
                  (last params)]))
     (enter-mode ha-desc (get flat-modes t) game-var ha-var)]))

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

(declare jsify-value)
(defn rel-expr [opts rel rel-js args]
  (if (= 2 (count args))
    (str "("
         (jsify-value opts (first args))
         " " rel-js " "
         (jsify-value opts (second args))
         ")")
    (jsify-value opts
                 (into [:and]
                       (map
                        (fn [a b]
                          [:= a b])
                        (butlast args)
                        (rest args))))))

(defn jsify-value [opts val]
  (cond
    (boolean? val) (str val)
    (nil? val)     "null"
    (keyword? val) (cond
                     ;;todo: have to handle this for real later, this forces all the guard functions to call the variable :ha.
                     (contains? (:special-names opts) val)
                     (var-name->js (str (name val) "_" (:suffix opts)))
                     (= ::self val) (var-name->js :ha)
                     :else          (var-name->js (name val)))
    (number? val)  (str val)
    (string? val)  (str "\"" val "\"")
    (map? val)     (str "{" (string/join ", " (for [[k v] val]
                                                (str (jsify-value opts k) ": "
                                                     (jsify-value opts v)))) "}")
    :else
    (case (first val)
      :contains ;;gotta pass an expression returning a string!
      (let [[d k] (rest val)]
        (str "(" (jsify-value opts k) " in " (jsify-value opts d) ")"))
      :contains-key ;;gotta pass a key!
      (let [[d k] (rest val)]
        (str "('" (jsify-value opts k) "' in " (jsify-value opts d) ")"))
      :and
      (str "("
           (string/join " && " (map #(jsify-value opts %)
                                    (rest val)))
           ")")
      :or
      (str "("
           (string/join " || " (map #(jsify-value opts %)
                                    (rest val)))
           ")")
      :not
      (str "!" (jsify-value opts (second val)))
      (:+ :- :/ :*)
      (str "(" (string/join (name (first val))
                            (map #(jsify-value opts %)
                                 (rest val)))
           ")")
      :**
      (str "Math.pow("
           (jsify-value opts (second val)) ", "
           (jsify-value opts (last val))
           ")")
      :=
      (rel-expr opts (first val) " == " (rest val))
      (:< :<= :>= :>)
      (rel-expr opts (first val) (name (first val)) (rest val))
      (:dict :string :number ::basic ::var ::constant)
      (jsify-value opts (second val))
      :list
      (str "[" (string/join "," (map #(jsify-value opts %) (second val))) "]")
      :deref   (do
                 (assert (every? some? (rest val)))
                 (string/join "."
                             (map #(jsify-value opts %)
                                  (rest val))))
      :lookup  (str (jsify-value opts (nth val 1))
                    "["
                    (jsify-value opts (nth val 2))
                    "]")
      ::lookup (jsify-value opts [:deref
                                  ;;todo: have to handle ::self specially.
                                  (::ref (second val))
                                  (::var (second val))])
      :call    (str (if (keyword? (nth val 1))
                      (jsify-value opts (nth val 1))
                      (str "(" (jsify-value opts (nth val 1)) ")"))
                    "("
                    (string/join ","
                                 (map #(jsify-value opts %)
                                      (nth val 2)))
                    ")")
      (do (println "Weird value " val)
          (assert false)))))

(defn indent->spaces [opts]
  (string/join (repeat (* 2 (get opts :indent 0)) " ")))

(defn jsify-statement [opts [vk & vrest :as v]]
  (let [indent (:indent opts)
        spaces (indent->spaces opts)]
    (case vk
      :block
      (string/join "\n"
                   (map #(jsify-statement opts %) vrest))
      :case
      (let [[value & checks] vrest
            inner-opts       (update opts :indent inc)
            more-spaces      (indent->spaces inner-opts)]
        (str spaces
             "switch(" (jsify-value opts value) ") {\n"
             (string/join "\n"
                          (map
                           (fn [[check body]]
                             (str more-spaces "case " (jsify-value opts check) ":\n"
                                  (jsify-statement inner-opts
                                                   [:block body [:break]])))
                           checks))
             "\n"
             spaces "}"))
      :def
      (str spaces "var " (var-name->js (first vrest)) " = " (jsify-value opts (second vrest)) ";")
      :assign
      (str spaces (jsify-value opts (first vrest)) " = " (jsify-value opts (second vrest)) ";")
      :if
      (str spaces
           "if(" (jsify-value opts (first vrest)) ") {\n"
           (jsify-statement (update opts :indent inc) (second vrest)) "\n"
           spaces "}"
           (if (= 3 (count vrest))
             (str " else {\n"
                  (jsify-statement (update opts :indent inc) (last vrest)) "\n"
                  spaces "}")
             ""))
      :breakable-block
      (str spaces "for(var _bk_" indent " = true; _bk_" indent "; _bk_" indent " = false) {\n"
           (jsify-statement (update opts :indent inc) vrest) "\n"
           spaces "}")
      :break
      (str spaces "break;")
      :return
      (str spaces "return (" (if (empty? vrest)
                             ""
                             (jsify-value opts (first vrest))) ");")
      ;;...?
      (cond
        (keyword? vk)    ;;implicit expr
        (str spaces (jsify-value opts v) ";")
        (sequential? vk) ;;implicit block
        (jsify-statement opts (into [:block] v))
        (nil? vk)        "" ;;implicit empty block
        :else            (do (println "weird value"
                                      vk v)
                             (assert false))))))

(defn jsify-root [opts hlcode]
  (let [opts (merge {:indent 0} opts)]
    (string/join
     "\n\n"
     (for [[nom df] hlcode
           :let     [nomjs (str (var-name->js nom) "_" (:suffix opts))
                     spaces (indent->spaces opts)]]
       (if (= :defn (first df))
         (let [[args & body] (rest df)]
           (str
            spaces "function " nomjs "(" (string/join "," (map var-name->js args)) ") {\n"
            (string/join "\n"
                         (map #(jsify-statement (update opts :indent inc) %)
                              body)) "\n"
            spaces "}"))
         (jsify-statement opts [:def nom df]))))))

(defn hlify-guard [opts ha-desc g game-var ha-var status-var]
  (case (first g)
    ::input-guard
    (let [{:keys [::input ::input-state]} (second g)
          state-type                      (first input-state)
          state-test                      (second input-state)]
      [:block
       [:def :input-val [:call :get-input-fn [game-var ha-var (name input)]]]
       [:assign status-var
        (cond
          (and (= state-type ::button) (= state-test :on))
          :input-val
          (and (= state-type ::button) (= state-test :off))
          [:not :input-val]
          (= state-type ::axis)
          [(::rel state-test)
           :input-val
           (::threshold state-test)])]])
    ::collision-guard
    (let [{:keys [::a-tags ::normals ::b-tags]} (second g)]
      ;;go through ha.contacts and look for ones involving a-tag, b-tag, check the normal if present
      ;;todo: handle qvars and looking for collisions with specific HAs.
      [:block
       [:def :contacts
        [:call :get-collisions-fn
         [[:list [ha-var]]
          (when a-tags [:list (map name a-tags)])
          (when normals [:list (vec normals)])
          nil
          (when b-tags [:list (map name b-tags)])]]]
       [:assign status-var [:< 0 :contacts.length]]])
    (do
      (println "Unrecognized guard " g)
      (s/unform ::guard g))))

(defn all-guards [modes]
  (mapcat #(map :guard (:transitions %)) (vals modes)))

(defn phaserize [ha-desc opts]
  (let [{:keys [:bodies :cvars :dvars :params :flows :modes :tags] :as ha-desc}
        (s/conform ::ha-desc ha-desc)
        ha-name                 (:name ha-desc)
        flat-modes              (flatten-modes modes)
        guards                  (concat
                                 (map :guard bodies)
                                 (all-guards flat-modes))
        guard-nums              (zipmap guards (range 0 (count guards)))
        guard-satisfied-fn-name (fn [g]
                                  (keyword (str "guard-satisfied-"
                                                (str (get guard-nums g)))))
        guard-fns-hlcode
        (into
         {}
         (for [g     guards
               :when (some? g)]
           [(keyword (guard-satisfied-fn-name g))
            [:defn [:game :ha]
             [:def :status true]
             (hlify-guard opts ha-desc g :game :ha :status)
             [:return :status]]]))
        hook-keys               [:make-container-fn
                                 :destroy-container-fn
                                 :make-body-fn
                                 :destroy-body-fn
                                 :activate-body-fn
                                 :deactivate-body-fn
                                 :get-collisions-fn
                                 :get-chars-fn
                                 :get-input-fn]
        hlcode
        (merge
         guard-fns-hlcode
         (zipmap hook-keys nil)
         {:setup-fn (let [hook-args (map #(keyword (str (name %) "-arg"))
                                         hook-keys)]
                      [:defn hook-args
                       (for [[hn ha] (zipmap hook-keys hook-args)]
                         [:assign hn ha])])
          :update-bodies
          [:defn [:game :ha]
           (for [[bi {g :guard}] (zipmap
                                  (range 0 (count bodies))
                                  bodies)]
             [:block
              (if (some? g)
                [:if [:call (guard-satisfied-fn-name g) [:game :ha]]
                 [:call :activate-body-fn [:game :ha [:lookup :ha.bodies bi]]]
                 [:call :deactivate-body-fn [:game :ha [:lookup :ha.bodies bi]]]]
                [])
              ;;todo: update collider positions based on my xy?
              ])]
          :make-char
          [:defn [:game :name :x :y :other-cvars :other-dvars :other-params]
           [:def :group [:call :make-container-fn [:game (name ha-name) [:list (map name tags)] :name :x :y]]]
           [:assign :group.modes
            [:dict
             (into
              {}
              (for [[mode-name _] flat-modes]
                [mode-name
                 [:dict {:name     (name mode-name) :active  false
                         :entering false            :exiting false}]]))]]
           (for [[nom {domain ::domain init ::init}] (dissoc cvars :x :y)]
             (default-assign :group nom :other-cvars init))
           (for [[nom {domain ::domain init ::init}] dvars]
             (default-assign :group nom :other-dvars init))
           (for [[nom {domain ::domain init ::init}] params]
             (default-assign :group nom :other-params init))
           [:assign :group.bodies [:list []]]
           [:assign :group.next [:dict {}]]
           [:def :body nil]
           (for [{prim :prim btags :tags g :guard} bodies
                 ;;todo: support non-constant keys
                 :let
                 [;;todo assuming "basic" "constant": [::basic [::constant num]].
                  ;;not sure why there's three "1"s here. oh, it is because select-keys yields a dict. 
                  [x y w h] (map #(get-in % [1 1 1])
                                 (select-keys prim [::x ::y ::w ::h]))]]
             [:block
              [:assign
               :body
               [:call
                :make-body-fn
                [:game
                 (name ha-name)
                 [:list (map name tags)]
                 :group
                 [:list (map name btags)]
                 (name (::shape prim))
                 [:list [x y w h]]]]]
              [:call :group.bodies.push [:body]]
              (if (some? g)
                []
                [:call :activate-body-fn [:game :group :body]])])
           (for [m (initial-modes (:modes ha-desc))]
             (enter-mode ha-desc m :game :group))
           [:call :update-bodies [:game :group]]]
          :destroy-char
          [:defn [:game :ha]
           (for [[bi {g     :guard
                      btags :tags :as b}] (zipmap
                                           (range 0 (count bodies))
                                           bodies)]
             [:call :destroy-body-fn
              [:game :ha [:lookup :ha.bodies bi]]])
           [:call :destroy-container-fn
            [:game :ha]]]
          :before-steps
          [:defn [:game :ha]
           (for [[n _] flat-modes]
             [:block
              [:assign [:deref [:deref :ha.modes n] :entered] false]
              [:assign [:deref [:deref :ha.modes n] :exited] false]])]
          :discrete-step-early
          [:defn [:game :ha]
           #_[:assign :ha.contacts [:call :get-collisions-fn [:game :ha]]]
           ;;todo: nested ifs to avoid some extra checks?
           (for [[n {trs :transitions}] flat-modes
                 :when                  (< 0 (count trs))]
             [:block
              [:assign [:deref [:deref :ha.modes n] :transition] -1]
              [:if [:deref [:deref :ha.modes n] :active]
               [:breakable-block
                (for [[ti {g :guard t :target u :update}] (zipmap
                                                           (range 0 (count trs))
                                                           trs)]
                  (if (some? g)
                    [:block
                     [:def :guard-result
                      [:call (guard-satisfied-fn-name g) [:game :ha]]]
                     [:if :guard-result
                      [:block
                       [:assign [:deref [:deref :ha.modes n] :transition] ti]
                       [:assign [:deref [:deref :ha.modes n] :transition-guard-result] :guard-result]
                       [:break]]]]
                    [:block
                     [:assign [:deref [:deref :ha.modes n] :transition] ti]
                     [:break]]))]]])]
          :discrete-step-late
          [:defn [:game :ha]
           ;;todo: nested ifs to avoid some extra checks?
           ;;todo: what about refs that became null or unlinked due to destruction? at any rate destruction can't happen instantaneously it's too weird. here seems like the best option to deal with them, but what if the HA with the unlinked transition already transitioned earlier in the frame?
           (for [[n {trs :transitions}] flat-modes
                 :when                  (< 0 (count trs))]
             [:if [:deref [:deref :ha.modes n] :active]
              (for [[ti {g :guard t :target u :update}] (zipmap
                                                         (range 0 (count trs))
                                                         trs)]
                [:if [:= [:deref [:deref :ha.modes n] :transition] ti]
                 [:block
                  [:def :guard-result [:deref [:deref :ha.modes n] :transition-guard-result]]
                  (follow-transition ha-desc flat-modes n u t :game :ha :guard-result)]])])]
          :continuous-step
          [:defn [:game :ha :dt]
           ;;even though flows could be updated just on state changes, this way we can
           ;; more easily handle state changes of ref'd HAs.
           ;;todo:nested ifs?
           (for [[vbl flow] flows]
             ;;fill in all root flows
             ;;todo: detect conflicts
             [:block
              [:assign [:deref :ha vbl] flow]
              (for [higher-prime (higher-primes vbl)]
                [:assign [:deref :ha higher-prime] 0])])
           (for [[n {fs :flows}] flat-modes
                 :when           (< 0 (count fs))]
             [:if [:deref [:deref :ha.modes n] :active]
              (for [[vbl flow] fs]
                ;;fill in all explicit flows
                ;;todo: detect conflicts
                [:block
                 [:assign [:deref :ha vbl] flow]
                 (for [higher-prime (higher-primes vbl)]
                   [:assign [:deref :ha higher-prime] 0])])])
           ;;update accelerations, then update velocities, then update positions. new position depends on old position and _new_ velocity, new velocity depends on old velocity and new acceleration, etc.
           (for [v     (sort-primes-descending (keys (:cvars ha-desc)))
                 :when (some? (first (higher-primes v)))]
             [:assign
              [:deref :ha v]
              [:+ [:deref :ha v] [:* [:deref :ha (prime v)] :dt]]])
           [:call :update-bodies [:game :ha]]]
          :stop-movement
          [:defn [:game :ha :dim]
           (into [:case :dim]
                 (for [v    (keys (:cvars ha-desc))
                       :let [ps (higher-primes v)]]
                   [v [(for [pi ps]
                         [:assign [:deref :ha pi] 0])]]))]})
        opts
        (update opts
                :special-names
                sets/union
                (set hook-keys)
                (set (keys hlcode)))
        opts
        (update opts :suffix #(if (nil? %)
                                (name ha-name)
                                (concat (name %) "_" (name ha-name))))]
    (str
     "//First, call setup_fn_" (name ha-name) "(make_container, destroy_container, make_body, destroy_body, activate_body, deactivate_body, get_collisions, get_chars, get_input) to add all the necessary callbacks.\n"
     "//To make a character, call make_char_" (name ha-name) "; to destroy, destroy_char_" (name ha-name) ".\n"
     "//Each frame, update your non-Hyped characters and then call the following functions on every " (name ha-name) " character. If you have multiple Hyped characters, call all the before_steps_* functions, then all the discrete_step_early_* functions, etc.:\n"
     "//  1. before_steps_" (name ha-name) "(game, ha)\n"
     "//  2. discrete_step_early_" (name ha-name) "(game, ha)\n"
     "//  3. discrete_step_late_" (name ha-name) "(game, ha)\n"
     "//  4. continuous_step_" (name ha-name) "(game, ha, dt)\n"
     "//If you want to stop it from moving in x or y or whatever, call e.g. stop_movement_" ha-name "(game, ha, 'x')\n"
     
     "//Each frame, call before_steps_" (name ha-name) "() on each char of this type then the respective before_steps_* function of each char of any other Hyped character types.\n\n"
     (jsify-root opts hlcode))))
