(ns ha.ha2
  (:require [clojure.spec :as s]
            [clojure.spec.gen :as gen]
            [clojure.string :as string]
            [clojure.set :as sets]
            [clojure.walk :as walk]))

(def *state-part-joiner* "$")

;;todo: function make-ha that takes a ha spec, conforms it, and then produces records(?)

(s/def ::var-name simple-keyword?)
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
(s/def ::state-name
  (s/and #(or (simple-keyword? %)
              (and (seq? %) (every? simple-keyword? %)))
         (s/conformer #(if (seq? %)
                         (string/join *state-part-joiner* (map name %))
                         %)
                      #(if (string/includes? (name %) *state-part-joiner*)
                         (mapv keyword (string/split % *state-part-joiner*))
                         %))))
(s/def ::state-guard (s/or
                      ::state ::state-name
                      ::remote (s/cat ::ref ::var
                                      ::state ::state-name)
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
(s/def ::transition
  (s/keys :req-un [::target ::guard] :opt-un [::update]))
(s/def ::transitions (s/coll-of ::transition))
(s/def ::flows (s/map-of ::var-name ::arith-expr))
(s/def ::name simple-keyword?)
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
;;todo: $, __ are maybe not a great choice. \. is definitely not.

(defn qualify-child-names [mode]
  (let [n (:name mode)]
    (walk-child-modes #(update % :name kw-prepend n *state-part-joiner*) mode)))
(defn kw-pop-dot-prefix [k]
  (let [parts                    (string/split (name k) *state-part-joiner*)
        [before [_dropped last]] (split-at parts (- (count parts) 2))]
    (keyword (string/join *state-part-joiner* (concat before [last])))))
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
(s/def ::tag simple-keyword?)
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
                        :target [:alive :flapping]}]}
        {:name        :flapping
         :flows       {:y' :flap-speed}
         :transitions [{:guard  [:input :flap :off]
                        :target [:alive :falling]}]}]]}
     {:name  :dead
      :flows {:x' 0 :y' 0}}]]})

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

(defn all-guards [modes]
  (mapcat #(map :guard (:transitions %)) (vals modes)))
