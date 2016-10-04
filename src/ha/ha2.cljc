(ns ha.ha2
  (:require [clojure.spec :as s]
            [clojure.spec.gen :as gen]))

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
(s/def ::state-path (s/coll-of ::state-name))
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
;;todo: most/least and local qvar collapsing guards
;;todo: when conforming a collision, input, state, or _todo_ least/most/any/all/... guard, tag the local qvar with type info
;;todo: note that we don't need to do all that now. just focus on flappy at the moment, do the minimum possible for that.
(s/def ::guard (s/or ::input-guard ::input-guard
                     ::collision-guard ::collision-guard
                     ::state-guard ::state-guard
                     ::rel-guard ::rel-guard
                     ::unlink-guard ::unlink-guard
                     ::boolean-guard ::boolean-guard))

(s/def ::target ::state-path)
(s/def ::update (s/map-of ::var-name ::arith-expr))
(s/def ::transition (s/keys :req-un [::target ::guard] :opt-un [::update]))
(s/def ::flows (s/map-of ::var-name ::arith-expr))
(s/def ::name (s/with-gen simple-keyword? var-name-gen))
(s/def ::modes (s/coll-of ::mode))
(s/def ::mode (s/keys :req-un [::name]
                      :opt-un [::flows ::modes ::transitions]))
(s/def ::params (s/map-of ::var-name ::var-decl))
(s/def ::prim (s/cat ::shape #{:rect}
                     ::x ::arith-expr
                     ::y ::arith-expr
                     ::w ::arith-expr
                     ::h ::arith-expr))
(s/def ::tag (s/with-gen simple-keyword? var-name-gen))
(s/def ::tags (s/coll-of ::tag))
(s/def ::body (s/keys :req-un [::prim ::tags]))
(s/def ::bodies (s/coll-of ::body))
(s/def ::var-domain (s/cat ::init number? ::domain #{:number}))
(s/def ::var-decls (s/map-of ::var-name ::var-domain))
(s/def ::cvars ::var-decls)
(s/def ::dvars ::var-decls)
(s/def ::implicit-flows ::flows)
(s/def ::ha
  ;;todo conform cvars and flows to include the defaults, and also add implicit flows in a separate key, and add params, dvars, etc lists
  (s/keys :req-un [::bodies ::flows ::modes]
          :opt-un [::params ::cvars ::dvars ::implicit-flows]))
(def flappy
  {:params {:flap-speed [40 :number] :move-speed [10 :number]}
   :bodies [{:prim [:rect 0 0 16 16] :tags [:body]}]
   :flows {:y' -10}
   :modes
   [{:name :alive
     :flows {:x' :move-speed}
     :transitions [{:guard [:touching :body :wall]
                    :target [:dead]}]
     :modes
     [{:name :falling
       :transitions [{:guard [:input :flap :on]
                      :target [:alive :flapping]}]}
      {:name :flapping
       :flows {:y' :flap-speed}
       :transitions [{:guard [:input :flap :off]
                      :target [:alive :falling]}]}]}
    {:name :dead
     :flows {:x' 0 :y' 0}}]})

