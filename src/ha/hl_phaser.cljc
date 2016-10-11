(ns ha.hl-phaser
  (:require [ha.ha2 :as ha2]
            [ha.hl-to-js :as js]
            [clojure.spec :as s]
            [clojure.string :as string]
            [clojure.set :as sets])
  (:use ha.hl-utils))

(defn default-assign [target nom dict default]
  [:if [:contains-key dict nom]
   [:assign [:deref target nom] [:deref dict nom]]
   [:assign [:deref target nom] default]])

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
         [game-var
          [:list [ha-var]]
          (when a-tags [:list (map name a-tags)])
          (when normals [:list (vec normals)])
          nil
          (when b-tags [:list (map name b-tags)])]]]
       [:assign status-var [:< 0 :contacts.length]]])
    (do
      (println "Unrecognized guard " g)
      (s/unform ::guard g))))

(defn phaserize [ha-desc opts]
  (let [{:keys [:bodies :cvars :dvars :params :flows :modes :tags] :as ha-desc}
        (s/conform :ha2/ha-desc ha-desc)
        ha-name                 (:name ha-desc)
        flat-modes              (ha2/flatten-modes modes)
        guards                  (concat
                                 (map :guard bodies)
                                 (ha2/all-guards flat-modes))
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
           (for [m (ha2/initial-modes (:modes ha-desc))]
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
     (js/jsify-root opts hlcode))))
