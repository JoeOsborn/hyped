(ns player.ha-rollout
  [:require
    [player.ha-eval :as heval]
    [ha.intervals :as iv]
    [ha.ha :as ha]])

(def bailout 100)

;todo: replace [start end] with (interval)

(defn next-required-transitions [config]
  (reduce
    (fn [trs [_ha-id ha]]
      (let [rt (first (:required-transitions ha))]
        (cond
          (nil? rt) trs
          (or (empty? trs)
              (< (iv/start (:interval rt))
                 (iv/start (:interval (first trs))))) [rt]
          (= (iv/start (:interval rt))
             (iv/start (:interval (first trs)))) (conj trs rt)
          :else trs)))
    []
    (:objects config)))

(defn constrain-optional-interval-by [weaker stronger]
  (if (and
        (= (:id weaker) (:id stronger))
        (<= (:index (:transition stronger))
            (:index (:transition weaker)))
        (ha/subsumes-inputs? (:transition stronger) (:transition weaker)))
    (let [w' (update weaker :interval #(iv/subtract % (:interval stronger)))]
      (assert (iv/interval? (:interval w')))
      w')
    weaker))

(defn optional-transitions-before [config max-t]
  (reduce
    (fn [trs [_ha-id ha]]
      (let [opts (:optional-transitions ha)
            intvl (iv/interval (:entry-time config) max-t)
            opts (reduce (fn [opts opt]
                           (let [opt (update opt :interval
                                             (fn [ointvl] (iv/intersection ointvl intvl)))
                                 opt (reduce constrain-optional-interval-by opt opts)]
                             (if (iv/empty-interval? (:interval opt))
                               opts
                               (conj
                                 ; if opt dominates c-opt, subtract from that member opt's interval
                                 (filterv #(not (iv/empty-interval? (:interval %)))
                                          (map (fn [c-opt]
                                                 (constrain-optional-interval-by c-opt opt))
                                               opts))
                                 opt))))
                         []
                         opts)]
        (concat trs opts)))
    []
    (:objects config)))

(defn satisficing-input [edge]
  (let [l (:label edge)
        ons (ha/propset-get l :on #{})
        ; we can ignore offs because we assume no conflict between ons and offs
        ; offs (ha/propset-get l :off #{})
        pressed (ha/propset-get l :pressed #{})
        released (ha/propset-get l :released #{})]
    ; this can even produce impossible combinations of inputs,
    ; e.g. same key in both pressed and released, or released and on. don't sweat it!
    {:on ons :pressed pressed :released released}))

; If we go through this many stages where there's only required transitions, give up and declare livelock.
; later, can use some fixpoint semantics.
(def livelock-threshold 10)

(defn simplify-ha [o]
  [(:id o)
   (select-keys o (conj (:variables o) :state))])

(defn see-config [seen c]
  (when seen
    (conj seen (into {} (map simplify-ha (vals (:objects c)))))))

(defn seen-config? [seen c]
  (when seen
    (contains? seen (into {} (mapv simplify-ha (vals (:objects c)))))))

; pick-fn: config X reqs X opts X req-time -> [:required | transition, time]
(defn pick-next-move
  ([config pick-fn] (map (fn [config-move]
                           (vec (take 2 config-move)))
                         (pick-next-move config 0 nil pick-fn)))
  ([config seen-configs pick-fn] (pick-next-move config 0 seen-configs pick-fn))
  ([config req-chain-count seen-configs pick-fn]
   (let [; all simultaneously active required transitions
         reqs (next-required-transitions config)
         ;_ (println "got reqs" reqs)
         required-time (if (not (empty? reqs))
                         (iv/start (:interval (first reqs)))
                         Infinity)
         ; all non-dominated optional transitions
         opts (optional-transitions-before config required-time)]
     (cond
       ; no optional transitions and no required transitions
       (and (empty? reqs) (empty? opts))
       [[config [:end (:entry-time config)] seen-configs]]
       (and (empty? opts) (>= req-chain-count livelock-threshold))
       [[config [:livelock? (:entry-time config)] seen-configs]]
       ; no optional transitions
       ;; the trickery on bailout is to scale up the bailout (which is usually a per-frame thing) with the number of frames to pass
       (empty? opts)
       (do
         #_(println "no opts run to" required-time (ha/ceil-time (+ required-time (/ heval/frame-length 2)) heval/frame-length))
         ;(println "call update")
         (let [config' (heval/update-config config
                                            (ha/ceil-time (+ required-time (/ heval/frame-length 2)) heval/frame-length)
                                            :inert
                                            (+ bailout (* bailout (/ (- required-time (:entry-time config)) heval/frame-length)))
                                            0)]
           (if (seen-config? seen-configs config')
             (do
               ;(println "bail seen 2")
               [[config' [:seen required-time] seen-configs]])
             (concat [[config' [:required required-time] seen-configs]]
                     (pick-next-move config'
                                     (inc req-chain-count)
                                     (see-config seen-configs config')
                                     pick-fn)))))
       ; no required transitions
       ;; note: actually we should "skip over" intervening optional transitions before the selected one even if they overlap on button inputs.
       ;; we should jump to "right before" and then put the inputs in and then proceed one tick
       ;; if two optional transitions are available at a time and the higher-priority one subsumes the lower priority one's inputs, just use the higher one
       ;; this has the effect of making higher priority inputs somewhat more likely to be taken?
       ;; and if that transition _wasn't_ taken, we should revise the move to indicate the one that _was_ taken
       ;;;; this may require new support in heval to indicate which transitions were taken in the past.
       ;; so basically we may need to make many calls to update-config to skip over inputs... unless we want to add heval support for these specially selected inputs. which may be preferable
       ;; picking a time is also a little tricky. Randomly pick a transition and then a time within that transition's range?
       ;; in fact, we can handle the required transitions here too with a designated :required token
       :else
       (let [[choice time] (pick-fn config reqs opts required-time)
             time (if (= choice :required)
                    required-time
                    time)
             inputs (if (= choice :required)
                      :inert
                      [(iv/interval time (+ time heval/frame-length)) (satisficing-input (:transition choice))])]
         (if (= time Infinity)
           [[config [:end (:entry-time config)] (see-config seen-configs config)]]
           (let [_ (assert (number? time))
                 ;_ (println "call update 2")
                 config' (heval/update-config config
                                              (ha/ceil-time (+ time (/ heval/frame-length 2)) heval/time-unit)
                                              inputs
                                              (+ bailout (* bailout (/ (- time (:entry-time config)) heval/frame-length)))
                                              0)]
             (if (seen-config? seen-configs config')
               (do                                          ;(println "bail seen 3")
                 [[config' [:seen time] seen-configs]])
               [[config'
                 [choice time]
                 (see-config seen-configs config')]]))))))))

(def close-duration 120)
(def req-move-prob 0.5)

(defn random-move [config]
  (pick-next-move config
                  #{}
                  (fn [_config reqs options required-time]
                    (let [choice (if (and (not (empty? reqs))
                                          (< (rand) req-move-prob))
                                   :required
                                   (rand-nth options))
                          time (if (= choice :required)
                                 required-time
                                 (let [start (iv/start (:interval choice))
                                       interval (iv/intersection (:interval choice) (iv/interval start (+ start close-duration)))
                                       time (iv/rand-t interval)
                                       _ (assert (not= Infinity time))
                                       floored-time (ha/floor-time time heval/frame-length)
                                       _ (assert (not= Infinity floored-time))]
                                   (if (iv/interval-contains? (:interval choice) floored-time)
                                     floored-time
                                     time)))]
                      [choice time]))))

(defn config-brief [c]
  (into {:entry-time (:entry-time c)} (map (fn [[k v]]
                                             [k (select-keys v (concat [:state :entry-time] (:variables v)))])
                                           (:objects c))))

(defn configs-from [config-moves]
  (mapv first config-moves))

(defn moves-from [config-moves]
  (map (fn [[_ [m t]]]
         [(if (map? m)
            (update m :transition dissoc :guard :update)
            m)
          t])
       config-moves))

(defn seen-configs-from [config-move-seens]
  (nth (last config-move-seens) 2))

; returns all intermediate configs and the terminal config, along with a sequence of moves
(defn random-playout [config len]
  (let [config-move-seens (into [] (reduce
                                     (fn [steps _movenum]
                                       (let [config (first (last steps))
                                             config-move-seens (random-move config)
                                             [last-move _last-move-t] (second (last config-move-seens))]
                                         (if (or (= last-move :end)
                                                 (= last-move :livelock?)
                                                 (= last-move :seen))
                                           (reduced (concat steps config-move-seens))
                                           (concat steps config-move-seens))))
                                     [[config [:start (:entry-time config)]]]
                                     (range len)))
        configs (configs-from config-move-seens)
        ;_ (println "configs:" (map config-brief configs))
        moves (moves-from config-move-seens)
        ; _ (println "moves:" moves)
        ]
    [configs moves]))

(defn find-move [options ha-id target-state time]
  (some (fn [o]
          (and (= (:id o) ha-id)
               (= (get-in o [:transition :target]) target-state)
               (iv/interval-contains? (:interval o) time)
               [o time]))
        options))

(defn find-move-by-edge [options ha-id edge-index]
  (some (fn [o]
          (and (= (:id o) ha-id)
               (= (get-in o [:transition :index]) edge-index)
               o))
        options))

(defn fixed-playout- [config moves]
  (if (empty? moves)
    []
    (let [[m-ha m-target time] (first moves)
          ms (rest moves)
          config-moves (pick-next-move config
                                       (fn [_config' _reqs options required-time]
                                         (if (> required-time time)
                                           (let [found (find-move options m-ha m-target time)]
                                             (assert found
                                                     (str
                                                       "Move " [m-ha m-target time]
                                                       " for HA in state " (get-in _config' [:objects m-ha :state])
                                                       " not available among " (str (mapv (fn [o] [(:id o) (:target (:transition o)) (:interval o)])
                                                                                          (filter #(= (:id %) m-ha) options)))
                                                       " reqs= " (str (mapv (fn [r] [(:id r) (:target (:transition r)) (:interval r)])
                                                                            (filter #(= (:id %) m-ha) _reqs)))))
                                             found)
                                           [:required required-time])))
          [last-config [last-move _last-move-t]] (last config-moves)]
      (when (not (empty? ms))
        (when (= last-move :required)
          ; never skip a move
          (assert (not (> (:entry-time config) time))))
        (assert (not= last-move :end))
        (assert (not= last-move :livelock?)))
      ; did we actually use the desired move? if not, try again with the same moves.
      ; eventually, required-time will surpass time and we can proceed.
      (concat config-moves (fixed-playout- last-config (if (= last-move :required)
                                                         moves
                                                         ms))))))

(defn fixed-playout [config moves]
  (let [config-moves (vec (fixed-playout- config moves))
        configs (configs-from config-moves)
        moves (moves-from config-moves)]
    [configs moves]))

(defn next-config [config]
  (let [reqs (next-required-transitions config)
        required-time (if (empty? reqs)
                        Infinity
                        (iv/start (:interval (first reqs))))]
    (if (= required-time Infinity)
      config
      (heval/update-config config
                           (ha/ceil-time (+ required-time (/ heval/frame-length 2)) heval/frame-length)
                           :inert
                           (+ bailout (* bailout (/ (- required-time (:entry-time config)) heval/frame-length)))
                           0))))

(defn inert-playout [config move-limit seen]
  (let [[steps seen] (reduce (fn [[cs seen] _]
                               (let [here (last cs)
                                     next (next-config here)]
                                 (if (or (= here next)
                                         (seen-config? seen next))
                                   (reduced [cs seen])
                                   [(conj cs next) (see-config seen next)])))
                             [[config] seen]
                             (range 0 move-limit))]
    [(vec (rest steps)) seen]))

; might be nice to have a diagnostic that takes a config and extrapolates it forwards as far as the next required transition,
;; and the next, and the next... building up a set of seen valuations. maybe just up to a bounded depth. would be an easy diagnostic.
;; could even do it by writing into a bitmap or something.

(defn next-transitions [config]
  (let [reqs (next-required-transitions config)
        req-t (if (not (empty? reqs))
                (iv/start (:interval (first reqs)))
                Infinity)
        opts (optional-transitions-before config req-t)]
    [reqs opts]))

(defn follow-transition [config choice time]
  (let [reqs (next-required-transitions config)
        required-time (if (not (empty? reqs))
                        (iv/start (:interval (first reqs)))
                        Infinity)
        time (if (= choice :required)
               required-time
               time)
        inputs (if (= choice :required)
                 :inert
                 [(iv/interval time (+ time heval/frame-length)) (satisficing-input (:transition choice))])]
    (if (= time Infinity)
      config
      (let [_ (assert (number? time))
            ;_ (println "call update 2")
            config' (heval/update-config config
                                         (ha/ceil-time (+ time (/ heval/frame-length 2)) heval/time-unit)
                                         inputs
                                         (+ bailout (* bailout (/ (- time (:entry-time config)) heval/frame-length)))
                                         0)]
        config'))))