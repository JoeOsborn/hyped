(ns player.ha-rollout
  [:require
    [player.ha-eval :as heval]
    [ha.intervals :as iv]
    [ha.ha :as ha]])

(def bailout 100)

(defn next-required-transitions [config]
  (reduce
    (fn [trs [_ha-id ha]]
      (let [rt (first (:required-transitions ha))]
        (cond
          (nil? rt) trs
          (or (empty? trs)
              (< (iv/start-time (:interval rt))
                 (iv/start-time (:interval (first trs))))) [rt]
          (= (iv/start-time (:interval rt))
             (iv/start-time (:interval (first trs)))) (conj trs rt)
          :else trs)))
    []
    (:objects config)))

(defn constrain-optional-interval-by [weaker stronger]
  (if (and
        (= (:id weaker) (:id stronger))
        (ha/subsumes-inputs? (:transition stronger) (:transition weaker))
        (>= (:priority (:transition stronger))
            (:priority (:transition weaker))))
    (update weaker :interval #(iv/subtract % (:interval stronger)))
    weaker))

(defn optional-transitions-before [config max-t]
  (reduce
    (fn [trs [_ha-id ha]]
      (let [opts (:optional-transitions ha)
            intvl [(:entry-time config) max-t]
            opts (reduce (fn [opts opt]
                           (let [opt (update opt :interval
                                             (fn [ointvl] (iv/intersection ointvl intvl)))
                                 opt (reduce constrain-optional-interval-by opt opts)]
                             (if (iv/empty-interval? (:interval opt))
                               opts
                               (conj
                                 ; if opt dominates c-opt, subtract from that member opt's interval
                                 (filter #(not (iv/empty-interval? (:interval %)))
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

; If we go through 100 stages where there's only required transitions, give up and declare livelock.
; later, can use some fixpoint semantics.
(def livelock-threshold 10)

; pick-fn: config X reqs X opts X req-time -> [:required | transition, time]
(defn pick-next-move
  ([config pick-fn] (pick-next-move config 0 pick-fn))
  ([config req-chain-count pick-fn]
    ; a move is a [time ha-id edge-index] tuple, and this code is responsible for looking up that edge and picking the right
    ; on- and off-inputs to match it.
    ; pick any random move. this could also be "wait until the next required transition and pick a random move"
   (let [; all simultaneously active required transitions
         reqs (next-required-transitions config)
         _ (println "got reqs" reqs)
         required-time (if (not (empty? reqs))
                         (iv/start-time (:interval (first reqs)))
                         Infinity)
         ; all non-dominated optional transitions
         opts (optional-transitions-before config required-time)]
     (cond
       ; no optional transitions and no required transitions
       (and (empty? reqs) (empty? opts)) (do (println "dead?!" config)
                                             [config :end])
       (and (empty? opts) (>= req-chain-count livelock-threshold)) (do (println "livelock?")
                                                                       [config :livelock?])
       ; no optional transitions
       ;; the trickery on bailout is to scale up the bailout (which is usually a per-frame thing) with the number of frames to pass
       (empty? opts) (do (println "no opts run to" required-time (ha/ceil-time (+ required-time (/ heval/frame-length 2)) heval/frame-length))
                         (pick-next-move (heval/update-config config
                                                              (ha/ceil-time (+ required-time (/ heval/frame-length 2)) heval/frame-length)
                                                              :inert
                                                              (+ bailout (* bailout (/ (- required-time (:entry-time config)) heval/frame-length)))
                                                              0)
                                         (inc req-chain-count)
                                         pick-fn))
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
       :else (let [[choice time] (pick-fn config reqs opts required-time)]
               (assert (number? time))
               (assert (number? required-time))
               (if (= choice :required)
                 (do (println "picked required thing")
                     (assert (not= required-time Infinity))
                     (pick-next-move (heval/update-config config
                                                          (ha/ceil-time (+ required-time (/ heval/frame-length 2)) heval/frame-length)
                                                          :inert
                                                          (+ bailout (* bailout (/ (- required-time (:entry-time config)) heval/frame-length)))
                                                          0)
                                     ; reset livelock chain count, since there were options available
                                     0
                                     pick-fn))
                 (let [inputs [[time (+ time heval/frame-length)] (satisficing-input (:transition choice))]]
                   (assert (not= time Infinity))
                   (println "doit")
                   [(heval/update-config config
                                         (ha/ceil-time (+ time (/ heval/frame-length 2)) heval/time-unit)
                                         inputs
                                         (+ bailout (* bailout (/ (- time (:entry-time config)) heval/frame-length)))
                                         0)
                    [choice time]])))))))

(def close-duration 120)
(def req-move-prob 0.5)

(defn random-move [config]
  (pick-next-move config
                  (fn [_config reqs options required-time]
                    (let [choice (if (and (not (empty? reqs))
                                          (< (rand) req-move-prob))
                                   :required
                                   (rand-nth options))
                          time (if (= choice :required)
                                 required-time
                                 (let [start (iv/start-time (:interval choice))
                                       interval (iv/intersection (:interval choice) [start (+ start close-duration)])
                                       time (iv/rand-t interval)
                                       _ (assert (not= Infinity time))
                                       floored-time (ha/floor-time time heval/frame-length)
                                       _ (assert (not= Infinity floored-time))]
                                   (if (iv/interval-contains? (:interval choice) floored-time)
                                     floored-time
                                     time)))]
                      [choice time]))))

(defn steps [stepfn so-far value c]
  (if (empty? c)
    (conj so-far value)
    (let [f (first c)
          r (rest c)
          result (stepfn value f)]
      (if (and (vector? result) (= (first result) :reduced))
        (conj so-far value (second result))
        (steps stepfn (conj so-far value) result r)))))

(defn config-brief [c]
  (into {:entry-time (:entry-time c)} (map (fn [[k v]]
                                             [k (into {} (map (fn [vbl] [vbl (get v vbl)])
                                                              (concat [:state :entry-time] (:variables v))))])
                                           (:objects c))))

; returns all intermediate configs and the terminal config, along with a sequence of moves
(defn random-playout [config len]
  (let [config-moves (steps
                       (fn [[config moves] _movenum]
                         (let [[config' move] (random-move config)
                               moves' (conj moves move)]
                           (if (or (= move :end) (= move :livelock?))
                             [:reduced [config' moves']]
                             [config' moves'])))
                       []
                       [config []]
                       (range len))
        configs (mapv first config-moves)
        _ (println "configs:" (map config-brief
                                   configs))
        moves (map (fn [[m t]]
                     [(if (map? m)
                        (update m :transition dissoc :guard :update)
                        m)
                      t])
                   (second (last config-moves)))
        _ (println "moves:" moves)]
    [configs moves]))

; might be nice to have a diagnostic that takes a config and extrapolates it forwards as far as the next required transition,
;; and the next, and the next... building up a set of seen valuations. maybe just up to a bounded depth. would be an easy diagnostic.
;; could even do it by writing into a bitmap or something.