(ns player.ha-rollout
  [:require
    [player.ha-eval :as heval]
    [ha.intervals :as iv]
    [ha.ha :as ha]])

(def bailout 100)

(defn next-required-transitions [scene]
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
    (:objects scene)))

(defn constrain-optional-interval-by [weaker stronger]
  (if (and
        (= (:id weaker) (:id stronger))
        (ha/subsumes-inputs? (:transition stronger) (:transition weaker))
        (>= (:priority (:transition stronger))
            (:priority (:transition weaker))))
    (update weaker :interval #(iv/subtract % (:interval stronger)))
    weaker))

(defn optional-transitions-before [scene max-t]
  (reduce
    (fn [trs [ha-id ha]]
      (let [opts (:optional-transitions ha)
            intvl [(:now scene) max-t]
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
    (:objects scene)))

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

; pick-fn: scene X reqs X opts X req-time -> [:required | transition, time]
(defn pick-next-move
  ([scene pick-fn] (pick-next-move scene 0 pick-fn))
  ([scene req-chain-count pick-fn]
    ; a move is a [time ha-id edge-index] tuple, and this code is responsible for looking up that edge and picking the right
    ; on- and off-inputs to match it.
    ; pick any random move. this could also be "wait until the next required transition and pick a random move"
   (let [; all simultaneously active required transitions
         reqs (next-required-transitions scene)
         _ (println "got reqs" reqs)
         required-time (if (not (empty? reqs))
                         (iv/start-time (:interval (first reqs)))
                         Infinity)
         ; all non-dominated optional transitions
         opts (optional-transitions-before scene required-time)]
     (cond
       ; no optional transitions and no required transitions
       (and (empty? reqs) (empty? opts)) (do (println "dead?!" scene)
                                             [scene :end])
       (and (empty? opts) (>= req-chain-count livelock-threshold)) (do (println "livelock?")
                                                                       [scene :livelock?])
       ; no optional transitions
       ;; the trickery on bailout is to scale up the bailout (which is usually a per-frame thing) with the number of frames to pass
       (empty? opts) (do (println "no opts run to" required-time (ha/ceil-time (+ required-time (/ heval/frame-length 2)) heval/frame-length))
                         (pick-next-move (heval/update-scene scene
                                                             (ha/ceil-time (+ required-time (/ heval/frame-length 2)) heval/frame-length)
                                                             :inert
                                                             (+ bailout (* bailout (/ (- required-time (:now scene)) heval/frame-length)))
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
       ;; so basically we may need to make many calls to update-scene to skip over inputs... unless we want to add heval support for these specially selected inputs. which may be preferable
       ;; picking a time is also a little tricky. Randomly pick a transition and then a time within that transition's range?
       ;; in fact, we can handle the required transitions here too with a designated :required token
       :else (let [[choice time] (pick-fn scene reqs opts required-time)]
               (assert (number? time))
               (assert (number? required-time))
               (if (= choice :required)
                 (do (println "picked required thing")
                     (assert (not= required-time Infinity))
                     (pick-next-move (heval/update-scene scene
                                                         (ha/ceil-time (+ required-time (/ heval/frame-length 2)) heval/frame-length)
                                                         :inert
                                                         (+ bailout (* bailout (/ (- required-time (:now scene)) heval/frame-length)))
                                                         0)
                                     ; reset livelock chain count, since there were options available
                                     0
                                     pick-fn))
                 (let [inputs (satisficing-input (:transition choice))
                       _ (assert (not= time Infinity))
                       _ (println "picked" choice "run upto" time)
                       upto (heval/update-scene scene
                                                (ha/floor-time time heval/time-unit)
                                                :inert
                                                (+ bailout (* bailout (/ (- time (:now scene)) heval/frame-length)))
                                                0)]
                   (println "doit")
                   [(heval/update-scene upto
                                        (ha/ceil-time (+ time (/ heval/frame-length 2)) heval/time-unit)
                                        inputs
                                        bailout
                                        0) [choice time]])))))))

(def close-duration 120)

(defn random-move [scene]
  (pick-next-move scene
                  (fn [scene reqs opts required-time]
                    (let [options (if (empty? reqs)
                                    opts
                                    (conj opts :required))
                          choice (rand-nth options)
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

(defn scene-brief [s]
  (into {:now (:now s)} (map (fn [[k v]]
                               [k (into {} (map (fn [vbl] [vbl (get v vbl)])
                                                (concat [:state :entry-time] (:variables v))))])
                             (:objects s))))

; returns all intermediate scenes and the terminal scene, along with a sequence of moves
(defn random-playout [scene len]
  (let [scene-moves (steps
                      (fn [[scene moves] _movenum]
                        (let [[scene' move] (random-move scene)
                              moves' (conj moves move)]
                          (if (or (= move :end) (= move :livelock?))
                            [:reduced [scene' moves']]
                            [scene' moves'])))
                      []
                      [scene []]
                      (range len))
        scenes (mapv first scene-moves)
        _ (println "scenes:" (map scene-brief
                                  scenes))
        moves (second (last scene-moves))
        _ (println "moves:" moves)]
    [scenes moves]))

; might be nice to have a diagnostic that takes a scene and extrapolates it forwards as far as the next required transition,
;; and the next, and the next... building up a set of seen valuations. maybe just up to a bounded depth. would be an easy diagnostic.
;; could even do it by writing into a bitmap or something.