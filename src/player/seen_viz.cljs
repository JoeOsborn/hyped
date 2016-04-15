(ns player.seen-viz
  (:require [ha.ha :as ha]
            [player.ha-eval :as heval]
            [clojure.string :as string]))

(defn solve-t-xy [v0 flow vt min-t max-t]
  ; issue: what if there are multiple solutions? just take the first valid one.
  ; find t s.t. x0 + xflow(t) = xt and y0 + yflow(t) = yt
  ; must be same t!
  ; and s.t. <= min-t t max-t
  (let [xt (:x vt)
        yt (:y vt)]
    (if (and (= xt (:x v0))
             (= yt (:y v0)))
      min-t
      (let [; at^2+bt+c = x, plus valid ranges
            x-eqns (ha/flow-equations v0 flow :x)
            ; at^2+bt+c = y
            y-eqns (ha/flow-equations v0 flow :y)
            ; at^2+bt+c-xt = 0
            x-solutions (mapcat (fn [[a b c start end]]
                                  (let [c (- c xt)
                                        roots (ha/find-roots a b c)]
                                    (filter #(<= start % end) roots)))
                                x-eqns)
            y-solutions (mapcat (fn [[a b c start end]]
                                  (let [c (- c yt)
                                        roots (ha/find-roots a b c)]
                                    (filter #(<= start % end) roots)))
                                y-eqns)
            ;_ (println "xs" x-solutions "ys" y-solutions)
            x-solutions-working-for-y (filter #(= (:y (ha/extrapolate-flow v0 flow [:y] %))
                                                  yt)
                                              x-solutions)
            y-solutions-working-for-x (filter #(= (:x (ha/extrapolate-flow v0 flow [:x] %))
                                                  xt)
                                              y-solutions)

            ;_ (println "xs2" x-solutions-working-for-y "ys2" y-solutions-working-for-x)
            first-soln (first (concat x-solutions-working-for-y y-solutions-working-for-x))]
        (if (some? first-soln)
          (ha/floor-time first-soln
                         heval/time-unit)
          :no-solution)))))

(defn shrink-seen-poly [[nid nstate nv0 nflow nd :as np] [id state v0 flow d :as op]]
  ;(assert (= nid id))
  (cond
    ; incomparable
    (or (not= nflow flow)
        (not= nstate state)) [np]
    ; exactly covered
    (= np op) []
    :else (let [
                ;_ (println "ne" (ha/extrapolate-flow nv0 nflow nd))
                ;_ (println "oe" (ha/extrapolate-flow v0 flow d))
                ; find t < nd s.t. nv0+nflow(t) = v0
                old-start-in-new-terms (solve-t-xy nv0 nflow
                                                   v0
                                                   0 nd)
                ;_ (println "os-in-nt" old-start-in-new-terms)
                ; find t < nd s.t. v0+flow(nd) = nv0+nflow(t)
                old-end-in-new-terms (solve-t-xy nv0 nflow
                                                 (ha/extrapolate-flow v0
                                                                      flow
                                                                      [:x :y :v/x :v/y]
                                                                      d)
                                                 0 nd)
                ;_ (println "oe-in-nt" old-end-in-new-terms)
                ; find t < d s.t. v0+flow(t) = nv0
                new-start-in-old-terms (solve-t-xy v0 flow
                                                   nv0
                                                   0 d)
                ;_ (println "ns-in-ot" new-start-in-old-terms)
                ; find t < d s.t. nv0+nflow(nd) = v0+flow(t)
                new-end-in-old-terms (solve-t-xy v0 flow
                                                 (ha/extrapolate-flow nv0
                                                                      nflow
                                                                      [:x :y :v/x :v/y]
                                                                      nd)
                                                 0 d)
                ;_ (println "ne-in-ot" new-end-in-old-terms)
                ; os-in-new?. is oldp's start inside of np?
                os-in-new? (and (not= old-start-in-new-terms :no-solution)
                                (<= 0 old-start-in-new-terms nd))
                ; oe-in-new?. is oldp's end inside of np?
                oe-in-new? (and (not= old-end-in-new-terms :no-solution)
                                (<= 0 old-end-in-new-terms nd))
                ; ns-in-old? is np's start inside of oldp?
                ns-in-old? (and (not= new-start-in-old-terms :no-solution)
                                (<= 0 new-start-in-old-terms d))
                ; ne-in-old?. is np's end inside of oldp?
                ne-in-old? (and (not= new-end-in-old-terms :no-solution)
                                (<= 0 new-end-in-old-terms d))]
            #_(println "shrink" nid [nv0 nd] "\n" flow "\n" "by" [v0 d] "\n" os-in-new? oe-in-new? "\n" ns-in-old? ne-in-old?)
            (cond
              ; exactly covered
              (and ns-in-old? ne-in-old? os-in-new? oe-in-new?) []
              ; subsumed
              (and ns-in-old? ne-in-old?) []
              ; contains old. we have to either drop old or split new into 2.
              ; but it's OK by me if we just keep old around and don't shrink new.
              ; unfortunately, future shrinks could make new exactly the same as old!
              ; so we have to make one or the other choice.
              ; it's easier to add two than to remove one, so we do that.
              (and os-in-new? oe-in-new?) (do
                                            #_(println "split poly")
                                            ;(assert (not= old-start-in-new-terms :no-solution))
                                            ;(assert (not= old-end-in-new-terms :no-solution))
                                            [[nid
                                              nstate
                                              nv0
                                              nflow
                                              old-start-in-new-terms]
                                             [nid
                                              nstate
                                              (ha/extrapolate-flow
                                                nv0
                                                nflow
                                                [:x :y :v/x :v/y]
                                                old-end-in-new-terms)
                                              nflow
                                              (- nd old-end-in-new-terms)]])
              ; overlapping (new start outside, new end inside)
              ; shrink new to just new-start...old-start
              (and (not ns-in-old?) ne-in-old? os-in-new?) (do
                                                             #_(println "shrink end to" old-start-in-new-terms)
                                                             ;(assert (not= old-start-in-new-terms :no-solutions))
                                                             [[nid
                                                               nstate
                                                               nv0
                                                               nflow
                                                               old-start-in-new-terms]])
              ; overlapping (new start inside, new end outside)
              ; shrink new to just old-end...new-end
              (and ns-in-old? (not ne-in-old?) oe-in-new?) (do
                                                             #_(println "shrink start to" old-end-in-new-terms)
                                                             ;(assert (not= old-end-in-new-terms :no-solution))
                                                             [[nid
                                                               nstate
                                                               (ha/extrapolate-flow
                                                                 nv0
                                                                 nflow
                                                                 [:x :y :v/x :v/y]
                                                                 old-end-in-new-terms)
                                                               nflow
                                                               (- nd old-end-in-new-terms)]])
              ; otherwise, no overlap: just yield the new one unchanged
              :else [np]))))

(defn merge-seen-poly [seen-for-ha ha hav end-time]
  ;(assert (ha/ha? ha))
  ;(assert (ha/ha-val? hav))
  (let [rs (reduce (fn [new-ps old-p]
                     (let [rs (mapcat #(shrink-seen-poly % old-p) new-ps)]
                       (if (empty? rs)
                         (reduced [])
                         rs)))
                   [[(:id hav)
                     (:state hav)
                     (:v0 hav)
                     (:flows (ha/current-state ha hav))
                     (- end-time (:entry-time hav))]]
                   ; reverse it because the new poly is probably similar to more recent polys
                   (reverse seen-for-ha))]
    (apply conj seen-for-ha rs)))


(defn clip [a b c]
  (max a (min b c)))

(defn path-str [h [_ha-id _ha-state {x :x y :y :as v0} flow duration]]
  ; poly-spec is an ha ID, an initial valuation, a flow, and a duration
  (let [{x' :x y' :y} (ha/extrapolate-flow v0 flow [:x :y] duration)
        cx (clip -1000 (+ x 8) 1000)
        cy (clip -1000 (- h (+ y 8)) 1000)
        cx' (clip -1000 (+ x' 8) 1000)
        cy' (clip -1000 (- h (+ y' 8)) 1000)]
    (str "M " cx "," cy " L " cx' "," cy')))

(defn seen-viz [world-h polys]
  [:g {:key "seen-viz"}
   (map (fn [poly]
          [:path {:key   (str poly)
                  :d     (path-str world-h poly)
                  :style {:strokeWidth 16 :stroke "rgba(200,255,200,0.25)"}}]
          #_[:polygon {:key    (str poly)
                       :points (poly-str world-h poly)
                       :style  {:fill   "rgba(200,255,200,0.25)"
                                :stroke "none"}}])
        polys)])