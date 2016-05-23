(ns player.editor
  (:require
    [player.worlds :as worlds]
    [ha.ha :as ha]))

(defn make-editor []
  ; todo: move editor scrolling info here?
  {:selection   #{}
   :create-mode {:name      "Wall"
                 :type      :wall
                 :key       :wall
                 :prototype {:type :white
                             :x    0 :y 0
                             :w    16 :h 16}}})

(defn walls-under [wld wx wy]
  (keep (fn [[id {x :x y :y w :w h :h :as wall}]]
          (when (and (<= x wx (+ x w))
                     (<= y wy (+ y h)))
            [id wall]))
        (:walls (:desc wld))))

(defn ha-starts-under [wld wx wy]
  (keep (fn [[id ha]]
          ;todo: fix this to use colliders
          (when (and (<= (:x ha) wx (+ (:x ha) (:w ha)))
                     (<= (:y ha) wy (+ (:y ha) (:h ha))))
            [id ha]))
        (:objects (:desc wld))))

(defn has-under [wld wx wy]
  (let [ha-defs (:ha-defs wld)
        has (:objects (worlds/current-config wld))]
    (filter #(let [ha-val (ha/extrapolate (get ha-defs (:id %)) % (:now wld))
                   v0 (.-v0 ha-val)]
              #_(println "check" wx wy v0)
              (and (<= (:x v0) wx (+ (:x v0) (:w v0)))
                   (<= (:y v0) wy (+ (:y v0) (:h v0)))))
            (vals has))))

(defn things-under [wld x y]
  (concat (map (fn [[id _wall]]
                 [:walls id])
               (walls-under wld x y))
          (map (fn [[id _ha-desc]]
                 [:objects id])
               (ha-starts-under wld x y))
          (map (fn [{id :id}]
                 [:live-objects id])
               (has-under wld x y))))

(defn random-id
  ([ha-type existing-ids] (random-id ha-type existing-ids (count existing-ids)))
  ([ha-type existing-ids candidate-index]
   (let [cand (keyword (str ha-type "-" candidate-index))]
     (if (contains? existing-ids cand)
       (random-id ha-type existing-ids (inc candidate-index))
       cand))))

(defn ha->desc [{v0 :v0 state :state ha-type :ha-type id :id}]
  (assoc v0 :state state :type ha-type :id id))

(defn editor-start-new-thing [ed x y now-x now-y]
  (let [{type :type proto :prototype} (:create-mode ed)
        new-id (case type
                 :wall (inc (apply max (map first (:walls (:draft-desc ed)))))
                 :ha (random-id (:type proto)
                                (set (keys (:objects (:draft-desc ed))))))
        _ (println "create new thing" new-id x y now-x now-y)
        new-thing-handle [(case type
                            :wall :walls
                            :ha :objects)
                          new-id]
        ax x
        ay y
        bx now-x
        by now-y]
    (assoc ed
      :move-mode (case type
                   :wall :resizing
                   :ha :moving)
      :selection #{new-thing-handle}
      :draft-desc (assoc-in
                    (:draft-desc ed)
                    new-thing-handle
                    (merge
                      proto
                      (case type
                        :wall
                        {:x (.min js/Math ax bx)
                         :y (.min js/Math ay by)
                         :w (.abs js/Math (- bx ax))
                         :h (.abs js/Math (- by ay))}
                        :ha
                        {:x x :y y}))))))

(defn editor-move-selection [ed wld dx dy]
  (println "move selection" (:selection ed) "of" (:draft-desc ed) "by" dx dy)
  (assoc ed
    :move-mode :moving
    :draft-desc
    (reduce
      (fn [desc sel-path]
        (println "update" sel-path "of" desc)
        (update-in desc sel-path (fn [obj]
                                   (let [{x :x y :y :as obj}
                                         (if (and (= (first sel-path) :live-objects) (nil? obj))
                                           ;copy from world
                                           (ha->desc (get-in (worlds/current-config (worlds/reenter-current-config wld))
                                                             [:objects (second sel-path)]))
                                           obj)]
                                     (println "move selection" obj "to" (+ x dx) (+ y dy))
                                     (assoc obj :x (+ x dx)
                                                :y (+ y dy))))))
      (:draft-desc ed)
      (:selection ed))))

(defn editor-resize-selection [ed wld dx dy]
  (println "resize selection"
           (first (:selection ed))
           (get-in (:draft-desc ed)
                   (first (:selection ed)))
           "by" dx dy)
  (let [[sx sy] (:last-loc ed)
        obj (get-in (:draft-desc ed) (first (:selection ed)))
        {x :x y :y w :w h :h} (if (nil? obj)
                                ;copy from world
                                (ha->desc (get-in (worlds/current-config (worlds/reenter-current-config wld))
                                                  [:objects (second (first (:selection ed)))]))
                                obj)
        ; if sx is rightish, adjust width only; else adjust width and x
        [nx nw] (if (> sx (+ x (/ w 2)))
                  [x (+ w dx)]
                  [(+ x dx) (- w dx)])
        ; if sy is toppish, adjust height only; else adjust height and y
        [ny nh] (if (> sy (+ y (/ h 2)))
                  [y (+ h dy)]
                  [(+ y dy) (- h dy)])
        [nx nw] (if (< nw 0)
                  [(+ nx nw) (.abs js/Math nw)]
                  [nx nw])
        [ny nh] (if (< nh 0)
                  [(+ ny nh) (.abs js/Math nh)]
                  [ny nh])]
    (assoc ed :draft-desc (update-in (:draft-desc ed)
                                     (first (:selection ed))
                                     assoc
                                     :x nx :y ny
                                     :w nw :h nh)
              :move-mode :resizing)))

(def resize-threshold 2)
(def drag-threshold 2)

(defn wall-centerish-point? [{x :x y :y w :w h :h} wx wy]
  (and (<= (+ x resize-threshold) wx (- (+ x w) resize-threshold))
       (<= (+ y resize-threshold) wy (- (+ y h) resize-threshold))))

(defn selection-init [ed]
  (assoc ed :selection #{}))

(defn selection-add [ed new-sel]
  (if (= (first new-sel) :live-objects)
    (assoc ed :selection (conj (:selection ed) new-sel))
    (update ed :selection conj new-sel)))

(defn selection-remove [ed new-sel]
  (if (= (first new-sel) :live-objects)
    (assoc ed
      :selection (disj (:selection ed) new-sel)
      :draft-desc (update (:draft-desc ed) :live-objects dissoc (second new-sel)))
    (update ed :selection disj new-sel)))

(defn selection-delete [ed wld]
  (let [new-desc (reduce (fn [desc sel]
                           (case (first sel)
                             (:live-objects :objects) (update desc :objects dissoc (second sel))
                             :walls (update desc :walls dissoc (second sel))))
                         (dissoc (or (:draft-desc ed)
                                     (:desc wld))
                                 :live-objects)
                         (:selection ed))]
    (assoc (selection-init ed) :draft-desc new-desc)))

(defn mouse-down [ed wld wx wy shift?]
  (if (and (<= 0 wx (:width wld))
           (<= 0 wy (:height wld)))
    (let [found-things (things-under wld wx wy)
          sel (:selection ed)
          ed (assoc ed
               :draft-desc (:desc wld)
               :mouse-down-loc [wx wy]
               :last-loc [wx wy]
               :move-mode :clicking)
          new-sel (first found-things)
          present? (and new-sel
                        (contains? sel new-sel))]
      (cond
        ; shift-clicked on an object already present --> deselect
        (and new-sel shift? present?)
        (selection-remove ed new-sel)
        ; shift-clicked on a new object --> add to selection
        (and new-sel shift?)
        (selection-add ed new-sel)
        ; regular-clicked on a new object --> change selection to new object
        (and new-sel (not shift?) (not present?))
        (selection-add (selection-init ed)
                       new-sel)
        ;regular clicked on nothing while in HA-placing mode --> place ha
        (and (not new-sel)
             (not shift?)
             (= (:type (:create-mode ed))
                :ha))
        (editor-start-new-thing ed wx wy wx wy)
        ; regular-clicked on nothing while in walls or select mode --> clear selection
        (and (not new-sel)
             (not shift?))
        (selection-init ed)
        ; otherwise (eg regular clicked on a selected object), do nothing
        :else
        ed))
    ed))

(defn mouse-drag [ed wld wx wy]
  (let [[down-x down-y] (or (:mouse-down-loc ed) [nil nil])
        dx (- wx down-x)
        dy (- wy down-y)
        [last-x last-y] (:last-loc ed)
        ddx (- wx last-x)
        ddy (- wy last-y)
        sel (:selection ed)
        mode (:move-mode ed)]
    (assoc
      (cond
        (= mode :resizing)
        ; resize selected object
        (editor-resize-selection ed wld ddx ddy)
        (= mode :moving)
        ; move selected objects
        (editor-move-selection ed wld ddx ddy)
        (>= (.sqrt js/Math (+ (* dx dx) (* dy dy))) drag-threshold)
        (do
          (println "start dragging")
          (cond
            ; no selection
            (empty? sel)
            ;create new object and set sel to it and enter either moving state (for HAs) or resizing state (for walls)
            ; multi-selection or HA selected or mouse in center
            (editor-start-new-thing ed down-x down-y wx wy)
            (or (> (count sel) 1)
                (= :objects (ffirst sel))
                (= :live-objects (ffirst sel))
                (wall-centerish-point? (get-in (:draft-desc ed) (first sel)) wx wy))
            ; move selected object(s)
            (editor-move-selection ed wld dx dy)
            ;(mouse started at edge of selected thing)
            :else
            ; resize selected object if wall
            (editor-resize-selection ed wld dx dy)))
        ; haven't moved enough to drag.
        ; todo: show resize or move cursor appropriately
        :else ed)
      :last-loc [wx wy])))

(defn mouse-up [ed]
  (assoc ed
    :mouse-down-loc nil
    :move-mode nil
    :draft-desc nil))