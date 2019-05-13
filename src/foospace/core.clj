(ns foospace.core
  (:require [quil.core :as q],
            [quil.middleware :as m],
            [clojure.xml :as xml],
            [clojure.string :as str],
            [foospace.tetrahedron :as tet],
            [clojure.zip :as z],
            [clojure.java.io :as io],
            [clojure.spec.alpha :as spec],
            [clojure.core.matrix :as ma],
            [clojure.set :as set],
            [clojure.tools.trace :as tr]))

(def fps 30)
(def frame-delta (/ 1 30))
(def width 300)
(def height 300)
(def raymarch-margin 0.01)

;(defn sdist [pos] (- (ma/length (let [[x y z] pos] [(mod x 1) y z])) 0.5))

;(spec/def ::vertex-data
;  (spec/keys :req-un [ ::pos ::adjacent-cells ]))
;
;(spec/def ::cell-vertices
;  (spec/and (spec/coll-of symbol?) #(= 4 (count %))))
;
;(spec/def ::cell-data
;  (spec/keys :req-un [ ::cell-vertices ::adjacent-cells ]))
;;
;(spec/def ::cells
;  (spec/map-of symbol? ::cell-data))
;
;(spec/def ::tetramesh
;  (spec/and (spec/keys :req-un [::vertices, ::cells])))

(defn all-vertices-exist [mesh]
  (let [vs (flatten (map #((nth % 1) :vertices) (mesh :cells)))]
    (every? #(-> mesh :vertices %) vs)))

(defn vertices-refer-to-cells [mesh]
  (every? (fn [[cId cd]]
            (every? (fn [vId] (contains? (-> mesh :vertices vId :cells) cId))
                    (cd :vertices)))
          (mesh :cells)))

(defn new-vertex-id [] (gensym "v"))
(defn new-cell-id [] (gensym "c"))

(defn single-tetra [p1 p2 p3 p4]
  (let [v1 (new-vertex-id)
        v2 (new-vertex-id)
        v3 (new-vertex-id)
        v4 (new-vertex-id)
        c (new-cell-id)]
    {:tetra-mesh {:vertices {v1 {:cells #{c}, :pos p1}
                             v2 {:cells #{c}, :pos p2}
                             v3 {:cells #{c}, :pos p3}
                             v4 {:cells #{c}, :pos p4}},
                  :cells    {c {:vertices   [v1 v2 v3 v4],
                                :neighbours [nil nil nil nil]}}}
     :cell       c}))

(defn merge-tetramesh [a b]
  {:pre  [(spec/valid? ::tetramesh a) (spec/valid? ::tetramesh b)]
   :post [(partial spec/valid? ::tetramesh)]}
  {:vertices (merge (:vertices a) (:vertices b))
   :cells    (merge (:cells a) (:cells b))})

(defn plane-signeddist [pt plane]
  (let [pt-delta (ma/sub pt (plane :pt))
        angle-cos (/ (ma/dot pt-delta (:normal plane))
                     (* (ma/length pt-delta) (ma/length (:normal plane))))]
    (* angle-cos (ma/distance (:pt plane) pt))))

(defn triangle-normal [a b c]
  {:pre (every? ma/vec? [a b c])}
  (ma/normalise (ma/cross (ma/sub a b) (ma/sub a c))))

(defn plane-from-3pt [a b c]
  {:normal (triangle-normal a b c), :pt a})

(defn triangle-middle [a b c]
  (ma/div (ma/add a b c) 3))

(defn triangle-average-edge-length [a b c]
  (/ (reduce + (map ma/length [(ma/sub a b) (ma/sub a c) (ma/sub b c)])) 3))

(defn tetrahedron-triangles [a b c d]
  [[a b c] [b d c] [c d a] [d b a]])

(defn extract-tetrahedron [tetramesh cell-id]
  (let [vids (:vertices ((:cells tetramesh) cell-id))]
    (map (fn [vid] (:pos ((:vertices tetramesh) vid))) vids)))

(def default-tetra (:tetra-mesh (single-tetra [-1 0 -1] [1 0 -1] [-1 0 1] [0 1 0])))

(defn score [tetramap]
  (-> default-tetra :cells count))

(defn celldata-faces [cId cell]
  (map (fn [cId fId nCid] {:cellId cId, :faceIdx fId, :neighbour-cell nCid})
       (repeat cId) (range) (cell :neighbours)))

(defn cell-faces [mesh cId]
  (celldata-faces cId (get-in mesh [:cells cId])))

(defn empty-faces [tetra-mesh]
  (flatten
    (map (fn [[cId cell]]
           (filter (comp nil? :neighbour-cell) (celldata-faces cId cell)))
         (:cells tetra-mesh))))

(defn point-in-tetrahedron [pt pts]
  (every? #(< (plane-signeddist pt (apply plane-from-3pt %)) 0)
          (apply tetrahedron-triangles pts)))

(defn point-in-tetramesh [pt mesh]
  (some (#(point-in-tetrahedron pt (extract-tetrahedron mesh %)))
        (-> mesh :cells keys)))

(defn tetrahedron-overlaps [tetra mesh]
  (some #(tet/intersect-tetrahedra? tetra (extract-tetrahedron mesh %))
        (-> mesh :cells keys)))

(defn extract-face-vertexids [face mesh]
  (let [cell-vIds (-> mesh :cells ((:cellId face)) :vertices)
        triangles (apply tetrahedron-triangles cell-vIds)]
    (nth triangles (:faceIdx face))))

(defn add-cell-to-vertex [mesh vId cId]
  (update-in mesh [:vertices vId :cells] #(conj % cId)))

(defn add-cell-to-vertices [mesh vIds cId]
  (reduce (fn [acc vtx] (add-cell-to-vertex acc vtx cId)) mesh vIds))

(defn pick-exposed-face [mesh]
  (rand-nth (empty-faces mesh)))

(defn point-in-front-of-triangle [pts]
  (ma/add-scaled (apply triangle-middle pts)
                 (apply triangle-normal pts)
                 (apply triangle-average-edge-length pts)))

(defn shrink-to-middle [vtx]
  (let [middle (ma/div (apply ma/add vtx) (count vtx))]
    (map #(ma/scale-add % 0.99 middle 0.1) vtx)))

(defn face-is-exposed [mesh face]
  (and
    (not (nil? (get-in mesh [:cells (:cellId face) :neighbours])))
    (nil? (get-in mesh [:cells (:cellId face) :neighbours (:faceIdx face)]))))

(defn vertex-pos [mesh vId]
  (get-in mesh [:vertices vId :pos]))

(defn tetrahedron-clear [mesh tetra-vtx]
  (not (tetrahedron-overlaps (shrink-to-middle tetra-vtx) mesh)))

(defn try-add-cell-on-exposed [mesh face]
  ;{:pre  [(spec/valid? ::tetramesh mesh)
  ;        (face-is-exposed mesh face)]
  ; :post [(partial spec/valid? ::tetramesh)]}
  (let [face-vertexIds (extract-face-vertexids face mesh)
        face-vertexPos (map (partial vertex-pos mesh) face-vertexIds)
        new-vtx-pos (point-in-front-of-triangle face-vertexPos)]
    (if (tetrahedron-clear mesh (cons new-vtx-pos face-vertexPos))
      (let [new-vtx-id (new-vertex-id)
            new-cell-id (new-cell-id)
            new-mesh (-> mesh
                         (#(assoc-in % [:vertices new-vtx-id]
                                     {:cells #{new-cell-id} :pos new-vtx-pos}))
                       (#(assoc-in % [:cells new-cell-id]
                                   {:vertices   (reverse (cons new-vtx-id face-vertexIds))
                                    :neighbours [(:cellId face) nil nil nil]}))
                       (#(assoc-in % [:cells (:cellId face) :neighbours (:faceIdx face)] new-cell-id))
                       (#(add-cell-to-vertices % face-vertexIds new-cell-id)))]
        {:mesh-after new-mesh :new-cell new-cell-id})
      :no-clear-space)))

(def init-state
  {:mesh default-tetra})

(defn unordered-combinations [elts]
  (if (or (empty? elts) (empty? (rest elts)))
    nil
    (let [[a & rest] elts]
      (concat (map #(set [%1 %2]) (repeat a) rest)
              (unordered-combinations rest)))))

(defn vertices-share-edge [mesh va-id vb-id]
  (not-empty (set/intersection (-> mesh :vertices va-id :cells)
                               (-> mesh :vertices vb-id :cells))))

(defn select-nearby-nonlinked-vertex-pair [mesh]
  (let [bin-size 1
        jitter (/ bin-size 2)]
    (let [verts (mesh :vertices)
          pos-bin (fn [[vId {pos :pos}]] (map #(int (/ (+ jitter %) bin-size)) pos))
          ;unpack-group (fn [[bin [vId v-data]]] (tr/trace "vId" vId))
          binned-verts (map #(map first (nth % 1)) (group-by pos-bin verts))
          potential-pairs (apply concat (map unordered-combinations binned-verts))
          nonlinked-pairs (filter (fn [ab] (not (apply (partial vertices-share-edge mesh) (seq ab))))
                                  potential-pairs)]
      (if (empty? nonlinked-pairs) nil (rand-nth nonlinked-pairs)))))

(defn cell-replace-vertex [mesh cId vBefore vAfter]
  (update-in mesh [:cells cId :vertices]
             (partial replace {vBefore vAfter})))

(defn adjacent-triangles [mesh vId]
  (let [cells (-> mesh :vertices vId :neighbours)
        triangles (map (partial cell-faces mesh) cells)]
    (filter #(contains? % vId) triangles)))

(defn face-vertexIds [mesh {cellId :cellId, fId :faceIdx}]
  (let [vertIds (-> mesh :cells cellId :vertices)
        tris (tetrahedron-triangles vertIds)]
    (tris fId)))

(defn link-faces [mesh fa fb]
  (-> mesh
      (assoc-in [:cells (:cellId fa) :neighbours (:faceIdx fa)] (:cellId fb))
    (assoc-in [:cells (:cellId fb) :neighbours (:faceIdx fb)] (:cellId fa))))

(defn unlink-cell-from-vertex [mesh cId vId]
  (update-in mesh [:vertices vId :neighbours] (partial filter (partial = cId))))

(defn remove-cell [mesh cId]
  (reduce (fn [vId] (unlink-cell-from-vertex mesh cId vId))
          (update :cells (dissoc cId))))

(defn link-opposite-faces [mesh faces]
  (let [grouped (group-by (comp set (partial face-vertexIds mesh)) faces)
        pairs (filter #(= 2 (count %)) grouped)]
    (reduce (fn [m pair] (link-faces m (pair 0) (pair 1)))
            mesh
            faces)))

(defn has-self-intersection [mesh cell-ids]
  (let [without-cells (reduce remove-cell mesh cell-ids)]
    (some #(tetrahedron-overlaps (extract-tetrahedron mesh %1) without-cells)
          cell-ids)))

(defn merge-vertices [mesh v1 v2]
  (-> mesh
      ; Delete v2
      (update :vertices #(dissoc % v2))
      ; Move v1 to midway point.
      (assoc-in [:vertices v1 :pos]
                (ma/scale-add (-> mesh :vertices v1 :pos) 0.5
                              (-> mesh :vertices v2 :pos) 0.5))
      ; Add cells adjacent to v2 as adjacent to v1
      (update-in [:vertices v1 :cells]
                 #(set/union % (-> mesh :vertices v2 :cells)))
      ; Replace v2 with v1 in all cells adjacent to v2
      (as-> m (reduce #(cell-replace-vertex %1 %2 v2 v1)
                      m
                      (-> mesh :vertices v2 :cells)))
      ; Update opposite faces
      (as-> m (link-opposite-faces m (adjacent-triangles m v1)))))

(defn try-merge-vertices [mesh]
  (let [pair (select-nearby-nonlinked-vertex-pair mesh)]
    (if (nil? pair)
      mesh
      (let [[a b] (seq pair)
            after-merge (merge-vertices mesh a b)
            isecs (has-self-intersection after-merge (-> mesh :vertices a :neighbours))]
        (if isecs mesh after-merge)))))

(defn improve-mesh [algo-state]
  (if (= 0 (rand-int 2))
    (let [res (try-add-cell-on-exposed (:mesh algo-state)
                                       (pick-exposed-face (:mesh algo-state)))]
      (if (= res :no-clear-space) algo-state {:mesh (:mesh-after res)}))
    (update algo-state :mesh try-merge-vertices)))

(defn setup []
  (do (q/frame-rate 30)
      {:algo-state init-state,
       :t          0}))

(defn st-update [state]
  (-> state
      (#(update-in % [:algo-state] (if (zero? (mod (q/frame-count) 1))
                                     improve-mesh identity)))
    (#(update % :t (partial + 0.01)))))

(defn draw [state]
  (q/background 200)
  ;(q/text "Hello" 0 0)
  (q/lights)
  (q/fill 150 100 150 120)
  (q/stroke-weight 0.1)
  (q/push-matrix)
  (q/perspective (* 0.5 Math/PI) 1.0 10 5000)
  (let [r (+ 400 (* 10 (state :t)))]
    (q/camera (* r (q/cos (state :t))) -100 (* r (q/sin (state :t)))
              0 0 0
              0 1 0))
  (q/scale 50 -50 50)

  (let [tetramap (-> state :algo-state :mesh)]
    (q/begin-shape :triangles)
    (doseq [[cId cell] (tetramap :cells)]
      (doseq [[a b c] (apply tetrahedron-triangles (extract-tetrahedron tetramap cId))]
        (apply q/vertex a)
        (apply q/vertex b)
        (apply q/vertex c)))
    (q/end-shape))
  ;(q/begin-shape :lines)
  ;(doseq [[cId cell] (tetramap :cells)]
  ;  (doseq [[a b c] (apply tetrahedron-triangles (extract-tetrahedron tetramap cId))]
  ;    (let [orig (triangle-middle a b c)]
  ;      (apply q/vertex orig)
  ;      (apply q/vertex (ma/add orig (triangle-normal a b c))))))
  ;(q/end-shape))

  (q/pop-matrix))

;
;(defn draw [state]
;  (q/color 1 0 0)
;  (q/begin-shape :triangles)
;  (doseq [[cId cell] state]
;    (doseq [[a b c] (map tetrahedron-triangles (extract-tetrahedron (state :tetra-map) cId))]
;      (q/vertex a)
;      (q/vertex b)
;      (q/vertex c)
;  (q/end-shape)))
; )



(q/defsketch example
             :size [width height]
             :setup setup
             :draw draw
             :renderer :p3d
             :update st-update
             :middleware [m/fun-mode])`