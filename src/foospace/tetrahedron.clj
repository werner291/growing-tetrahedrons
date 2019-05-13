;; Tetrahedron intersection based on this paper & algorithm:
;; http://vcg.isti.cnr.it/Publications/2003/GPR03/fast_tetrahedron_tetrahedron_overlap_algorithm.pdf
;;
;; Unlike original algorithm this implementation produces correct
;; results regardless of the orientation/ordering of points defining
;; the two tetrahedra. This is achieved via the orient-tetra function,
;; which ensures the correct ordering of vertices for this algorithm
;; to function properly.
;;
;; Implementation extracted from upcoming geometry library
;; All required vector operations are supplied here, so no further
;; dependencies...

;; Stolen from https://gist.github.com/postspectacular/9021724

(ns foospace.tetrahedron)

(defn sub
  "3D vector subtraction."
  [[ax ay az] [bx by bz]] [(- ax bx) (- ay by) (- az bz)])

(defn dot
  "Returns dot product of a and b."
  [[ax ay az] [bx by bz]] (+ (+ (* ax bx) (* ay by)) (* az bz)))

(defn cross
  "Returns cross product of a and b."
  [[ax ay az] [bx by bz]]
  [(- (* ay bz) (* az by))
   (- (* az bx) (* ax bz))
   (- (* ax by) (* bx ay))])

(defn normalize
  "Returns normalized vector."
  [[x y z :as v]]
  (let [m (+ (+ (* x x) (* y y)) (* z z))]
    (if (pos? m) [(/ x m) (/ y m) (/ z m)] v)))

(defn normal3
  "Returns normal vector for plane defined by a,b,c."
  [a b c] (normalize (cross (sub b a) (sub c a))))

(defn subdot
  "Computes sum((a-b)*c), where a, b, c are 3D vectors."
  [a b c] (reduce + (map * (sub a b) c)))

(defn orient-tetra
  "Takes a seq of 4 3D points, returns them as vector in the order so
  that the last point is on the opposite side of the plane defined by
  the first three points."
  [[a b c d :as t]]
  (let [dp (-> d (sub a) (normalize) (dot (normal3 a b c)))]
    (if (neg? dp) (vec t) [a c b d])))

(defn compute-mask
  "Computes bit mask for given seq of 4 affine coords."
  [aff]
  (bit-or
    (bit-or
      (bit-or
        (if (pos? (aff 0)) 1 0) (if (pos? (aff 1)) 2 0))
      (if (pos? (aff 2)) 4 0))
    (if (pos? (aff 3)) 8 0)))

(defn- face-a
  "Takes a transformation fn and the 4 delta vectors between tetra1/tetra2.
  Returns 2-elem vec of [bitmask affine-coords]."
  [f deltas]
  (let [affine (mapv f deltas)] [(compute-mask affine) affine]))

(defn face-b1?
  "Takes the 4 delta vectors between tetra2/tetra1 and a normal.
  Returns true if all dot products are positive."
  [deltas n] (every? #(pos? (dot % n)) deltas))

(defn face-b2?
  "Like face-b1?, but optimized for last face of tetrahedron."
  [verts refv n] (every? #(pos? (subdot % refv n)) verts))

(defn edge-a
  "Takes 2 bitmasks and edge flags, returns true if there's a
  separating plane between the faces shared by that edge."
  [ma mb ea eb]
  (let [xa (bit-and ma (bit-xor ma mb))
        xb (bit-and mb (bit-xor xa mb))
        edge (fn [a b i j]
               (let [cp (- (* (ea i) (eb j)) (* (ea j) (eb i)))]
                 (or (and (pos? cp) (pos? (bit-or xa a)) (pos? (bit-or xb b)))
                     (and (neg? cp) (pos? (bit-or xa b)) (pos? (bit-or xb a))))))]
    (not
      (or
        (not= 15 (bit-or ma mb))
        (edge 1 2 1 0)
        (edge 1 4 2 0)
        (edge 1 8 3 0)
        (edge 2 4 2 1)
        (edge 2 8 3 1)
        (edge 4 8 3 2)))))

(defn get-edge
  "Lazy edge evaluation. Takes a vector of edges, vector of edge
  points and an edge id. Looks up edge for given id and if not yet
  present constructs it. Returns 2-elem vector of [edges edge]."
  [edges epoints id]
  (let [e (edges id)]
    (if e
      [edges e]
      (let [ep (epoints id), e (sub (ep 0) (ep 1))]
        [(assoc edges id e) e]))))

(defn check-faces-a
  "Takes the 4 delta vectors between the two tetras, edge definitions
  of the 1st tetra, vertices of the 2nd, a reference point of the 1st
  and a seq of specs, each encoding a specific check (either calls to
  face-a* or edge-a). Returns vector of bitmasks or nil if fail early."
  [deltas epoints verts p specs]
  (loop [masks [], affine [], edges [nil nil nil nil nil], s specs]
    (if s
      (let [[f a b] (first s)]
        (if (or (= :f f) (= :f* f))
          (let [[edges ea] (get-edge edges epoints a)
                [edges eb] (get-edge edges epoints b)
                n (cross ea eb)
                [m a] (if (= :f f)
                        (face-a #(dot % n) deltas)
                        (face-a #(subdot % p n) verts))]
            (if (< m 15)
              (recur (conj masks m) (conj affine a) edges (next s))))
          (if-not (edge-a (masks a) (masks b) (affine a) (affine b))
            (recur masks affine edges (next s)))))
      masks)))

(defn check-faces-b
  "Much like check-faces-a, but for 2nd tetra and specs encoding calls to face-b1/2?.
  Returns true if tetras do intersect."
  [deltas epoints verts p specs]
  (loop [edges [nil nil nil nil nil], s specs]
    (if s
      (let [[f a b] (first s)
            [edges ea] (get-edge edges epoints a)
            [edges eb] (get-edge edges epoints b)]
        (if-not (if (= :f f)
                  (face-b1? deltas (cross ea eb))
                  (face-b2? verts p (cross ea eb)))
          (recur edges (next s))))
      true)))

(defn intersect-tetrahedra?
  "Takes 2 seqs of 4 3D points, each defining a tetrahedron. Returns
  true if they intersect. Orientation of points is irrelevant (unlike
  in the original algorithm this implementation is based on)."
  [p q]
  (let [[pa pb pc pd :as p] (orient-tetra p)
        [qa qb qc qd :as q] (orient-tetra q)
        masks (check-faces-a
                (map #(sub % pa) q)
                [[pb pa] [pc pa] [pd pa] [pc pb] [pd pb]]
                q pb [[:f 0 1] [:f 2 0] [:e 0 1] [:f 1 2]
                      [:e 0 2] [:e 1 2] [:f* 4 3] [:e 0 3]
                      [:e 1 3] [:e 2 3]])]
    (if masks
      (or (not= 15 (apply bit-or masks))
          (check-faces-b
            (map #(sub % qa) p)
            [[qb qa] [qc qa] [qd qa] [qc qb] [qd qb]]
            p qb [[:f 0 1] [:f 2 0] [:f 1 2] [:f* 4 3]])))))

;; worst case scenario testing constellation requiring all checks
(def p [[0.0 0.0 0.0] [50.0 50.0 0.0] [100.0 0.0 0.0] [50.0 25.0 100.0]])
(def q [[0.0 0.0 0.0] [-50.0 50.0 0.0] [-200.0 0.0 20.0] [150.0 25.0 100.0]])

;; should = true
(prn :first (intersect-tetrahedra? p q))

(def q [[100.001 0.0 0.0] [150.0 50.0 0.0] [200.0 0.0 0.0] [150.0 25.0 10.0]])
;; should = nil (false)
(prn :second (intersect-tetrahedra? p q))