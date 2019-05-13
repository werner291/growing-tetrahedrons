(ns foospace.metaball-thingy
  (:require [quil.core :as q],
            [quil.middleware :as m],
            [clojure.core.matrix :as ma]
            [clojure.tools.trace :as tr]))

(def width 600)
(def height 600)

(defn setup []
  {:points [{:pos [0 0 0], :size 1}]})

(defn dim-span [dim pts]
  (let [ys (map #(nth (% :pos) dim) pts)]
    (- (apply max ys) (apply min ys))))

(defn score [pts]
  (+ (-(* 0.01 (count pts)))
     ;(-(dim-span 1 pts))
     (min 50 (dim-span 0 pts))))

(defn add-random-ball [balls]
  (let [sp (rand-nth balls)
        rand-dir (ma/normalise [(- (rand) 0.5) (- (rand) 0.5) (- (rand) 0.5)])
        orig-pos (sp :pos)
        new-size (* (sp :size) (+ (* 0.1 (+ 0.5 (rand)))))
        move-dist (+ new-size (sp :size))
        new-pos (ma/add-scaled orig-pos rand-dir move-dist)
        new-ball {:pos new-pos, :size 1}]
    (conj balls new-ball)))

(defn remove-random [xs]
  (let [idx (rand-int (count xs))
       [pre post] (split-at idx xs)]
    (concat pre (drop 1 post))))

(defn st-update [state]
  (let [after-modif ((rand-nth [add-random-ball remove-random-ball]) (state :points))
        old-score (score (state :points))
        new-score (score after-modif)
        _ (println ["Score:" old-score new-score (count after-modif)])]
    (if (> new-score old-score)
      (assoc state :points after-modif)
      state)))

(defn draw [state]
  (q/background 255)
  (q/lights)
  (q/fill 150 100 150)
  (q/stroke-weight 0.01)
  (q/push-matrix)
  (q/perspective (* 0.5 Math/PI) 1.0 10 5000)
  (q/sphere-detail 7)
  (let [r 300]
    (q/camera (* r (q/cos (/ (q/frame-count) 100))) -100 (* r (q/sin (/ (q/frame-count) 100)))
              0 0 0
              0 1 0))
  (q/scale 50 -50 50)

  (doseq [ball (state :points)]
    (q/with-translation (ball :pos) (q/sphere (ball :size))))
  (q/pop-matrix))

(q/defsketch example
             :size [width height]
             :setup setup
             :draw draw
             :renderer :p3d
             :update st-update
             :middleware [m/fun-mode])