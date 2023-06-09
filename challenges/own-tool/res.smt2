(declare-rel inv0 (Int Int))
(declare-rel inv (Int Int Int))

(declare-var x0 Int)
(declare-var x1 Int)
(declare-var y0 Int)
(declare-var y1 Int)


(declare-var N Int)
(declare-var M Int)

(declare-rel fail ())

;; move numbers into separate initial state
(rule (inv0 0 5000))

;; initialize x, y, and the bound
(rule (=> (inv0 x0 N) (inv x0 N N)))

;; transition relation
(rule (=> (and (inv x0 y0 N)
              (= y1 (ite (>= x0 N) (+ y0 1) y0))
              (= x1 (+ x0 1)))
         (inv x1 y1 N)))

(rule (=> (and (inv x0 y0 N) (>= M N) (>= x0 M) (not (= x0 y0))) fail))

(query fail)
