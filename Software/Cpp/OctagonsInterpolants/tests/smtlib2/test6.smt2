(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)

(assert (<= (+ x1 (- x2)) 5))
(assert (<= (- x2  x3) (- 6)))
(assert (<= (+ (* (- 1) x3)  (- x1)) (* (- 1 ) 44)))
