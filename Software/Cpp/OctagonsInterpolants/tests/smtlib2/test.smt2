(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)

(assert (<= (- (* 6 x1) (* (- 5) x2)) 0) )
(assert (<= (- (* 6 x2) (* (- 5) x3)) 0) )
(assert (<= (- (* 6 x3) (* (- 5) x1)) 0) )
(assert (> x1 0))
