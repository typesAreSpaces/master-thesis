(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)

(assert (<= (- x1  (- x2)) 0))
(assert (<= (- x2  (- x3)) 0))
(assert (<= (- x3  (- x1)) 0))
