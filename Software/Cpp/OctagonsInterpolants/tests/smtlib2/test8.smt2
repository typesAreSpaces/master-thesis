(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)

(assert (<= (+ x1 x2) 5))
(assert (<= (+ x1 (- x2)) 5))
(assert (<= (+ (- x1) x2) 5))
(assert (<= (+ (- x1) (- x2)) 5))
(assert (<= (+ x1 x2) (- 5)))
(assert (<= (+ x1 (- x2)) (- 5)))
(assert (<= (+ (- x1) x2) (- 5)))
(assert (<= (+ (- x1) (- x2)) (- 5)))

(assert (<= x1 33))
(assert (<= x1 (- 45)))
(assert (<= (- x1) 354))
(assert (<= (- x1) (- 34)))
