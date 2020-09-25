(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

(assert (and 
(<= (+ x1 x2) 1)
(<= (- x3 x2) 1)
(<= (- x4 x3) 1)
(<= (- x1 x4) 1)
))

(assert (and 
(> x1 2)
))

(check-sat)
