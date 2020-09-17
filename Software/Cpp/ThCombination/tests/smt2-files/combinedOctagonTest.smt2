(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun y1 () Int)
(declare-fun y3 () Int)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)

(assert 
(and
(= (+ (f x1) x2) 0)
(= y3 (f y1))
(<= y1 x1)
)
)

(assert
(and 
(= x2 (g b))
(= 0 (g b))
(<= x1 y1)
(<= 1 y3)
)
)

(check-sat)
