(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)
(declare-fun x5 () Int)
(declare-fun x6 () Int)
(declare-fun x7 () Int)
(declare-fun x8 () Int)

(define-fun a_part () Bool
(and 
(<= (+ x1 x2) 1)
(<= (- x3 x2) 1)
(<= (- x4 x3) 1)
(<= (- x5 x4) 1)
(<= (- x6 x5) 1)
(<= (- x7 x6) 1)
(<= (- x8 x7) 1)
(<= (- x1 x8) 1)
)
)

(define-fun b_part () Bool
(> x1 4)
)

(define-fun my_interpolant () Bool 
(<= x1 4)
)

(push)
(assert (and a_part b_part))
(check-sat)
(pop)

(push)
(assert (not (=> a_part my_interpolant)))
(check-sat)
(pop)

(push)
(assert (and b_part my_interpolant))
(check-sat)
(pop)
