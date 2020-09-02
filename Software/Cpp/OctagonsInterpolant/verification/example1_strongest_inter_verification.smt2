(declare-fun x1 () Int)
(declare-fun x3 () Int)
(declare-fun x5 () Int)
(declare-fun x6 () Int)

(define-fun implementation_interpolant () Bool 
(and
(<= (- (- x6) x1) 0)
(<= (+ (- x6) x3) (- 9))
(<= (- (- x5) x1) 7)
(<= (+ (- x5) x3) (- 2))
)
)

(define-fun z3_interpolant () Bool
(and 
(<= 9 (+ (* (- 1) x3) (* 2 x6) x1))
(<= (- 5) (+ (* (- 1) x3) (* 2 x5) x1))
)
)

(push)
(assert (not (implies  z3_interpolant implementation_interpolant)))
(check-sat) ;; This check returns sat, i.e. z3_interpolant does not imply implementation_interpolant
(pop)
(push)
(assert (not (implies implementation_interpolant z3_interpolant)))
(check-sat) ;; This check returns unsat, i.e. implementation_interpolant implies z3_interpolant
(pop)
