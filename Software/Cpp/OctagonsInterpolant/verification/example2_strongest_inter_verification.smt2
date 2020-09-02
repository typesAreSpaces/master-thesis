(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)
(declare-fun x5 () Int)
(declare-fun x6 () Int)

(define-fun implementation_interpolant () Bool 
(and
(<= (+ (- x3) x2) 4)
(<= (+ x4 x3) (- 6))
(<= (- (- x5) x4) 1))
)

(define-fun z3_interpolant () Bool
(and 
(<= (- 4) (+ x3 (* (- 1) x2))) 
(<= (+ x3 x4) (- 6)) 
(>= (+ x4 x5) (- 1)))
)

(define-fun mathsat_interpolant () Bool
(<= (+ x2 (+ x3 (+ x4 (* (- 1) x5)))) (- 7))
)

(push)
(assert (not (iff z3_interpolant implementation_interpolant)))
(check-sat) ;; This check returns unsat, i.e. z3_interpolant is equivalent to implementation_interpolant
(pop)

(push)
(assert (not (implies  mathsat_interpolant implementation_interpolant)))
(check-sat) ;; This check returns sat, i.e. mathsat_interpolant does not imply implementation_interpolant
(pop)

(push)
(assert (not (implies implementation_interpolant mathsat_interpolant)))
(check-sat) ;; This check returns unsat, i.e. implementation_interpolant implies mathsat_interpolant
(pop)
