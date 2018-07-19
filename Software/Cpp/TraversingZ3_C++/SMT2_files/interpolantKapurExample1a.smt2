;; Interpolant of A, B where eval(A && B) = unsat

;; Declarations of involved elements
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)
(declare-fun x5 () Int)
(declare-fun x6 () Int)

;; Definition of formula A
(define-fun A () Bool
	    (and
	    (>= (- (- 0 x2) x1) 0)
	    (>= (+ x1 x3) (- 0 1))
	    (>= (- (- 0 x3) x4) 6)
	    (>= (+ x5 x4) (- 0 1))
	    )
)
;; Definition of formula B
(define-fun B () Bool
	    (and
	    (>= (+ x2 x3) (- 0 3))
	    (>= (- x6 x5) 1)
	    (>= (- x4 x6) (- 0 4))
	    )
)
;; Assertion of [interp] A and B
(assert (interp A))
(assert B)