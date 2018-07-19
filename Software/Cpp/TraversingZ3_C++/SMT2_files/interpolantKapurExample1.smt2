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
	    (>= (- x1 x2) (- 0 4))
	    (>= (- (- 0 x2) x3) 5)
	    (>= (+ x2 x6) 4)
	    (>= (+ x2 x5) (- 0 3))
	    )
)
;; Definition of formula B
(define-fun B () Bool
	    (and
	    (>= (- x3 x1) (- 0 2))
	    (>= (- (- 0 x4) x6) 0)
	    (>= (- x4 x5) 0)
	    )
)
;; Assertion of [interp] A and B
(assert (interp A))
(assert B)