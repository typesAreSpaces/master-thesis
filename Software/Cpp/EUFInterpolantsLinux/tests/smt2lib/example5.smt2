(declare-sort A 0)
(declare-fun x () A)
(declare-fun f (A) A)
(define-fun A () Bool
	    (and (= x (f x)))
)
(define-fun B () Bool
	    (and (= x (f x)))
)
(assert (interp A))
(assert B)