(declare-sort A 0)
(declare-fun x () A)
(declare-fun g (A A) A)

(define-fun A () Bool
	    (and (= x (g x x)))
)
(define-fun B () Bool
            (and (= x (g x x)))
)
(assert (interp A))
(assert B)
