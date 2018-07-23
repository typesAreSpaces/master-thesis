(declare-sort A 0)
(declare-fun x () A)
(declare-fun y () A)
(declare-fun z () A)
(declare-fun f (A) A)
(declare-fun g (A A) A)
(declare-fun h (A A A) A)

(define-fun A () Bool
	    (and (= x y) (= z (h x y z) (= z x)))
)
(define-fun B () Bool
	    (and (= x y) (= z (h x y z) (= z x)))
)
(assert (interp A))
(assert B)