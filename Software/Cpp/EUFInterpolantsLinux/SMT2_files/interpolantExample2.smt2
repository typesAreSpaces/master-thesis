;; Interpolant of A, B where eval(A && B) = unsat

;; Declarations of involved elements
(declare-sort A 0)
(declare-fun a () A)
(declare-fun b () A)
(declare-fun c () A)
(declare-fun d () A)
(declare-fun f (A A) A)
(declare-fun g (A A A) A)
(declare-fun h (A A A A A) A)

;; Definition of formula A
(define-fun A () Bool
	    (and (= a b) (= a c) (= (f a b) b) (= (f b b) (g c b a)) (= a (h a b c d a)))
)
;; Definition of formula B
(define-fun B () Bool
	    (and (= b d) (not (= c d)))
)
;; Assertion of [interp] A and B
(assert (interp A))
(assert B)