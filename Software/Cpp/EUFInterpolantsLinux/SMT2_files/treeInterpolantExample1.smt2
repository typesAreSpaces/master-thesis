;; Sequence of Interpolants for A1, ..., An where eval(A1 && ... && An) = unsat

;; Declarations of involved elements
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun d () Int)
(declare-fun e () Int)

;; Definition of formula A1
(define-fun A1 () Bool
	    (and (= a b) (= a c))
)
;; Definition of formula A2
(define-fun A2 () Bool
	    (= c d)
)
;; Definition of formula A3
(define-fun A3 () Bool
	    (and (= b e) (not (= d e)))
)

;; Assertion of [interp]([interp] A1 and A2) and A3
(assert (and (interp A1) (interp A2) A3))