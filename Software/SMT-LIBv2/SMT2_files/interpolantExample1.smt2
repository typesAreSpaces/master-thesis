;; Interpolant of A, B where eval(A && B) = unsat

;; Declarations of involved elements
(declare-sort A 0)
(declare-fun a () A)
(declare-fun b () A)
(declare-fun c () A)
(declare-fun d () A)
(declare-fun u () A)
(declare-fun v () A)
(declare-fun w () A)
(declare-fun f (A) A)
(declare-fun g (A) A)

;; Definition of formula A
;;(define-fun A () Bool (and (= (f a) u) (= (f b) c) (= (f c) u) (= (f d) d)))
(define-fun A () Bool (= a b))
;; Definition of formula B
;;(define-fun B () Bool (and (= (g a) v) (= (g d) w) (= (g v) b) (= (g w) c) (= a d) (distinct c d)))
(define-fun B () Bool (= a b))
;; Assertion of [interp] A and B
(assert A)
(assert B)