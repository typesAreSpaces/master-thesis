;; Proving or Disproving A

;; Declarations of involved elements
(declare-sort A 0)
(declare-fun s1 () A)
(declare-fun s2 () A)
(declare-fun y1 () A)
(declare-fun z1 () A)
(declare-fun z2 () A)
(define-fun x () Bool (= z1 z2))
(define-fun y () Bool (and (= z1 y1) (= z2 y1)))
(define-fun conjecture1 () Bool (=> x y))

;; Assertion of A
(assert (not conjecture1))
(check-sat)
(get-model)
(exit)