;; Proving or Disproving A

;; Declarations of involved elements
(declare-sort A 0)
(declare-fun x () A)
(declare-fun y () A)
(declare-fun g (A) A)
(define-fun conjecture1 () Bool (=> (= x y) (= (g x) (g y))))
(define-fun conjecture2 () Bool (=> (= (g x) (g y)) (= x y)))

;; Assertion of A
(assert (and conjecture1 conjecture2))