;; Proving or Disproving A

;; Declarations of involved elements
(declare-sort A 0)
(declare-fun x () A)
(declare-fun y () A)
(declare-fun g (A) A)
(define-fun conjecture2 () Bool (=> (= x y) (= (g (g x)) (g y))))

;; Assertion of A
(assert conjecture2)