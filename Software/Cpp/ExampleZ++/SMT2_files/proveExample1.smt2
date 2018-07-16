;; Proving or Disproving A

;; Declarations of involved elements
(declare-sort A 0)
(declare-fun x () A)
(declare-fun y () A)
(declare-fun g (A) A)
(define-fun conjecture1 () Bool (=> (= x y) (= (g x) (g y))))

;; Assertion of A
(assert conjecture1)