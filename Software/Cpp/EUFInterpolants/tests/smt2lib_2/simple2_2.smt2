(declare-sort A 0)
(declare-fun x  () A)
(declare-fun y () A)
(declare-fun f (A) A)

(assert (= x y))
(assert (distinct (f x) (f y)))
(assert (= y (f x)))
