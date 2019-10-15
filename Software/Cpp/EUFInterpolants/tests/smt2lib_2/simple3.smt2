(declare-sort A 0)
(declare-fun x  () A)
(declare-fun y () A)
(declare-fun z () A)
(declare-fun f (A) A)

(define-fun input_formula () Bool
	    (and (= x y) (distinct (f x) (f y)) (distinct (f x) (f z)))
)
(assert input_formula)