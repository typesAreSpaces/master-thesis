(declare-sort A 0)
(declare-fun x  () A)
(declare-fun y () A)
(declare-fun f (A) A)

(define-fun input_formula () Bool
	    (and (= x y) (distinct (f x) (f y)))
)
(assert input_formula)
(compute-elim-interpolant input_formula f x f y)
