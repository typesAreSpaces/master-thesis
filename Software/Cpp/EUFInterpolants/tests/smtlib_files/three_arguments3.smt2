(declare-sort A 0)
(declare-fun x  () A)
(declare-fun y () A)
(declare-fun z () A)
(declare-fun f (A A A) A)
(declare-fun g (A A) A)	

(define-fun input_formula () Bool
	    (and (distinct (f x x x) (f y x y))
	     (distinct (f x y x) (f z y x)) 
	      (distinct (f x y x) (g y x)))
)
(assert input_formula)