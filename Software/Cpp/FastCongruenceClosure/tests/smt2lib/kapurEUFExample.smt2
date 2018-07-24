(declare-sort A 0)
(declare-fun z1 () A)
(declare-fun z2 () A)
(declare-fun y1 () A)
(declare-fun y2 () A)
(declare-fun s1 () A)
(declare-fun s2 () A)
(declare-fun v () A)
(declare-fun t () A)
(declare-fun f (A A) A)

(define-fun A () Bool
	    (and (= (f z1 v) s1) (= (f z2 v) s2) (= (f (f y1 v) (f y2 v)) t))
)
(define-fun B () Bool
	    (and (= (f z1 z1) s1) (= (f z2 z1) s2) (= (f (f y1 z1) (f y2 z1)) t))
)	 
(assert (interp A))
(assert B)