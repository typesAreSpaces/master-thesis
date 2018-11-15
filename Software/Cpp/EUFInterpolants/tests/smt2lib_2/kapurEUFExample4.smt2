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
(declare-fun g (A) A)

(define-fun A () Bool
	    (and (= (f z1 v) (g s1)) (= (f z2 v) (g s2)) (= (f (f (g y1) v) (f (g y2) v)) t))
)
(assert A)