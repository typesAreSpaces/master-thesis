(declare-sort A 0)
(declare-fun x1 () A)
(declare-fun x2 () A)
(declare-fun x3 () A)
(declare-fun x4 () A)
(declare-fun x5 () A)
(declare-fun f (A) A)

(define-fun A1 () Bool
						( and
						(distinct (f (f x1)) (f (f x2)))
						(distinct (f x1) (f x2))		
						)
)
(assert A1)