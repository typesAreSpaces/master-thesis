(declare-sort A 0)
(declare-fun x1 () A)
(declare-fun x2 () A)
(declare-fun x3 () A)
(declare-fun x4 () A)
(declare-fun x5 () A)
(declare-fun f (A) A)

(define-fun A1 () Bool
						( and
						(distinct (f x1) (f x2))
						(= (f x1) (f x3))		
						(= (f x1) (f x4))
						)
)
(assert A1)