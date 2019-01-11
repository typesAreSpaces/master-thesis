(declare-sort A 0)
(declare-fun x1 () A)
(declare-fun f (A A) A)

(define-fun A1 () Bool
						( and
						(distinct (f (f x1 x1) x1) (f x1 (f x1 x1)))
						(distinct (f x1 x1) (f x1 x1))		
						)
)
(assert A1)