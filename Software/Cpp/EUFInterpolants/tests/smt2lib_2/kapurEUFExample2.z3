(declare-sort A 0)
(declare-fun x1 () A)
(declare-fun x2 () A)
(declare-fun f (A) A)

(define-fun A1 () Bool
						(distinct (f x1) (f x2))
)
(assert A1)
(check-sat)
(get-model)