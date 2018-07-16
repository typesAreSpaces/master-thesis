(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(declare-const e Int)
(compute-interpolant
   (and
   (interp (and (= a b) (= a c)))
   (interp (= c d))
   (and (= b e) (not (= d e)))
   ))