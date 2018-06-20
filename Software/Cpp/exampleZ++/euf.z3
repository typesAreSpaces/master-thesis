(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(compute-interpolant
   (and (= (f a) c) (= (f b) d))
   (and (= a b) (not (= (g c) (g d)))))