(declare-fun x () Int)
(declare-fun a () Int)
(declare-fun f (Int) Int)

(assert (and
(<= 1 x)
(<= x 10)
))

(assert (and
(= (f x) a)
(distinct (f 1) a)
(distinct (f 2) a)
(distinct (f 3) a)
(distinct (f 4) a)
(distinct (f 5) a)
(distinct (f 6) a)
(distinct (f 7) a)
(distinct (f 8) a)
(distinct (f 9) a)
(distinct (f 10) a)
))

(check-sat)
