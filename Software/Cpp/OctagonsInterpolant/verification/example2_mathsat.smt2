(set-option :produce-interpolants true)

(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)
(declare-fun x5 () Int)
(declare-fun x6 () Int)

(assert (!
(and
(>= (+ (- x2) (- x1) 3) 0)
(>= (+ x1 x3 1) 0)
(>= (+ (- x3) (- x4) (- 6)) 0)
(>= (+ x5 x4 1) 0)
) :interpolation-group part_a)
)

(assert (!
(and
(>= (+ x2 x3 3) 0)
(>= (+ x6 (- x5) (- 1)) 0)
(>= (+ x4 (- x6) 4) 0)
) :interpolation-group part_b)
)

(check-sat)
(get-interpolant (part_a))
(exit)
