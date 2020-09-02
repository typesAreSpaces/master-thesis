(set-option :produce-interpolants true)

(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)
(declare-fun x5 () Int)
(declare-fun x6 () Int)

(define-fun part_a () Bool
(and
(>= (+ (- x2) (- x1) 3) 0)
(>= (+ x1 x3 1) 0)
(>= (+ (- x3) (- x4) (- 6)) 0)
(>= (+ x5 x4 1) 0)
) 
)

(define-fun part_b () Bool
(and
(>= (+ x2 x3 3) 0)
(>= (+ x6 (- x5) (- 1)) 0)
(>= (+ x4 (- x6) 4) 0)
)
)

(compute-interpolant part_a part_b)
