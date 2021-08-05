(set-option :produce-interpolants true)

(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)
(declare-fun x5 () Int)
(declare-fun x6 () Int)

(define-fun part_a () Bool 
(and
(>= (- x1 x2) (- 4))
(>= (- (- x2) x3) 5)
(>= (+ x2 x6) 4)
(>= (+ x2 x5) (- 3))
)
)

(define-fun part_b () Bool
(and
(>= (+ (- x1) x3) (- 2))
(>= (- (- x4) x6) 0)
(>= (+ (- x5) x4) 0)
)
)

(compute-interpolant part_a part_b)
