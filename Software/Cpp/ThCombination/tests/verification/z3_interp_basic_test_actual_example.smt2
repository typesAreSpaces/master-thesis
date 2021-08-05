(set-option :produce-interpolants true)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun y1 () Int)
(declare-fun y2 () Int)
(declare-fun y3 () Int)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)

(assert (!
(and 
(= (f x1) 0)
(= x1 a)
(<= y1 a)
) :named part_a))

(assert (!
(and 
(<= x1 b)
(= y1 b)
(distinct (f y1) 0)
) :named part_b))

(compute-interpolant part_a part_b)
