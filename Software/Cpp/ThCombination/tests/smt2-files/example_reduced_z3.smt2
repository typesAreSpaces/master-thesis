(set-info :status unknown)
(declare-sort ElementSort 0)
 (declare-sort ArraySort 0)
 (declare-fun e3 () ElementSort)
(declare-fun rd (ArraySort Int) ElementSort)
(declare-fun i3 () Int)
(declare-fun a () ArraySort)
(declare-fun i1 () Int)
(declare-fun a1 () ArraySort)
(declare-fun e1 () ElementSort)
(declare-fun b () ArraySort)
(declare-fun c2 () ArraySort)
(declare-fun c1 () ArraySort)
(declare-fun fresh_index_0 () Int)
(declare-fun fresh_index_1 () Int)
(declare-fun i2 () Int)
(define-fun part_a () Bool (and 
(= (rd a i3) e3)
(=> (distinct i1 i3) (= (rd a i1) (rd a1 i1)))
(=> (distinct i3 i3) (= (rd a i3) (rd a1 i3)))
(= (rd a1 i1) e1)
(=> (distinct i1 i1) (= (rd a1 i1) (rd b i1)))
(=> (distinct i3 i1) (= (rd a1 i3) (rd b i3)))
(=> (> i1 i1) (= (rd c2 i1) (rd b i1)))
(=> (> i3 i1) (= (rd c2 i3) (rd b i3)))
(=> (= (rd c2 i1) (rd b i1)) (= i1 0))
(=> (> i1 i1) (= (rd c1 i1) (rd a i1)))
(=> (> i3 i1) (= (rd c1 i3) (rd a i3)))
(=> (= (rd c1 i1) (rd a i1)) (= i1 0))
(=> (= (rd c2 fresh_index_0) (rd c1 fresh_index_0)) (= fresh_index_0 0))
(=> (> i1 fresh_index_0) (or (= (rd c2 i1) (rd c1 i1)) (= i1 fresh_index_0)))
(=> (> i3 fresh_index_0) (or (= (rd c2 i3) (rd c1 i3)) (= i3 fresh_index_0)))
(=> (> fresh_index_0 fresh_index_0)
    (or (= (rd c2 fresh_index_0) (rd c1 fresh_index_0))
        (= fresh_index_0 fresh_index_0)))
(=> (distinct fresh_index_0 i3) (= (rd a fresh_index_0) (rd a1 fresh_index_0)))
(=> (distinct fresh_index_0 i1) (= (rd a1 fresh_index_0) (rd b fresh_index_0)))
(=> (> fresh_index_0 i1) (or (= (rd c2 fresh_index_0) (rd b fresh_index_0))))
(=> (> fresh_index_0 fresh_index_0)
    (or (= (rd c2 fresh_index_0) (rd c1 fresh_index_0))))
(=> (> fresh_index_0 i1) (or (= (rd c1 fresh_index_0) (rd a fresh_index_0))))
(>= fresh_index_0 fresh_index_1)
(=> (> fresh_index_0 fresh_index_1)
    (distinct (rd c2 fresh_index_0) (rd c1 fresh_index_0)))
(=> (= fresh_index_0 fresh_index_1) (= fresh_index_0 0))
(=> (= (rd c2 fresh_index_1) (rd c1 fresh_index_1)) (= fresh_index_1 0))
(=> (> i1 fresh_index_1)
    (or (= (rd c2 i1) (rd c1 i1)) (= i1 fresh_index_0) (= i1 fresh_index_1)))
(=> (> i3 fresh_index_1)
    (or (= (rd c2 i3) (rd c1 i3)) (= i3 fresh_index_0) (= i3 fresh_index_1)))
(=> (> fresh_index_0 fresh_index_1)
    (or (= (rd c2 fresh_index_0) (rd c1 fresh_index_0))
        (= fresh_index_0 fresh_index_0)
        (= fresh_index_0 fresh_index_1)))
(=> (> fresh_index_1 fresh_index_1)
    (or (= (rd c2 fresh_index_1) (rd c1 fresh_index_1))
        (= fresh_index_1 fresh_index_0)
        (= fresh_index_1 fresh_index_1)))
(=> (distinct fresh_index_1 i3) (= (rd a fresh_index_1) (rd a1 fresh_index_1)))
(=> (distinct fresh_index_1 i1) (= (rd a1 fresh_index_1) (rd b fresh_index_1)))
(=> (> fresh_index_1 i1) (or (= (rd c2 fresh_index_1) (rd b fresh_index_1))))
(=> (> fresh_index_1 fresh_index_0)
    (or (= (rd c2 fresh_index_1) (rd c1 fresh_index_1))))
(=> (> fresh_index_1 fresh_index_1)
    (or (= (rd c2 fresh_index_1) (rd c1 fresh_index_1))
        (= fresh_index_1 fresh_index_0)))
(=> (> fresh_index_1 i1) (or (= (rd c1 fresh_index_1) (rd a fresh_index_1))))
(>= i1 0)
(>= i3 0)
(>= fresh_index_0 0)
(>= fresh_index_1 0)
))
(define-fun part_b () Bool (and 
(< i1 i2)
(< i2 i3)
(distinct (rd c1 i2) (rd c2 i2))
(=> (= (rd c2 fresh_index_0) (rd c1 fresh_index_0)) (= fresh_index_0 0))
(=> (> i1 fresh_index_0) (or (= (rd c2 i1) (rd c1 i1)) (= i1 fresh_index_0)))
(=> (> i2 fresh_index_0) (or (= (rd c2 i2) (rd c1 i2)) (= i2 fresh_index_0)))
(=> (> i3 fresh_index_0) (or (= (rd c2 i3) (rd c1 i3)) (= i3 fresh_index_0)))
(=> (> fresh_index_0 fresh_index_0)
    (or (= (rd c2 fresh_index_0) (rd c1 fresh_index_0))
        (= fresh_index_0 fresh_index_0)))
(=> (> fresh_index_0 fresh_index_0)
    (or (= (rd c2 fresh_index_0) (rd c1 fresh_index_0))))
(>= fresh_index_0 fresh_index_1)
(=> (> fresh_index_0 fresh_index_1)
    (distinct (rd c2 fresh_index_0) (rd c1 fresh_index_0)))
(=> (= fresh_index_0 fresh_index_1) (= fresh_index_0 0))
(=> (= (rd c2 fresh_index_1) (rd c1 fresh_index_1)) (= fresh_index_1 0))
(=> (> i1 fresh_index_1)
    (or (= (rd c2 i1) (rd c1 i1)) (= i1 fresh_index_0) (= i1 fresh_index_1)))
(=> (> i2 fresh_index_1)
    (or (= (rd c2 i2) (rd c1 i2)) (= i2 fresh_index_0) (= i2 fresh_index_1)))
(=> (> i3 fresh_index_1)
    (or (= (rd c2 i3) (rd c1 i3)) (= i3 fresh_index_0) (= i3 fresh_index_1)))
(=> (> fresh_index_0 fresh_index_1)
    (or (= (rd c2 fresh_index_0) (rd c1 fresh_index_0))
        (= fresh_index_0 fresh_index_0)
        (= fresh_index_0 fresh_index_1)))
(=> (> fresh_index_1 fresh_index_1)
    (or (= (rd c2 fresh_index_1) (rd c1 fresh_index_1))
        (= fresh_index_1 fresh_index_0)
        (= fresh_index_1 fresh_index_1)))
(=> (> fresh_index_1 fresh_index_0)
    (or (= (rd c2 fresh_index_1) (rd c1 fresh_index_1))))
(=> (> fresh_index_1 fresh_index_1)
    (or (= (rd c2 fresh_index_1) (rd c1 fresh_index_1))
        (= fresh_index_1 fresh_index_0)))
(>= i1 0)
(>= i2 0)
(>= i3 0)
(>= fresh_index_0 0)
(>= fresh_index_1 0)
))
(compute-interpolant (interp part_a) part_b)
