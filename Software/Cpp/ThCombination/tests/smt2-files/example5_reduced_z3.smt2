; 
(set-info :status unknown)
(declare-sort ElementSort 0)
 (declare-sort ArraySort 0)
 (declare-fun i3 () Int)
(declare-fun i1 () Int)
(declare-fun i4 () Int)
(declare-fun i5 () Int)
(declare-fun e4 () ElementSort)
(declare-fun rd (ArraySort Int) ElementSort)
(declare-fun a () ArraySort)
(declare-fun fresh_array_0 () ArraySort)
(declare-fun e3 () ElementSort)
(declare-fun fresh_array_1 () ArraySort)
(declare-fun e2 () ElementSort)
(declare-fun fresh_array_2 () ArraySort)
(declare-fun e1 () ElementSort)
(declare-fun b () ArraySort)
(declare-fun fresh_index_3 () Int)
(declare-fun i2 () Int)
(define-fun part_a () Bool (and 
(< i1 i3)
(< i3 i4)
(< i4 i5)
(= (rd a i5) e4)
(=> (distinct i1 i5) (= (rd a i1) (rd fresh_array_0 i1)))
(=> (distinct i5 i5) (= (rd a i5) (rd fresh_array_0 i5)))
(=> (distinct i3 i5) (= (rd a i3) (rd fresh_array_0 i3)))
(=> (distinct i4 i5) (= (rd a i4) (rd fresh_array_0 i4)))
(= (rd fresh_array_0 i4) e3)
(=> (distinct i1 i4) (= (rd fresh_array_0 i1) (rd fresh_array_1 i1)))
(=> (distinct i5 i4) (= (rd fresh_array_0 i5) (rd fresh_array_1 i5)))
(=> (distinct i3 i4) (= (rd fresh_array_0 i3) (rd fresh_array_1 i3)))
(=> (distinct i4 i4) (= (rd fresh_array_0 i4) (rd fresh_array_1 i4)))
(= (rd fresh_array_1 i3) e2)
(=> (distinct i1 i3) (= (rd fresh_array_1 i1) (rd fresh_array_2 i1)))
(=> (distinct i5 i3) (= (rd fresh_array_1 i5) (rd fresh_array_2 i5)))
(=> (distinct i3 i3) (= (rd fresh_array_1 i3) (rd fresh_array_2 i3)))
(=> (distinct i4 i3) (= (rd fresh_array_1 i4) (rd fresh_array_2 i4)))
(= (rd fresh_array_2 i1) e1)
(=> (distinct i1 i1) (= (rd fresh_array_2 i1) (rd b i1)))
(=> (distinct i5 i1) (= (rd fresh_array_2 i5) (rd b i5)))
(=> (distinct i3 i1) (= (rd fresh_array_2 i3) (rd b i3)))
(=> (distinct i4 i1) (= (rd fresh_array_2 i4) (rd b i4)))
(=> (> i1 i1) (= (rd b i1) (rd a i1)))
(=> (> i5 i1) (= (rd b i5) (rd a i5)))
(=> (> i3 i1) (= (rd b i3) (rd a i3)))
(=> (> i4 i1) (= (rd b i4) (rd a i4)))
(=> (= (rd b i1) (rd a i1)) (= i1 0))
(= fresh_index_3 i1)
(=> (> i1 fresh_index_3) (or (= (rd b i1) (rd a i1)) (= i1 i1)))
(=> (> i5 fresh_index_3) (or (= (rd b i5) (rd a i5)) (= i5 i1)))
(=> (> i3 fresh_index_3) (or (= (rd b i3) (rd a i3)) (= i3 i1)))
(=> (> i4 fresh_index_3) (or (= (rd b i4) (rd a i4)) (= i4 i1)))
(=> (> fresh_index_3 fresh_index_3)
    (or (= (rd b fresh_index_3) (rd a fresh_index_3)) (= fresh_index_3 i1)))
(=> (distinct fresh_index_3 i5)
    (= (rd a fresh_index_3) (rd fresh_array_0 fresh_index_3)))
(=> (distinct fresh_index_3 i4)
    (= (rd fresh_array_0 fresh_index_3) (rd fresh_array_1 fresh_index_3)))
(=> (distinct fresh_index_3 i3)
    (= (rd fresh_array_1 fresh_index_3) (rd fresh_array_2 fresh_index_3)))
(=> (distinct fresh_index_3 i1)
    (= (rd fresh_array_2 fresh_index_3) (rd b fresh_index_3)))
(=> (> fresh_index_3 i1) (or (= (rd b fresh_index_3) (rd a fresh_index_3))))
(>= i1 0)
(>= i5 0)
(>= i3 0)
(>= i4 0)
(>= fresh_index_3 0)
))
(define-fun part_b () Bool (and 
(< i1 i2)
(< i2 i3)
(distinct (rd a i2) (rd b i2))
(=> (= (rd b fresh_index_3) (rd a fresh_index_3)) (= fresh_index_3 0))
(=> (> i1 fresh_index_3) (or (= (rd b i1) (rd a i1)) (= i1 fresh_index_3)))
(=> (> i2 fresh_index_3) (or (= (rd b i2) (rd a i2)) (= i2 fresh_index_3)))
(=> (> i3 fresh_index_3) (or (= (rd b i3) (rd a i3)) (= i3 fresh_index_3)))
(=> (> fresh_index_3 fresh_index_3)
    (or (= (rd b fresh_index_3) (rd a fresh_index_3))
        (= fresh_index_3 fresh_index_3)))
(=> (> fresh_index_3 fresh_index_3)
    (or (= (rd b fresh_index_3) (rd a fresh_index_3))))
(>= i1 0)
(>= i2 0)
(>= i3 0)
(>= fresh_index_3 0)
))
(compute-interpolant (interp part_a) part_b)
