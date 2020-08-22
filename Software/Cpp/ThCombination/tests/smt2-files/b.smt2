; 
(set-option :produce-unsat-cores true)
(set-info :status unknown)
(declare-sort ElementSort 0)
 (declare-sort ArraySort 0)
 (declare-fun e3 () ElementSort)
(declare-fun rd (ArraySort Int) ElementSort)
(declare-fun i3 () Int)
(declare-fun a () ArraySort)
(declare-fun i1 () Int)
(declare-fun fresh_array_0 () ArraySort)
(declare-fun e1 () ElementSort)
(declare-fun b () ArraySort)
(declare-fun c2 () ArraySort)
(declare-fun c1 () ArraySort)
(declare-fun fresh_index_1 () Int)
(declare-fun fresh_index_2 () Int)
(declare-fun i2 () Int)

(assert (! 
(=> (= (rd c2 fresh_index_1) (rd c1 fresh_index_1)) (= fresh_index_1 0))
:named a14))
(assert (! 
(=> (distinct fresh_index_1 i3)
    (= (rd a fresh_index_1) (rd fresh_array_0 fresh_index_1)))
:named a17))
(assert (! 
(=> (distinct fresh_index_1 i1)
    (= (rd fresh_array_0 fresh_index_1) (rd b fresh_index_1)))
:named a18))
(assert (! 
(=> (> fresh_index_1 i1) (or (= (rd c2 fresh_index_1) (rd b fresh_index_1))))
:named a19))
(assert (! 
(=> (> fresh_index_1 i1) (or (= (rd c1 fresh_index_1) (rd a fresh_index_1))))
:named a21))
(assert (! 
(>= fresh_index_1 fresh_index_2)
:named a22))
(assert (! 
(=> (> fresh_index_1 fresh_index_2)
    (distinct (rd c2 fresh_index_1) (rd c1 fresh_index_1)))
:named a23))
(assert (! 
(=> (= fresh_index_1 fresh_index_2) (= fresh_index_1 0))
:named a24))
(assert (! 
(=> (= (rd c2 fresh_index_2) (rd c1 fresh_index_2)) (= fresh_index_2 0))
:named a25))
(assert (! 
(=> (distinct fresh_index_2 i3)
    (= (rd a fresh_index_2) (rd fresh_array_0 fresh_index_2)))
:named a30))
(assert (! 
(=> (distinct fresh_index_2 i1)
    (= (rd fresh_array_0 fresh_index_2) (rd b fresh_index_2)))
:named a31))
(assert (! 
(=> (> fresh_index_2 i1) (or (= (rd c2 fresh_index_2) (rd b fresh_index_2))))
:named a32))
(assert (! 
(=> (> fresh_index_2 i1) (or (= (rd c1 fresh_index_2) (rd a fresh_index_2))))
:named a35))
(assert (! 
(>= i1 0)
:named a36))

;(apply simplify)
;(apply (then simplify (or-else split-clause skip)))
;(apply (then simplify (repeat (or-else split-clause skip) 18)))

;(assert (!
;(< i1 i2)
;:named b1))
;(assert (!
;(< i2 i3)
;:named b2))
;(assert (!
;(distinct (rd c1 i2) (rd c2 i2))
;:named b3))
;(assert (!
;(=> (> i2 fresh_index_1) (or (= (rd c2 i2) (rd c1 i2)) (= i2 fresh_index_1)))
;:named b6))
;(assert (!
;(=> (> i2 fresh_index_2)
    ;(or (= (rd c2 i2) (rd c1 i2)) (= i2 fresh_index_1) (= i2 fresh_index_2)))
;:named b15))

;(check-sat)
;(get-unsat-core)
