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
(= (rd a i3) e3) 
:named a40))
(assert (! 
(=> (distinct i1 i3) (= (rd a i1) (rd fresh_array_0 i1)))
:named a2))
(assert (! 
(=> (distinct i3 i3) (= (rd a i3) (rd fresh_array_0 i3)))
:named a3))
(assert (! 
(= (rd fresh_array_0 i1) e1)
:named a4))
(assert (! 
(=> (distinct i1 i1) (= (rd fresh_array_0 i1) (rd b i1)))
:named a5))
(assert (! 
(=> (distinct i3 i1) (= (rd fresh_array_0 i3) (rd b i3)))
:named a6))
(assert (! 
(=> (> i1 i1) (= (rd c2 i1) (rd b i1)))
:named a7))
(assert (! 
(=> (> i3 i1) (= (rd c2 i3) (rd b i3)))
:named a8))
(assert (! 
(=> (= (rd c2 i1) (rd b i1)) (= i1 0))
:named a9))
(assert (! 
(=> (> fresh_index_1 fresh_index_1)
    (or (= (rd c2 fresh_index_1) (rd c1 fresh_index_1))
        (= fresh_index_1 fresh_index_1)))
:named a10))
(assert (! 
(=> (> i1 i1) (= (rd c1 i1) (rd a i1)))
:named a11))
(assert (! 
(=> (> i3 i1) (= (rd c1 i3) (rd a i3)))
:named a12))
(assert (! 
(=> (= (rd c1 i1) (rd a i1)) (= i1 0))
:named a13))
(assert (! 
(=> (= (rd c2 fresh_index_1) (rd c1 fresh_index_1)) (= fresh_index_1 0))
:named a14))
(assert (! 
(=> (> i1 fresh_index_1) (or (= (rd c2 i1) (rd c1 i1)) (= i1 fresh_index_1)))
:named a15))
(assert (! 
(=> (> i3 fresh_index_1) (or (= (rd c2 i3) (rd c1 i3)) (= i3 fresh_index_1)))
:named a16))
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
(=> (> fresh_index_1 fresh_index_1)
    (or (= (rd c2 fresh_index_1) (rd c1 fresh_index_1))))
:named a20))
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
(=> (> i1 fresh_index_2)
    (or (= (rd c2 i1) (rd c1 i1)) (= i1 fresh_index_1) (= i1 fresh_index_2)))
:named a26))
(assert (! 
(=> (> i3 fresh_index_2)
    (or (= (rd c2 i3) (rd c1 i3)) (= i3 fresh_index_1) (= i3 fresh_index_2)))
:named a27))
(assert (! 
(=> (> fresh_index_1 fresh_index_2)
    (or (= (rd c2 fresh_index_1) (rd c1 fresh_index_1))
        (= fresh_index_1 fresh_index_1)
        (= fresh_index_1 fresh_index_2)))
:named a28))
(assert (! 
(=> (> fresh_index_2 fresh_index_2)
    (or (= (rd c2 fresh_index_2) (rd c1 fresh_index_2))
        (= fresh_index_2 fresh_index_1)
        (= fresh_index_2 fresh_index_2)))
:named a29))
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
(=> (> fresh_index_2 fresh_index_1)
    (or (= (rd c2 fresh_index_2) (rd c1 fresh_index_2))))
:named a33))
(assert (! 
(=> (> fresh_index_2 fresh_index_2)
    (or (= (rd c2 fresh_index_2) (rd c1 fresh_index_2))
        (= fresh_index_2 fresh_index_1)))
:named a34))
(assert (! 
(=> (> fresh_index_2 i1) (or (= (rd c1 fresh_index_2) (rd a fresh_index_2))))
:named a35))
(assert (! 
(>= i1 0)
:named a36))
(assert (! 
(>= i3 0)
:named a37))
(assert (! 
(>= fresh_index_1 0)
:named a38))
(assert (! 
(>= fresh_index_2 0)
:named a39))

;(apply simplify)
;(apply (then simplify (or-else split-clause skip)))
;(apply (then simplify (repeat (or-else split-clause skip) 18)))

(assert (!
(< i1 i2)
:named b1))
(assert (!
(< i2 i3)
:named b2))
(assert (!
(distinct (rd c1 i2) (rd c2 i2))
:named b3))
(assert (!
(=> (= (rd c2 fresh_index_1) (rd c1 fresh_index_1)) (= fresh_index_1 0))
:named b4))
(assert (!
(=> (> i1 fresh_index_1) (or (= (rd c2 i1) (rd c1 i1)) (= i1 fresh_index_1)))
:named b5))
(assert (!
(=> (> i2 fresh_index_1) (or (= (rd c2 i2) (rd c1 i2)) (= i2 fresh_index_1)))
:named b6))
(assert (!
(=> (> i3 fresh_index_1) (or (= (rd c2 i3) (rd c1 i3)) (= i3 fresh_index_1)))
:named b7))
(assert (!
(=> (> fresh_index_1 fresh_index_1)
    (or (= (rd c2 fresh_index_1) (rd c1 fresh_index_1))
        (= fresh_index_1 fresh_index_1)))
:named b8))
(assert (!
(=> (> fresh_index_1 fresh_index_1)
    (or (= (rd c2 fresh_index_1) (rd c1 fresh_index_1))))
:named b9))
(assert (!
(>= fresh_index_1 fresh_index_2)
:named b10))
(assert (!
(=> (> fresh_index_1 fresh_index_2)
    (distinct (rd c2 fresh_index_1) (rd c1 fresh_index_1)))
:named b11))
(assert (!
(=> (= fresh_index_1 fresh_index_2) (= fresh_index_1 0))
:named b12))
(assert (!
(=> (= (rd c2 fresh_index_2) (rd c1 fresh_index_2)) (= fresh_index_2 0))
:named b13))
(assert (!
(=> (> i1 fresh_index_2)
    (or (= (rd c2 i1) (rd c1 i1)) (= i1 fresh_index_1) (= i1 fresh_index_2)))
:named b14))
(assert (!
(=> (> i2 fresh_index_2)
    (or (= (rd c2 i2) (rd c1 i2)) (= i2 fresh_index_1) (= i2 fresh_index_2)))
:named b15))
(assert (!
(=> (> i3 fresh_index_2)
    (or (= (rd c2 i3) (rd c1 i3)) (= i3 fresh_index_1) (= i3 fresh_index_2)))
:named b16))
(assert (!
(=> (> fresh_index_1 fresh_index_2)
    (or (= (rd c2 fresh_index_1) (rd c1 fresh_index_1))
        (= fresh_index_1 fresh_index_1)
        (= fresh_index_1 fresh_index_2)))
:named b17))
(assert (!
(=> (> fresh_index_2 fresh_index_2)
    (or (= (rd c2 fresh_index_2) (rd c1 fresh_index_2))
        (= fresh_index_2 fresh_index_1)
        (= fresh_index_2 fresh_index_2)))
:named b18))
(assert (!
(=> (> fresh_index_2 fresh_index_1)
    (or (= (rd c2 fresh_index_2) (rd c1 fresh_index_2))))
:named b19))
(assert (!
(=> (> fresh_index_2 fresh_index_2)
    (or (= (rd c2 fresh_index_2) (rd c1 fresh_index_2))
        (= fresh_index_2 fresh_index_1)))
:named b20))
(assert (!
(>= i1 0)
:named b21))
(assert (!
(>= i2 0)
:named b22))
(assert (!
(>= i3 0)
:named b23))
(assert (!
(>= fresh_index_1 0)
:named b24))
(assert (!
(>= fresh_index_2 0)
:named b25))

(check-sat)
(get-unsat-core)
