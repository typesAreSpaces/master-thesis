(set-option :produce-unsat-cores true)
(declare-sort A)
(declare-fun f (A A) A)
(declare-fun z1 () A)
(declare-fun z2 () A)
(declare-fun s1 () A)
(declare-fun s2 () A)
(declare-fun y1 () A)
(declare-fun y2 () A)
(declare-fun u () A)
(declare-fun t () A)

(push)
(assert (= (f z1 u) s1))
(assert (= (f z2 u) s2))
(assert (= (f (f y1 u) (f y2 u)) t))
(check-sat)
(pop)

(push)
;; ---------------------------------
;; A part
(assert (= (f z1 u) s1))
(assert (= (f z2 u) s2))
(assert (= (f (f y1 u) (f y2 u)) t))
;; ---------------------------------
;; B part
(assert (= y1 z1))
(assert (= y2 z2))
(assert (not (= t (f s1 s2))))
(check-sat)
(pop)

(push)
;; ---------------------------------
;; A-Interpolant
(assert (! (=> (and (= z1 y1) (= z1 y2)) (= (f s1 s2) t)) :named a1))
(assert (! (=> (and (= z1 y1) (= z2 y2)) (= (f s1 s2) t)) :named a2))
(assert (! (=> (and (= z2 y1) (= z1 y2)) (= (f s2 s1) t)) :named a3))
(assert (! (=> (and (= z2 y1) (= z2 y2)) (= (f s2 s2) t)) :named a4))
(assert (! (=> (= z1 z2) (= s1 s2)) :named a5))
;; ---------------------------------
;; B part
(assert (! (= y1 z1) :named b1))
(assert (! (= y2 z2) :named b2))
(assert (! (not (= t (f s1 s2))) :named b3))
(check-sat)
(echo "The unsat core is:")
(get-unsat-core)
(pop)
