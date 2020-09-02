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

(define-fun my_interpolant () Bool 

(let ((a!1 (and (<= (+ (* (- 1) x1) y1) 0) (<= (+ x1 (* (- 1) y1)) (- 1)))))
(let ((a!2 (or (= x1 y1) a!1 (<= (+ (* (- 1) x1) y1) (- 1)))))
(let ((a!3 (or (not (= (f x1) 0)) (= 0 (f x1)) (and a!2 (not (= x1 y1)))))
      (a!5 (or (= x1 y1) (and a!2 (not (= x1 y1))))))
(let ((a!4 (or (not (= x1 y1)) (= (f y1) 0) (and (= (f x1) 0) a!3))))
  (and a!4 a!5)))))
)

(define-fun z3_interpolant () Bool
(and (>= (+ x1 (* (- 1) y1)) 0) (= (f x1) 0))
)

(define-fun mathsat_interpolant () Bool
(or (= (f y1) 0) (<= 1 (+ x1 (* (- 1) y1))))
)

(push)
;; The following returns sat, which means
;; that my_interpolant does not imply z3_interpolant
(assert (not (implies my_interpolant z3_interpolant)))
(check-sat)
(pop)
(push)
;; The following returns unsat, which means
;; that z3_interpolant implies my_interpolant
(assert (not (implies z3_interpolant my_interpolant)))
(check-sat)
(pop)
(push)
;; The following returns unsat, which means
;; that my_interpolant implies math_interpolant
(assert (not (implies my_interpolant mathsat_interpolant)))
(check-sat)
(pop)
(push)
;; The following returns sat, which means
;; that mathsat_interpolant does not imply my_interpolant
(assert (not (implies mathsat_interpolant my_interpolant )))
(check-sat)
(pop)
(push)
;; The following returns unsat, which means
;; that z3_interpolant implies math_interpolant
(assert (not (implies z3_interpolant mathsat_interpolant)))
(check-sat)
(pop)
(push)
;; The following returns sat, which means
;; that mathsat_interpolant does not imply z3_interpolant
(assert (not (implies mathsat_interpolant z3_interpolant )))
(check-sat)
(pop)
