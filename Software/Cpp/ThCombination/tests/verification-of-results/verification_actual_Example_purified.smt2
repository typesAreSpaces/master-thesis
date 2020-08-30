(declare-fun c_x1 () Int)
(declare-fun c_x2 () Int)
(declare-fun c_x3 () Int)
(declare-fun c_y1 () Int)
(declare-fun c_y2 () Int)
(declare-fun c_y3 () Int)
(declare-fun c_oct_1 () Int)
(declare-fun c_oct_2 () Int)
(declare-fun a_a () Int)
(declare-fun b_b () Int)
(declare-fun c_f (Int) Int)
(declare-fun c_g (Int) Int)

(define-fun part_a () Bool 
(and 
(= (c_f c_x1) c_oct_1)
(= c_x1 a_a)
(= 0 c_oct_1)
(<= c_y1 a_a)
)
)

(define-fun part_b () Bool 
(and 
(= c_y1 b_b)
(distinct (c_f c_y1) c_oct_2)
(<= c_x1 b_b)
(= 0 c_oct_2)
)
)

(define-fun interp_ () Bool

(let ((a!1 (and (<= (+ (* (- 1) c_x1) c_y1) 0)
                (<= (+ c_x1 (* (- 1) c_y1)) (- 1)))))
(let ((a!2 (or (= c_x1 c_y1) a!1 (<= (+ (* (- 1) c_x1) c_y1) (- 1)))))
(let ((a!3 (or (= c_x1 c_y1) (and a!2 (not (= c_x1 c_y1))))))
  (and (not (= c_x1 c_y1)) a!3))))
)

;(assert (and part_a part_b))
;(assert (not (implies part_a interp_))) ;; Giving problems
;(assert (and interp_ part_b))
;(check-sat)
(compute-interpolant part_a part_b)
