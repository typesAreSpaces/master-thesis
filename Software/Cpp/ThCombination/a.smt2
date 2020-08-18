(declare-fun c_x1 () Int)
(declare-fun c_y1 () Int)
(declare-fun a_a () Int)
(declare-fun b_b () Int)
(declare-fun c_f (Int) Int)

(define-fun part_a () Bool 
(and
(= (c_f c_x1) 0)
(= c_x1 a_a)
(<= c_y1 a_a)
)
)

(define-fun part_b () Bool 
(and
(<= c_x1 b_b)
(= c_y1 b_b)
(distinct (c_f c_y1) 0)
)
)

(define-fun interp () Bool 
(let ((a!1 (and (<= (+ (* (- 1) c_x1) c_y1) 0)
                (<= (+ c_x1 (* (- 1) c_y1)) (- 1)))))
(let ((a!2 (or (= c_x1 c_y1) a!1 (<= (+ (* (- 1) c_x1) c_y1) (- 1)))))
(let ((a!3 (or (not (= c_x1 c_y1)) (and a!2 (not (= c_x1 c_y1))))))
  (and (= c_x1 c_y1) a!3))))
)

;(assert (and part_a part_b))
;(assert (not (implies part_a interp)))
(assert (and part_b interp))
(check-sat)
