(declare-fun c_y1 () Int)
(declare-fun c_x1 () Int)
(declare-fun a_a () Int)
(declare-fun b_b () Int)

(define-fun part_a () Bool
(not
(or
 (not (<= c_y1 a_a))
 (not (= c_x1 a_a))
 (= c_x1 c_y1)
)
)
)


(define-fun part_b () Bool
(not
(or
 (not (<= c_x1 b_b))
 (not (= c_y1 b_b))
)
)
)

(define-fun interp () Bool
(let ((a!1 (and (<= (+ (* (- 1) c_x1) c_y1) 0)
                (<= (+ c_x1 (* (- 1) c_y1)) (- 1)))))
(let ((a!2 (or (= c_x1 c_y1) a!1 (<= (+ (* (- 1) c_x1) c_y1) (- 1)))))
  (and a!2 (not (= c_x1 c_y1)))))
)

(assert (and part_a part_b)) ;unsat
;(assert (not (implies part_a interp))) ;unsat
;(assert (and part_b interp)) ;unsat

(check-sat)
