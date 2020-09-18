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

(declare-fun euf_3 () Int)

(define-fun a_part () Bool (and
(= (+ (f x1) x2) 0)
(= y3 (+ (f y1) 0))
(<= y1 x1)
))

(define-fun b_part () Bool (and
(= x2 (g b))
(= 0 (g b))
(<= x1 y1)
(<= 1 y3)
))

(define-fun my_interp () Bool
(let ((a!1 (and (<= (+ (* (- 1) x1) y1) 0) (<= (+ x1 (* (- 1) y1)) (- 1))))
      (a!6 (and (<= x2 0)
                (>= x2 0)
                (<= (+ (* (- 1) y3) x2) 0)
                (<= (+ y3 (* (- 1) x2)) 0))))
(let ((a!2 (or (not (<= y1 x1)) (<= (+ (* (- 1) x1) y1) (- 1)) a!1)))
(let ((a!3 (and (or (= x1 y1) (not (<= x1 y1)) (and (<= y1 x1) a!2))
                (not (= x1 y1)))))
(let ((a!4 (and (or (not (= x1 y1)) (not (= x2 0))) (or (= x1 y1) a!3))))
(let ((a!5 (and (or (= x2 y3) a!4) (not (= x2 y3)))))
  (and (or (not (= x2 y3)) (not (<= 1 y3)) (not (= x2 0)) a!5 a!6)
       (or (= x2 y3) a!5)))))))
)

(push)
(assert (and a_part b_part))
(check-sat)
(pop)

(push)
(assert (not (implies a_part my_interp)))
(check-sat)
(pop)

(push)
(assert (and b_part my_interp))
(check-sat)
(pop)

;(compute-interpolant a_part b_part)
;(interpolants
 ;(let ((a!1 (and (not (= x1 y1)) (>= (+ x1 (* (- 1) y1)) 0))))
  ;(or (<= 0 (+ (* (- 1) y3) x3)) a!1 (not (= (* (- 1) y2) (* (- 1) x2))))))
