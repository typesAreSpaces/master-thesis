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

(define-fun part_a () Bool 
(and 
(= (f x1) 0)
(= x1 a)
(<= y1 a)
)
)

(define-fun part_b () Bool 
(and 
(<= x1 b)
(= y1 b)
(distinct (f y1) 0)
)
)

;(define-fun interp () Bool
;(let ((a!1 (and (<= (+ (* (- 1) x1) y1) 0) (<= (+ x1 (* (- 1) y1)) (- 1)))))
;(let ((a!2 (or (= x1 y1) a!1 (<= (+ (* (- 1) x1) y1) (- 1)))))
;(let ((a!3 (or (= x1 y1) (and a!2 (not (= x1 y1))))))
  ;(and (not (= x1 y1)) a!3))))
;)

(define-fun interp () Bool
(let ((a!1 (and (<= (+ (* (- 1) x1) y1) 0) (<= (+ x1 (* (- 1) y1)) (- 1)))))
(let ((a!2 (or (= x1 y1) a!1 (<= (+ (* (- 1) x1) y1) (- 1)))))
(let ((a!3 (or (not (= (f x1) 0)) (= 0 (f x1)) (and a!2 (not (= x1 y1)))))
      (a!5 (or (= x1 y1) (and a!2 (not (= x1 y1))))))
(let ((a!4 (or (not (= x1 y1)) (= (f y1) 0) (and (= (f x1) 0) a!3))))
  (and a!4 a!5)))))
)

;(assert (and part_a part_b))
;(assert (not (implies part_a interp)))
(assert (and interp part_b))
(check-sat)
