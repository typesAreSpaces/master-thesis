(set-option :produce-interpolants true)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun e () Int)
(declare-fun f (Int) Int)

(define-fun myinterp () Bool
(and (= (f x) x) (<= x 10) (<= (- x) (- 5))  (<= y 10) (<= (+ y x) 20) (<= (- y x) 0) (<= (- y) (- 5))   (<= (- x y) 0) (<= (- (- y) x) (- 10)))
)

(define-fun a () Bool
(and 
(<= (- y x) 0)
(<= (- x y) 10)
(<= (+ x y) 20)
(<= (- (- x) y) (- 10))
(<= (- x e) 0)
(<= (- e y) 0)
(= (f e) x)
)
)

(define-fun b_1 () Bool
(>= x 20)
)

(define-fun b_2 () Bool
(and
(distinct x y)
)
)

(define-fun b_3 () Bool
(and
(distinct (f x) x)
)
)

(define-fun b_4 () Bool
(and
(distinct (f y) x)
)
)

(push)
(assert (! a :named a1))
(assert (! b_1 :named b1))
(check-sat)
(get-interpolant a1 b1)
(pop)

(push)
(assert (! a :named a1))
(assert (! b_2 :named b1))
(check-sat)
(get-interpolant a1 b1)
(pop)

(push)
(assert (! a :named a1))
(assert (! b_3 :named b1))
(check-sat)
(get-interpolant a1 b1)
(pop)

(push)
(assert (! a :named a1))
(assert (! b_4 :named b1))
(check-sat)
(get-interpolant a1 b1)
(pop)

(echo "checking")

(push)
(assert (not (implies myinterp (<= x 15))))
(check-sat)
(pop)

(push)
(assert (not (implies myinterp (

let ((a!1 (not (<= (+ x (* (- 1) y)) 0))))
  (and (<= 0 (+ (* (- 1) x) y)) (or (= x y) a!1))

))))
(check-sat)
(pop)

(push)
(assert (not (implies myinterp (= (f x) x) )))
(check-sat)
(pop)

(push)
(assert (not (implies myinterp (let ((a!1 (not (<= (+ y (* (- 1) x)) 0))))
  (and (or a!1 (= (f y) x)) (>= (+ x (* (- 1) y)) 0))
))))
(check-sat)
(pop)
