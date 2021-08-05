(set-option :produce-interpolants true)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun e () Int)
(declare-fun f (Int) Int)

(define-fun myinterp () Bool
(and (= (f x) x) (<= x 10) (<= (- x) (- 5))  (<= y 10) (<= (+ y x) 20) (<= (- y x) 0) (<= (- y) (- 5))   (<= (- x y) 0) (<= (- (- y) x) (- 10)))
)

(push 1)
(assert (! 
(and 
(<= (- y x) 0)
(<= (- x y) 10)
(<= (+ x y) 20)
(<= (- (- x) y) (- 10))
(<= (- x e) 0)
(<= (- e y) 0)
(= (f e) x)
)
:interpolation-group f1))
(assert (! 
(>= x 20)
:interpolation-group f2))
(check-sat)
(get-interpolant (f1))
(pop 1)

(push 1)
(assert (! 
(and 
(<= (- y x) 0)
(<= (- x y) 10)
(<= (+ x y) 20)
(<= (- (- x) y) (- 10))
(<= (- x e) 0)
(<= (- e y) 0)
(= (f e) x)
)
:interpolation-group f1))
(assert (! 
(distinct x y)
:interpolation-group f2))
(check-sat)
(get-interpolant (f1))
(pop 1)

(push 1)
(assert (! 
(and 
(<= (- y x) 0)
(<= (- x y) 10)
(<= (+ x y) 20)
(<= (- (- x) y) (- 10))
(<= (- x e) 0)
(<= (- e y) 0)
(= (f e) x)
)
:interpolation-group f1))
(assert (! 
(distinct (f x) x)
:interpolation-group f2))
(check-sat)
(get-interpolant (f1))
(pop 1)

(push 1)
(assert (! 
(and 
(<= (- y x) 0)
(<= (- x y) 10)
(<= (+ x y) 20)
(<= (- (- x) y) (- 10))
(<= (- x e) 0)
(<= (- e y) 0)
(= (f e) x)
)
:interpolation-group f1))
(assert (! 
(distinct (f y) x)
:interpolation-group f2))
(check-sat)
(get-interpolant (f1))
(pop 1)
