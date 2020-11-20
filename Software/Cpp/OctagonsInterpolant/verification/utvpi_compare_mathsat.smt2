(set-option :produce-interpolants true)

(declare-fun x_0 () Int)
(declare-fun x_1 () Int)
(declare-fun x_2 () Int)

(push 1)
(assert (! (and
  (<= (+ x_0 x_1) (- 4))
  (<= (+ (- x_2) x_0) (- 10))
  (<= (- x_0) (- 8))
) :interpolation-group f1))
(assert (! (and
  (<= (- x_1 x_2) 6)
  (<= (- (- x_1) x_2) (- 8))
  (<= (- x_1) (- 4))
) :interpolation-group f2))
(check-sat)
(get-interpolant (f1))
(pop 1)

(push 1)
(assert (! (and
  (<= (+ x_0 x_1) (- 4))
  (<= (+ (- x_2) x_0) (- 10))
  (<= (- x_0) (- 8))
) :interpolation-group f1))
(assert (! (and
  (<= x_1 (- 10))
  (<= (+ (- x_1) x_2) 2)
) :interpolation-group f2))
(check-sat)
(get-interpolant (f1))
(pop 1)
