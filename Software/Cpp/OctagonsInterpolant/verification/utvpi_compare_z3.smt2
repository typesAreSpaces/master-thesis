(set-option :produce-interpolants true)

(declare-fun x_0 () Int)
(declare-fun x_1 () Int)
(declare-fun x_2 () Int)

(define-fun myinter () Bool
(and
  (<= x_1 (- 12))
  (<= (- x_2) (- 18)))
)

(define-fun a_3 () Bool (and
  (<= (+ x_0 x_1) (- 4))
  (<= (+ (- x_2) x_0) (- 10))
  (<= (- x_0) (- 8))))

(define-fun b_3_1 () Bool (and
  (<= (- x_1 x_2) 6)
  (<= (- (- x_1) x_2) (- 8))
  (<= (- x_1) (- 4))))

(define-fun b_3_2 () Bool (and
  (<= x_1 (- 10))
  (<= (+ (- x_1) x_2) 2)))

(push)
(assert (! a_3 :named a5))
(assert (! b_3_1 :named b5))
(check-sat)
(get-interpolant a5 b5)
(pop)

(push)
(assert (! a_3 :named a6))
(assert (! b_3_2 :named b6))
(check-sat)
(get-interpolant a6 b6)
(pop)
