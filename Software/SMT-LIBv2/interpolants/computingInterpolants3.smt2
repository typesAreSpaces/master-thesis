;; activate interpolation
(set-option :produce-interpolants true)

(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)

(define-fun A1 () Bool (not b))
(define-fun A2 () Bool (or (not a) b c))
(define-fun A3 () Bool a)
(define-fun B () Bool (or (not a) (not c)) )

;; use annotation :interpolation-group to partition the input problem into
;; several groups
(assert (! A1 :interpolation-group g1))
(assert (! A2 :interpolation-group g2))
(assert (! A3 :interpolation-group g3))
(assert (! B :interpolation-group g4))

(check-sat)

;; compute an interpolant for the given partition: the argument to
;; get-interpolant is a list of groups forming the A-part of the interpolation
;; problem
(get-interpolant (g1))
(get-interpolant (g2))
(get-interpolant (g3))
(get-interpolant (g4))
(get-interpolant (g1 g2 g3 g4))

(exit)