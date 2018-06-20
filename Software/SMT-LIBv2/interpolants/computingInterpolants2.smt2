;; activate interpolation
(set-option :produce-interpolants true)

(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)

(define-fun A () Bool (and (not b) (or (not a) b c) a))
(define-fun B () Bool (or (not a) (not c)) )

;; use annotation :interpolation-group to partition the input problem into
;; several groups
(assert (! A :interpolation-group g1))
(assert (! B :interpolation-group g2))

(check-sat)

;; compute an interpolant for the given partition: the argument to
;; get-interpolant is a list of groups forming the A-part of the interpolation
;; problem
(get-interpolant (g1))
(get-interpolant (g2))
(get-interpolant (g1 g2))

(exit)