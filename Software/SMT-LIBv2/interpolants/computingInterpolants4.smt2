;; activate interpolation
(set-option :produce-interpolants true)

(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)
(declare-fun t () Bool)

(define-fun A () Bool (and (or p (not r)) (or p q) (or q (not r)) q))
(define-fun B () Bool (and t r (not p)))

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

(exit)