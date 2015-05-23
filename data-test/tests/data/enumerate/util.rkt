#lang racket/base
(require data/enumerate rackunit)
(provide check-bijection? check-bijection/just-a-few?)

(define (do-check-bijection e confidence)
  (for/and ([n (in-range (if (finite-enum? e)
                             (min (enum-count e) confidence)
                             confidence))])
    (= n (to-nat e (from-nat e n)))))
(define-simple-check (check-bijection? e)
  (do-check-bijection e 1000))
(define-simple-check (check-bijection/just-a-few? e)
  (do-check-bijection e 100))
