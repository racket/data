#lang racket/base
(require data/enumerate rackunit)
(provide check-bijection? check-bijection/just-a-few?)

(define (do-check-bijection e confidence)
  (define nums (build-list (if (finite-enum? e)
                               (if (<= (enum-count e) confidence)
                                   (enum-count e)
                                   confidence)
                               confidence)
                           values))
  (andmap =
          nums
          (map (λ (n)
                 (to-nat e (from-nat e n)))
               nums)))
(define-simple-check (check-bijection? e)
  (do-check-bijection e 1000))
(define-simple-check (check-bijection/just-a-few? e)
  (do-check-bijection e 100))
