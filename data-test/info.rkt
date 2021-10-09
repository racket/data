#lang info

(define collection 'multi)

(define deps '("base"))

(define pkg-desc "tests for \"data-lib\"")

(define pkg-authors '(ryanc))
(define build-deps '("data-enumerate-lib"
                     "racket-index"
                     "data-lib"
                     "rackunit-lib"
                     "math-lib"))
(define update-implies '("data-lib"))

(define license
  '(Apache-2.0 OR MIT))
