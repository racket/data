#lang info
(define collection 'multi)
(define deps '(("base" #:version "6.4.0.14")
               "data-lib" "math-lib"))
(define build-deps '("rackunit-lib"))

(define pkg-desc "implementation (no documentation) of \"data/enumerate\"")

(define pkg-authors '(maxsnew jay robby))
(define version "1.2")
