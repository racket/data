#lang info

(define collection 'multi)

;; the gvector stress tests use parallel threads
(define deps '(("base" #:version "8.18.0.2")))

(define pkg-desc "tests for \"data-lib\"")

(define pkg-authors '(ryanc))
(define build-deps '("data-enumerate-lib"
                     "racket-index"
                     ["data-lib" #:version "1.3"]
                     "rackunit-lib"
                     "math-lib"))
(define update-implies '("data-lib"))

(define license
  '(Apache-2.0 OR MIT))
