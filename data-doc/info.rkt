#lang info

(define collection 'multi)

(define deps '("base"))

(define pkg-desc "documentation part of \"data\"")

(define pkg-authors '(ryanc))
(define build-deps '(["data-lib" #:version "1.2"]
                     "data-enumerate-lib"
                     "racket-doc"
                     "scribble-lib"
                     "plot-lib"
                     "math-doc"
                     "math-lib"
                     "pict-doc"
                     "pict-lib"))
(define update-implies '("data-lib" "data-enumerate-lib"))

(define license
  '(Apache-2.0 OR MIT))
