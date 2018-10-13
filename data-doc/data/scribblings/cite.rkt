#lang racket
(require scriblib/autobib) 
(provide (all-defined-out))

(define-cite ~cite citet generate-bibliography)

(define whats-the-difference
  (make-bib
   #:title "What's the difference? A Functional Pearl on Subtracting Bijections"
   #:author (authors "Brent Yorgey" "Kenneth Foner")
   #:date 2018
   #:location (proceedings-location "International Conference on Functional Programming")))
