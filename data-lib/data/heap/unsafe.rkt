#lang racket/base

(require (submod "../heap.rkt" unchecked)
         (only-in "../heap.rkt" heap-sort!)) 
(provide (all-from-out (submod "../heap.rkt" unchecked))
         heap-sort!)
