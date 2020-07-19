#lang racket/base

(require "heap/unsafe.rkt"
         racket/contract/base)

(provide/contract
 [make-heap        (->  (and (procedure-arity-includes/c 2)
                             (unconstrained-domain-> any/c))
                        heap?)]
 [heap?            (->  any/c boolean?)]
 [heap-count       (->  heap? exact-nonnegative-integer?)]
 [heap-add!        (->* (heap?) () #:rest list? void?)]
 [heap-add-all!    (->  heap? (or/c list? vector? heap?) void?)]
 [heap-min         (->  heap? any/c)]
 [heap-remove-min! (->  heap? void?)]
 [heap-remove!     (->* (heap? any/c) [#:same? (-> any/c any/c any/c)] boolean?)]
 [heap-remove-eq!  (->  heap? any/c boolean?)]

 [vector->heap (-> (and (procedure-arity-includes/c 2)
                             (unconstrained-domain-> any/c))
                   vector?
                   heap?)]
 [heap->vector (-> heap? vector?)]
 [heap-copy    (-> heap? heap?)]

 [in-heap          (-> heap? sequence?)]
 [in-heap/consume! (-> heap? sequence?)])

(provide heap-sort!) ; checks done in-function
