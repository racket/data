#lang racket/base

(require (prefix-in : "lib.rkt")
         (prefix-in unsafe: "unsafe.rkt")
         racket/stream
         racket/contract)

(provide (all-defined-out))

(define (map/e f1 f2 . es)
  (apply unsafe:map/e f1 f2 #:contract any/c es))

(define enum? :enum?)
(define size :enum-count)
(define from-nat :from-nat)
(define to-nat :to-nat)
(define (filter/e . args) (error 'filter/e "this one is gone; don't use it"))
(define except/e :except/e)
(define (to-stream e)
  (cond
    [(:finite-enum? e)
     (let loop ([n 0])
       (cond [(n . >= . (:enum-count e))
              empty-stream]
             [else
              (stream-cons (:from-nat e n)
                           (loop (add1 n)))]))]
    [else
     (let loop ([n 0])
       (stream-cons (:from-nat e n) (loop (add1 n))))]))
(define approximate :enum->list)
(define to-list :enum->list)
(define take/e :take/e)
(define slice/e :slice/e)
(define below/e :below/e)
(define empty/e :empty/e)
(define const/e :fin/e)
(define (from-list/e l) (apply fin/e l))
(define fin/e :fin/e)
(define nat/e :natural/e)
(define int/e :integer/e)
(define disj-sum/e :or/e)
(define disj-append/e :append/e)
(define fin-cons/e :cons/e)
(define cons/e :cons/e)
(define (elegant-cons/e a b) (cons/e a b))
(define (traverse/e f xs) (apply :list/e (map f xs)))
(define hash-traverse/e :hash-traverse/e)
(define (dep/e e f) (:cons/de [hd e] [tl (hd) (f hd)]))
(define (dep2/e n e f) (:cons/de [hd e] [tl (hd) (f hd)]))
(define fold-enum :fold-enum)
(define (flip-dep/e e f) (:cons/de [hd (tl) (f tl)] [tl e]))
(define range/e :range/e)
(define thunk/e :thunk/e)
(define fix/e
  (case-lambda
    [(n f) (define e (:thunk/e (λ () (f e)) #:count n)) e]
    [(f) (fix/e f)]))
(define many/e
  (case-lambda
    [(e n) (:listof-n/e nat/e n)]
    [(e) (:listof/e e)]))
(define many1/e :non-empty-listof/e)
(define (cantor-vec/e . args) (apply :vector/e #:ordering 'diagonal args))
(define vec/e :vector/e)
(define box-vec/e :vector/e)
(define inf-fin-fair-list/e :list/e)
;; (define mixed-box-tuples/e :mixed-box-tuples/e) this one was strange and not what the docs said
(define inf-fin-cons/e :cons/e)
(define list/e :list/e)
(define nested-cons-list/e :list/e)
(define (cantor-list/e . args) (apply :list/e #:ordering 'diagonal args))
(define box-list/e :list/e)
(define prime-length-box-list/e :list/e)
(define box-tuples/e unsafe:box-tuples/e)
(define bounded-list/e :bounded-list/e)
(define nat+/e :nat+/e)
; (define fail/e :fail/e) ;; probably not used
(define char/e :char/e)
(define string/e :string/e)
(define from-1/e (:nat+/e 1))
(define integer/e :integer/e)
(define float/e :flonum/e)
(define real/e :real/e)
;; (define non-real/e :non-real/e) ;; hopefully not used
(define num/e :number/e)
(define bool/e :bool/e)
(define symbol/e :symbol/e)
(define base/e (:or/e (:fin/e '())
                      (cons :two-way-number/e number?)
                      :string/e
                      :bool/e
                      :symbol/e))
(define any/e (:delay/e
               (:or/e (cons base/e (λ (x) (not (pair? x))))
                      (cons (cons/e any/e any/e) pair?))
               #:count +inf.0))
