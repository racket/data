#lang racket/base
(require data/enumerate
         rackunit
         (for-syntax racket/base)
         racket/contract)
(provide check-bijection? check-bijection/just-a-few?
         check-contract)

(define (do-check-bijection e confidence)
  (for/and ([n (in-range (if (finite-enum? e)
                             (min (enum-count e) confidence)
                             confidence))])
    (= n (to-nat e (from-nat e n)))))
(define-simple-check (check-bijection? e)
  (do-check-bijection e 1000))
(define-simple-check (check-bijection/just-a-few? e)
  (do-check-bijection e 100))


(define-syntax (check-contract stx)
  (syntax-case stx ()
    [(_ e)
     (with-syntax ([line (syntax-line stx)])
       #'(check-contract/proc line e 'e))]))

(define (check-contract/proc line enum enum-code)
  (for ([x (in-range (if (finite-enum? enum)
                         (min (enum-count enum) 100)
                         100))])
    (contract-exercise
     (contract (enum-contract enum)
               (from-nat enum x)
               'ignore-me
               'whatever
               (format "~s, index ~a" enum-code x)
               #f)))
  
  (when (two-way-enum? enum)
    (let/ec give-up-completely
      (for ([x (in-range 100)])
        (let/ec give-up-this-attempt
          (define value
            (contract-random-generate
             (enum-contract enum)
             2
             (λ (no-generator?)
               (cond
                 [no-generator?
                  (eprintf "no generator for:\n  ~s\n  ~s\n" 
                           enum-code
                           (enum-contract enum))
                  (give-up-completely (void))]
                 [else
                  (give-up-this-attempt)]))))
          (with-handlers ([exn:fail?
                           (λ (x)
                             (eprintf "test/data/enumerate: trying ~s\n" value)
                             (raise x))])
            (to-nat enum value)))))))