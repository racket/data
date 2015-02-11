#lang racket/base
(require "enumerate/unsafe.rkt"
         racket/contract
         racket/list
         racket/bool)

(provide 
 in-enum
 (contract-out
  [enum? (-> any/c boolean?)]
  [finite-enum? (-> any/c boolean?)]
  [infinite-enum? (-> any/c boolean?)]
  [two-way-enum? (-> any/c boolean?)]
  [one-way-enum? (-> any/c boolean?)]
  [flat-enum? (-> any/c boolean?)]
  
  [from-nat 
   (->i ([e enum?]
         [n nat?])
        #:pre/name (e n) 
        "n in bounds of enumeration size"
        (or (infinite-enum? e)
            (< n (enum-size e)))
        [res (e) (enum-contract e)])]
  [to-nat
   (->i ([e two-way-enum?] [v (e) (enum-contract e)])
        [result nat?])]
  [enum-size (-> finite-enum? nat?)]
  [enum-contract (-> enum? contract?)]
  
  [enum->list
   (->i ([e enum?])
        ([s (e) (if (finite-enum? e)
                    (integer-in 0 (enum-size e))
                    exact-nonnegative-integer?)])
        #:pre (e s)
        (implies (unsupplied-arg? s) (finite-enum? e))
        [res (e) (listof (enum-contract e))])]
  
  [nat/e enum?]
  [below/e (-> exact-nonnegative-integer? enum?)]  
  [empty/e enum?]


  [map/e
   (->i ([in (e es c) 
             (dynamic->* #:mandatory-domain-contracts (map enum-contract (cons e es))
                         #:range-contracts (list c))]
         [out (e es c) 
              (dynamic->* #:mandatory-domain-contracts (list c)
                          #:range-contracts (map enum-contract (cons e es)))]
         [e enum?] 
         #:contract [c contract?])
        #:rest [es (listof enum?)]
        #:pre/desc (in out e es)
        (appears-to-be-a-bijection? in out (cons e es))
        [result enum?])]
  [pam/e (->i ([in (e es c)
                   (dynamic->* #:mandatory-domain-contracts (map enum-contract (cons e es))
                               #:range-contracts (list c))]
               [e enum?]
               #:contract [c contract?])
              #:rest [es (listof enum?)]
              [result one-way-enum?])]
  [except/e
   (->i ([e two-way-enum?])
        (#:contract [c (or/c #f contract?)]) ;; aka optional #f isn't considered a contract
        #:rest [more (e) (listof (enum-contract e))]
        [res two-way-enum?])]
  
  [or/e
   (->* () #:rest (listof (or/c (cons/c enum? (-> any/c boolean?))
                                flat-enum?))
        enum?)]
  [append/e
   (->* ((or/c (cons/c enum? (-> any/c boolean?))
               flat-enum?))
        #:rest (listof (or/c (cons/c enum? (-> any/c boolean?))
                             flat-enum?))
        enum?)]
  [thunk/e
   (->i ([mk-e (size is-two-way-enum? is-flat-enum?)
               (-> (and/c (if (or (unsupplied-arg? size) (= size +inf.0))
                              infinite-enum?
                              (and/c finite-enum?
                                     (let ([matching-size? (λ (e) (= (enum-size e) size))])
                                       matching-size?)))
                          (if (or (unsupplied-arg? is-two-way-enum?) is-two-way-enum?)
                              two-way-enum?
                              one-way-enum?)
                          (if (or (unsupplied-arg? is-flat-enum?) is-flat-enum?)
                              flat-enum?
                              (not/c flat-enum?))))])
        (#:size 
         [size extended-nat/c]
         #:two-way-enum?
         [is-two-way-enum? boolean?]
         #:flat-enum?
         [is-flat-enum? boolean?])
        [result enum?])]
  [list/e
   (->* ()
        (#:ordering (or/c 'diagonal 'square)) 
        #:rest (listof enum?)
        enum?)]
  [bounded-list/e (-> nat? nat? enum?)]
  [dep/e dep/e-contract]))

(define nat? exact-nonnegative-integer?)
(define extended-nat/c (or/c nat? +inf.0))

(define (appears-to-be-a-bijection? in out es)
  (cond
    [(for/or ([e (in-list es)])
       (zero? (enum-size e)))
     ;; can't check bijection on empty enumerations
     #t]
    [(for/or ([e (in-list es)])
       (one-way-enum? e))
     ;; we aren't going to build a bijection if
     ;; we aren't starting with two-way enumerations
     #t]
    [else
     (let/ec k
       (parameterize ([give-up-escape (λ () (k #t))])
         (for ([x (in-range 10)])
           (define indicies 
             (for/list ([e (in-list es)])
               (random (if (infinite-enum? e)
                           1000
                           (min 1000 (enum-size e))))))
           (define elements
             (for/list ([i (in-list indicies)]
                        [e (in-list es)])
               (from-nat e i)))
           (define round-trip-elements
             (call-with-values
              (λ () (out (apply in elements)))
              list))
           (define round-trip-indicies
             (for/list ([element (in-list round-trip-elements)]
                        [e (in-list es)])
               (to-nat e element)))
           (unless (equal? indicies round-trip-indicies)
             (define line1 "new enumeration would not be bijective")
             (cond
               [(null? (cdr es))
                (k (list line1
                         (format "passing ~a to `from-nat` produces:"
                                 (car indicies))
                         (to-values elements)
                         "which, when passed through `in' and `out', produces:"
                         (to-values round-trip-elements)
                         (format "which, when passed to `to-nat' produces ~a,"
                                 (car round-trip-indicies))
                         (format "but it should have been ~a"
                                 (car indicies))))]
               [else
                (k (append 
                    (list line1
                          "using `from-nat' with these indicies in the given enumerations:"
                          (to-values indicies)
                          "produces these values:")
                    (for/list ([e (in-list elements)])
                      (format " ~e" e))
                    (list "which, when passed through `in' and `out', produces these values:"
                          (to-values round-trip-elements)
                          "which results in these indicies:")
                    (for/list ([e (in-list elements)])
                      (format " ~e" e))))])))
         #t))]))


(define (to-values eles)
  (apply
   string-append
   (for/list ([e (in-list eles)])
     (format " ~e" e))))
