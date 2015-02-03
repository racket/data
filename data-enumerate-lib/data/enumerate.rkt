#lang racket/base
(require "enumerate/unsafe.rkt"
         racket/contract
         racket/list
         racket/bool)

(provide 
 (contract-out
  [enum (->i ([size extended-nat/c]
              [from-nat (contract) (-> exact-nonnegative-integer? contract)]
              [to-nat (contract) (or/c #f (-> contract exact-nonnegative-integer?))]
              [contract contract?])
            [result enum?])]
  [enum? (-> any/c boolean?)]
  [finite-enum? (-> any/c boolean?)]
  [infinite-enum? (-> any/c boolean?)]
  [enum-size (-> finite-enum? nat?)]
  [two-way-enum? (-> any/c boolean?)]
  [one-way-enum? (-> any/c boolean?)]
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
  [enum-contract (-> enum? contract?)]
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
  [approximate
   (->i ([e enum?] [s (e) (if (finite-enum? e)
                              (integer-in 0 (- (enum-size e) 1))
                              exact-nonnegative-integer?)])
        [res (e) (listof (enum-contract e))])]
  [to-list (->i ([e finite-enum?]) [result (e) (listof (enum-contract e))])]
  [take/e
   (->i ([e enum?] 
         [s (e) 
            (if (finite-enum? e)
                (integer-in 0 (- (enum-size e) 1))
                exact-nonnegative-integer?)])
        (#:contract [c contract?])
        #:pre (c e)
        (implies (unsupplied-arg? c)
                 (and (two-way-enum? e)
                      (flat-contract? (enum-contract e))))
        [result enum?])]
  [slice/e
   (->i ([e enum?] [lo nat?] [hi nat?])
        #:pre 
        (e lo hi)
        (and (or (infinite-enum? e)
                 (hi . <= . (enum-size e)))
             (hi . >= . lo))
        [res enum?])]
  [below/e
   (-> nat?
       enum?)]
  [empty/e enum?]
  [fin/e
   (->i ()
        #:rest
        [elements 
         (listof (or/c symbol? boolean? char? keyword? null?
                       string? bytes? number?))]
        #:pre/name (elements) 
        "no duplicate elements"
        (let() 
          (define-values (nums non-nums) (partition number? elements))
          (and (= (length (remove-duplicates nums =))
                  (length nums))
               (= (length (remove-duplicates non-nums))
                  (length non-nums))))
        [result enum?])]
  [nat/e enum?]
  [int/e enum?]
  [sum/e
   (->* () #:rest (listof (or/c flat-enum?
                                (cons/c enum? (-> any/c boolean?))))
        enum?)]
  [disj-append/e
   (->* ((or/c (cons/c enum? (-> any/c boolean?))
               flat-enum?))
        #:rest (listof (or/c (cons/c enum? (-> any/c boolean?))
                             flat-enum?))
        enum?)]
  [cons/e
   (->* (enum? enum?)
        (#:ordering (or/c 'diagonal 'square))
        enum?)]
  [traverse/e
   (-> (-> any/c enum?)
       (listof any/c)
       enum?)]
  [hash-traverse/e
   (-> (-> any/c enum?) hash?
       enum?)]
  [dep/e dep/e-contract]
  [flip-dep/e dep/e-contract]
  [thunk/e
   (->i ([s extended-nat/c]
         [mk-e (s is-two-way?)
               (cond
                 [(and (= s +inf.0) is-two-way?)
                  (-> (and/c two-way-enum? infinite-enum?))]
                 [(= s +inf.0)
                  (-> (and/c one-way-enum? infinite-enum?))]
                 [else
                  (define (matching-size? n) (= (enum-size n) s))
                  (-> (and/c (if is-two-way?
                                 (and/c two-way-enum? finite-enum?)
                                 (and/c one-way-enum? finite-enum?))
                             matching-size?))])])
        (#:two-way-enum? [is-two-way? boolean?])
        [result enum?])]
  [fix/e
   (case->
    (-> (-> enum? enum?) 
        enum?)
    (-> extended-nat/c (-> enum? enum?)
        enum?))]
  [many/e
   (case->
    (-> enum?
        enum?)
    (-> enum? nat?
        enum?))]
  [many1/e
   (-> enum? 
       enum?)]
  [cantor-vec/e
   (->* () #:rest (listof enum?)
        enum?)]
  [vec/e
   (->* () #:rest (listof enum?)
        enum?)]
  [box-vec/e
   (->* () #:rest (listof enum?)
        enum?)]
  [list/e
   (->* ()
        (#:ordering (or/c 'diagonal 'square)) 
        #:rest (listof enum?)
        enum?)]
  [bounded-list/e
   (-> nat? nat?
       enum?)]
  [nat+/e
   (-> nat?
       enum?)]
  [fail/e
   (-> exn?
       enum?)]))

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

(define dep/e-contract
  (->i ([e enum?]
        [f (e f-range-finite?)
           (-> (enum-contract e)
               (and/c (if (or (unsupplied-arg? f-range-finite?)
                              (not f-range-finite?))
                          infinite-enum?
                          finite-enum?)
                      (if (two-way-enum? e)
                          two-way-enum?
                          one-way-enum?)))])
       (#:f-range-finite? [f-range-finite? boolean?])
       [res enum?]))
