#lang racket/base
(require "enumerate/private/core.rkt"
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
            (< n (enum-count e)))
        [res (e) (enum-contract e)])]
  [to-nat
   (->i ([e two-way-enum?] [v (e) (enum-contract e)])
        [result nat?])]
  [enum-count (-> finite-enum? nat?)]
  [enum-contract (-> enum? contract?)]
  
  [enum->list
   (->i ([e enum?])
        ([s (e) (if (finite-enum? e)
                    (integer-in 0 (enum-count e))
                    exact-nonnegative-integer?)])
        #:pre (e s)
        (implies (unsupplied-arg? s) (finite-enum? e))
        [res (e) (listof (enum-contract e))])]
  
  [natural/e enum?]
  [below/e (-> (or/c exact-nonnegative-integer? +inf.0) enum?)]
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
   (->i ()
        (#:one-way-enum? [is-one-way-enum? boolean?])
        #:rest
        [enums (listof (or/c (cons/c enum? (-> any/c boolean?))
                             enum?))]
        #:pre/name (enums is-one-way-enum?)
        "the enums must either have at least one one-way-enum?\n or must all either be flat-enum? or have predicates"
        (or (and is-one-way-enum?
                 (not (unsupplied-arg? is-one-way-enum?)))
            (either-a-one-way-enum-or-all-have-predicates? enums))
        #:pre/desc (enums is-one-way-enum?)
        (non-overlapping? enums is-one-way-enum?)
        [result enum?])]
  [append/e
   (->i ([first (or/c (cons/c enum? (-> any/c boolean?))
                      enum?)])
        (#:one-way-enum? [is-one-way-enum? boolean?])
        #:rest [rest (listof (or/c (cons/c enum? (-> any/c boolean?))
                                   enum?))]
        #:pre/name (first rest is-one-way-enum?)
        "the enums must either have at least one one-way-enum?\n or must all either be flat-enum? or have predicates"
        (or (and is-one-way-enum?
                 (not (unsupplied-arg? is-one-way-enum?)))
            (either-a-one-way-enum-or-all-have-predicates? (cons first rest)))
        #:pre/desc (first rest is-one-way-enum?) 
        (non-overlapping? (cons first rest) is-one-way-enum?)
        [result enum?])]
  [thunk/e
   (->i ([mk-e (size is-two-way-enum? is-flat-enum?)
               (-> (and/c (if (or (unsupplied-arg? size) (= size +inf.0))
                              infinite-enum?
                              (and/c finite-enum?
                                     (let ([matching-size? (λ (e) (= (enum-count e) size))])
                                       matching-size?)))
                          (if (or (unsupplied-arg? is-two-way-enum?) is-two-way-enum?)
                              two-way-enum?
                              one-way-enum?)
                          (if (or (unsupplied-arg? is-flat-enum?) is-flat-enum?)
                              flat-enum?
                              (not/c flat-enum?))))])
        (#:count
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

(define (either-a-one-way-enum-or-all-have-predicates? r)
  (cond
    [(has-one-way-enum? r) 
     #t]
    [(for/and ([e/p (in-list r)])
       (or (flat-enum? e/p)
           (pair? e/p)))
     #t]
    [else #f]))

(define (non-overlapping? enum/pairs is-one-way-enum?)
  (define upper-limit-to-explore 1000)
  (define howmany (length enum/pairs))
  (cond
    [(or (and is-one-way-enum?
              (not (unsupplied-arg? is-one-way-enum?)))
         (has-one-way-enum? enum/pairs))
     #t]
    [(< howmany 2) #t]
    [else
     (define enums
       (for/list ([i (in-list enum/pairs)])
         (if (pair? i) (car i) i)))
     (define preds
       (for/list ([i (in-list enum/pairs)])
         (if (pair? i) (cdr i) (flat-contract-predicate (enum-contract i)))))
     (let/ec k
       (parameterize ([give-up-escape (λ () (k #t))])
         (for ([x (in-range 10)])
           (define starter-enum-index/zero-based (random howmany))
           (define starter-enum-index/one-based (+ starter-enum-index/zero-based 1))
           (define starter-enum (list-ref enums starter-enum-index/zero-based))
           (when (or (infinite-enum? starter-enum)
                     (not (zero? (enum-count starter-enum))))
             (define index (random (if (finite-enum? starter-enum)
                                       (min upper-limit-to-explore (enum-count starter-enum))
                                       upper-limit-to-explore)))
             (define value (from-nat starter-enum index))
             (define true-returning-indicies/one-based
               (for/list ([pred (in-list preds)]
                          [i (in-naturals)]
                          #:when (pred value))
                 (+ i 1)))
             
             (unless (member starter-enum-index/one-based true-returning-indicies/one-based)
               (k
                (list
                 (format "enumeration passed as argument ~a has a predicate that does not"
                         starter-enum-index/one-based)
                 "accept one of the values that the enumeration itself produces,"
                 (format "index: ~a" index)
                 (format "value: ~e" value))))
             
             (when (> (length true-returning-indicies/one-based) 1)
               (define exactly-two? (= 2 (length true-returning-indicies/one-based)))
               (define other-enums-indicies
                 (remove starter-enum-index/one-based true-returning-indicies/one-based))
               (define prefix
                 (list "new enumeration would not be two-way because of overlapping predicates"
                       (format
                        "the enum passed as argument ~a, when passed to `from-nat' with index ~a"
                        starter-enum-index/one-based
                        index)
                       (format "produces ~e," value)
                       (cond
                         [exactly-two?
                          (format "and the enumeration passed as argument ~a also accepts that value"
                                  (car other-enums-indicies))]
                         [else
                          (format "and the enumerations passed as arguments~a also accept that value"
                                  (cond
                                    [(= 2 (length other-enums-indicies))
                                     (format " ~a and ~a"
                                             (car other-enums-indicies)
                                             (cadr other-enums-indicies))]
                                    [else
                                     (apply string-append
                                            (let loop ([is other-enums-indicies])
                                              (cond
                                                [(null? (cdr is))
                                                 (list (format " and ~a" (car is)))]
                                                [else
                                                 (cons (format " ~a," (car is))
                                                       (loop (cdr is)))])))]))])))
               (k (append prefix
                          (for/list ([i (in-list true-returning-indicies/one-based)])
                            (format "arg ~a: ~e" i (list-ref enum/pairs (- i 1)))))))))
         #t))]))
     
(define (has-one-way-enum? r)
  (for/or ([e/p (in-list r)])
    (or (one-way-enum? e/p)
        (and (pair? e/p)
             (one-way-enum? (car e/p))))))

(define nat? exact-nonnegative-integer?)
(define extended-nat/c (or/c nat? +inf.0))

(define (appears-to-be-a-bijection? in out es)
  (cond
    [(for/or ([e (in-list es)])
       (zero? (enum-count e)))
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
                           (min 1000 (enum-count e))))))
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
             (define line1 "new enumeration would not be two-way")
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
