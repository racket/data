#lang racket/base
(require racket/bool
         racket/list
         racket/contract
         "../enumerate.rkt"
         "private/more.rkt"
         (prefix-in unsafe: "private/core.rkt"))

(provide
 (all-from-out "../enumerate.rkt")
 cons/de
 char/e
 string/e
 integer/e
 flonum/e
 exact-rational/e
 real/e
 two-way-real/e
 number/e
 two-way-number/e
 bool/e
 symbol/e
 delay/e
 (contract-out
  [flip-dep/e unsafe:dep/e-contract]
  [random-index
   (-> enum? exact-nonnegative-integer?)]
  [infinite-sequence/e
   (-> finite-enum? enum?)]
  [set/e
   (-> enum? enum?)]
  [permutations/e
   (-> list? enum?)]
  [permutations-of-n/e
   (-> exact-nonnegative-integer? enum?)]
  [nat+/e (-> exact-nonnegative-integer? enum?)]
  [fold-enum
   (->i ([f (f-range-finite?)
            (if (or (unsupplied-arg? f-range-finite?)
                    (not f-range-finite?))
                (-> list? any/c infinite-enum?)
                (-> list? any/c finite-enum?))]
         [l list?])
        (#:f-range-finite? [f-range-finite? boolean?])
        [result enum?])]
  
  [range/e
   (->i ([low (or/c exact-integer? -inf.0)]
         [high (or/c exact-integer? +inf.0)])
        #:pre (low high) (<= low high)
        [res enum?])]
  [listof/e listof/e-contract]
  [non-empty-listof/e listof/e-contract]
  
  [listof-n/e (-> enum? exact-nonnegative-integer? enum?)]
  [take/e
   (->i ([e enum?] 
         [s (e) 
            (if (finite-enum? e)
                (integer-in 0 (- (enum-count e) 1))
                exact-nonnegative-integer?)])
        (#:contract [c contract?])
        #:pre (c e)
        (implies (unsupplied-arg? c)
                 (and (two-way-enum? e)
                      (flat-contract? (enum-contract e))))
        [result enum?])]
  [slice/e
   (->i ([e enum?] [lo exact-nonnegative-integer?] [hi exact-nonnegative-integer?])
        (#:contract [c contract?])
        #:pre (lo hi) (<= lo hi)
        #:pre (e hi) (or (infinite-enum? e) (hi . <= . (enum-count e)))
        #:pre (c e)
        (implies (unsupplied-arg? c)
                 (and (two-way-enum? e)
                      (flat-contract? (enum-contract e))))
        [res enum?])]
  [hash-traverse/e
   (-> (-> any/c enum?) 
       hash?
       #:get-contract (-> any/c contract?)
       enum?)]
  [cons/e
   (->* (enum? enum?)
        (#:ordering (or/c 'diagonal 'square))
        enum?)]
  [vector/e
   (->* ()
        (#:ordering (or/c 'diagonal 'square)) 
        #:rest (listof enum?)
        enum?)]
  [single/e
   (->* (any/c)
        (#:equal? (-> any/c any/c boolean?))
        finite-enum?)]
  
  [fin/e
   (->i ()
        #:rest
        [elements (listof any/c)]
        #:pre/name (elements) 
        "no duplicate elements"
        (let ()
          (define-values (nums non-nums) (partition number? elements))
          (and (= (length (remove-duplicates nums =))
                  (length nums))
               (= (length (remove-duplicates non-nums))
                  (length non-nums))))
        [result enum?])]))

(define listof/e-contract
  (->i ([e (simple-recursive?) 
           (if (or (unsupplied-arg? simple-recursive?)
                   simple-recursive?)
               enum?
               infinite-enum?)])
       (#:simple-recursive? [simple-recursive? any/c])
       [res enum?]))
