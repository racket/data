#lang racket/base
(require racket/contract
         racket/function
         racket/generator
         racket/stream
         (only-in racket/list remove-duplicates)
         math/base
         math/distributions
         math/number-theory
         math/flonum
         "../enumerate.rkt"
         (prefix-in unsafe: "unsafe.rkt"))

;; random-natural-w/o-limit : ([0,1] -> Nat) ∩ (-> Nat)
(define (random-natural-w/o-limit [prob-of-zero 0.01])
  (max (random-natural/no-mean prob-of-zero)
       (random-natural/no-mean prob-of-zero)
       (random-natural/no-mean prob-of-zero)))

;; random-natural/no-mean : [0,1] -> Nat
(define (random-natural/no-mean prob-of-zero)
  (define x (sample (geometric-dist prob-of-zero)))
  (define m1 (expt 2 (exact-floor x)))
  (define m0 (quotient m1 2))
  (random-integer m0 m1))

(define (random-index e)
  (define k (enum-size e))
  (if (infinite? k)
      (random-natural-w/o-limit)
      (random-natural k)))

(define (BPP-digits N)
  (let loop ([8Pi -8])
    (define 8i
      (+ 8 8Pi))

    (define (E k)
      (/ 1 (+ 8i k)))

    (define pi_i
      (* N
         (+ (* +4 (E 1))
            (* -2 (E 4))
            (* -1 (E 5))
            (* -1 (E 6)))))

    (for ([c (in-string (number->string pi_i))])
      (unless (eq? #\/ c)
        (yield (- (char->integer c) (char->integer #\0)))))

    (loop 8i)))

;; exported to tests/data/enumerate
(module+ test (provide BPP-digits 10-sequence->K-sequence))

(define (bits-of k)
  (/ (log k) (log 2)))

;; XXX just subtract k if greater than k and then push the digit to
;; left and go on
(define (10-sequence->K-sequence k seq)
  (cond
   [(< k 10)
    (10-sequence->sub10-sequence k seq)]
   [(= k 10)
    seq]
   [else
    (10-sequence->sup10-sequence k seq)]))

(define (10-sequence->sub10-sequence k seq)
  (in-generator
   (for ([d seq])
     (when (< d k)
       (yield d)))))

(define (10-sequence->sup10-sequence k seq)
  (in-generator
   (let loop ()
     (define d
       (for/sum ([i (in-range (ceiling (/ (log k) (log 10))))]
                 [sub-d seq])
         (* sub-d (expt 10 i))))
     (yield (modulo d k))
     (loop))))

(define (infinite-sequence/e inner/e)
  (define seed/e nat/e)
  (define K (enum-size inner/e))
  (define (seed->seq N)
    (define K-seq
      (10-sequence->K-sequence K (in-generator (BPP-digits (+ 1 N)))))
    (in-generator
     (for ([k K-seq])
       (yield (from-nat inner/e k)))))
  (pam/e seed->seq seed/e #:contract sequence?))

(define (permutations-of-n/e n)
  (cond
    [(zero? n)
     (fin/e '())]
    [else
     (define p-sub1 (permutations-of-n/e (sub1 n)))
     (define elem/c (integer-in 0 (- n 1)))
     (map/e
      values
      values
      (dep/e
       #:f-range-finite? #t
       (below/e n)
       (λ (v)
         (define (without-v-but-with-n? x) (not (member v x)))
         (unsafe:map/e
          (λ (l)
            (for/list ([i (in-list l)])
              (if (< i v)
                  i
                  (+ i 1))))
          (λ (l)
            (for/list ([i (in-list l)])
              (if (< i v)
                  i
                  (- i 1))))
          p-sub1
          #:contract
          any/c)))
      #:contract
      (and/c (apply list/c (build-list n (λ (_) elem/c)))
             no-duplicates?))]))

(define (no-duplicates? l) 
  (= (length (remove-duplicates l)) 
     (length l)))

(define (permutations/e l #:contract [c 
                                      (if (andmap contract? l)
                                          (apply or/c l)
                                          (error 'permutations/e
                                                 "expected an explicit contract"))])
  (define idx->e (list->vector l))
  (define e->idx
    (for/hash ([e (in-list l)]
               [i (in-naturals)])
      (values e i)))
  (map/e
   (λ (l)
     (for/list ([idx (in-list l)])
       (vector-ref idx->e idx)))
   (λ (l)
     (for/list ([e (in-list l)])
       (hash-ref e->idx e)))
   (permutations-of-n/e (vector-length idx->e))
   #:contract (and/c (apply list/c (build-list (length l) (λ (_) c)))
                     no-duplicates?)))

(provide
 (contract-out
  [random-index
   (-> enum? exact-nonnegative-integer?)]
  [infinite-sequence/e
   (-> enum? enum?)]
  [permutations/e
   (-> list? enum?)]
  [permutations-of-n/e
   (-> exact-nonnegative-integer? enum?)]))



;; to-stream seems like a bad idea; better
;; to make enumerations just be streams if
;; that's a useful thing to do
(define (to-stream e)
  (define (loop n)
    (cond [(n . >= . (enum-size e))
           empty-stream]
          [else
           (stream-cons (from-nat e n)
                        (loop (add1 n)))]))
  (loop 0))
(provide (contract-out [to-stream (-> enum? stream?)]))

(provide
 (contract-out
  [range/e
   (->i ([low (or/c exact-integer? -inf.0)]
         [high (or/c exact-integer? +inf.0)])
        #:pre (low high) (<= low high)
        [res enum?])]))

;; more utility enums
;; nats of course
(define (range/e low high)
  (cond 
    [(and (infinite? high) (infinite? low))
     int/e]
    [(infinite? high)
     (map/e
      (λ (n)
        (+ n low))
      (λ (n)
        (- n low))
      nat/e
      #:contract (and/c exact-integer? (>=/c low)))]
    [(infinite? low)
     (map/e
      (λ (n) (- high n))
      (λ (n) (- high n))
      nat/e
      #:contract (and/c exact-integer? (<=/c high)))]
    [else
     (map/e (λ (n) (+ n low))
            (λ (n) (- n low))
            (below/e (+ 1 (- high low)))
            #:contract (and/c (between/c low high)
                              exact-integer?))]))

(provide
 (contract-out
  [fold-enum
   (->i ([f (f-range-finite?)
            (if (or (unsupplied-arg? f-range-finite?)
                    (not f-range-finite?))
                (-> list? any/c infinite-enum?)
                (-> list? any/c finite-enum?))]
         [l list?])
        (#:f-range-finite? [f-range-finite? boolean?])
        [result enum?])]))

;; fold-enum : ((listof a), b -> enum a), (listof b) -> enum (listof a)
(define (fold-enum f l #:f-range-finite? [f-range-finite? #f])
  (define e
    (let loop ([l l]
               [acc (fin/e '())])
      (cond [(null? l) acc]
            [else
             (loop
              (cdr l)
              (flip-dep/e
               #:f-range-finite? f-range-finite?
               acc
               (λ (xs)
                 (f xs (car l)))))])))
  (map/e
   reverse
   reverse
   e
   #:contract (reverse/c (enum-contract e))))

(define (reverse/c ctc)
  ((cond
     [(chaperone-contract? ctc)
      make-chaperone-contract]
     [else
      make-contract])
   #:name `(reverse/c ,(contract-name ctc))
   #:first-order list?
   #:projection
   (let ([proj (contract-projection ctc)])
     (λ (b)
       (define proj+b (proj b))
       (λ (v)
         (if (list? v)
             (reverse (proj+b (reverse v)))
             (proj+b v)))))
   #:stronger (λ (this that) #f)
   #:list-contract? #t))

(define listof/e-contract
  (->i ([e (simple-recursive?) 
           (if (or (unsupplied-arg? simple-recursive?)
                   simple-recursive?)
               enum?
               infinite-enum?)])
       (#:simple-recursive? [simple-recursive? any/c])
       [res enum?]))
(provide
 (contract-out
  [listof/e listof/e-contract]
  [non-empty-listof/e listof/e-contract]))

(define (listof/e e #:simple-recursive? [simple-recursive? #t])
  (cond
    [simple-recursive?
     (define fix-size
       (if (and (finite-enum? e) (= 0 (enum-size e)))
           1
           +inf.0))
     (define result-e
       (fix/e #:size fix-size
              #:two-way-enum? (two-way-enum? e)
              #:flat-enum? (flat-enum? e)
              (λ (self)
                (or/e (cons (fin/e '()) null?)
                      (cons (cons/e e self) pair?)))))
     (map/e values values result-e #:contract (listof (enum-contract e)))]
    [else
     (or/e
      (fin/e '())
      (non-empty-listof/e e #:simple-recursive? #f))]))

(define (non-empty-listof/e e #:simple-recursive? [simple-recursive? #t])
  (cond
    [simple-recursive? 
     (except/e (listof/e e #:simple-recursive? #t) '()
               #:contract (non-empty-listof (enum-contract e)))]
    [else 
     (map/e 
      cdr 
      (λ (x) (cons (- (length x) 1) x))
      (dep/e
       nat/e
       (λ (i) (apply list/e (build-list (+ i 1) (λ (_) e)))))
      #:contract (non-empty-listof (enum-contract e)))]))

(provide
 (contract-out
  [listof-n/e (-> enum? exact-nonnegative-integer? enum?)]))
(define (listof-n/e e n)
  (apply list/e (build-list n (const e))))

;; Base Type enumerators

(provide
 char/e
 string/e
 from-1/e
 integer/e
 float/e
 exact-rational/e
 real/e
 two-way-real/e
 num/e
 two-way-num/e
 bool/e
 symbol/e
 base/e
 any/e)

(define (between? x low high)
  (and (>= x low)
       (<= x high)))
(define (range-with-pred/e-p low high)
  (cons (range/e low high)
        (λ (n) (between? n low high))))
(define low/e-p
  (range-with-pred/e-p #x61 #x7a))
(define up/e-p
  (range-with-pred/e-p #x41 #x5a))
(define bottom/e-p
  (range-with-pred/e-p #x0 #x40))
(define mid/e-p
  (range-with-pred/e-p #x5b #x60))
(define above1/e-p
  (range-with-pred/e-p #x7b #xd7FF))
(define above2/e-p
  (range-with-pred/e-p #xe000 #x10ffff))

(define char/e
  (map/e
   integer->char
   char->integer
   (disj-append/e low/e-p
                  up/e-p
                  bottom/e-p
                  mid/e-p
                  above1/e-p
                  above2/e-p)
   #:contract char?))

(define string/e
  (map/e
   list->string
   string->list
   (listof/e char/e)
   #:contract string?))

(define from-1/e
  (map/e add1
         sub1
         nat/e
         #:contract (and/c exact-nonnegative-integer? (>=/c 1))))

(define integer/e
  (let ()
    (define (i-from-nat x)
      (cond
        [(even? x) (- (/ x 2))]
        [else (/ (+ x 1) 2)]))
    (define (i-to-nat x)
      (cond
        [(<= x 0) (* (- x) 2)]
        [else (- (* x 2) 1)]))
    (map/e i-from-nat
           i-to-nat
           nat/e
           #:contract exact-integer?)))

(define normal-flonums/e-p
  (take/e (map/e
           ordinal->flonum
           flonum->ordinal
           integer/e
           #:contract flonum?)
          (+ 1 (* 2 9218868437227405311))
          #:contract 
          (and/c flonum?
                 (not/c infinite?)
                 (not/c nan?))))

(define float/e
  (disj-append/e (fin/e +inf.0 -inf.0)
                 (fin/e +nan.0)
                 normal-flonums/e-p))

(define exact-rational/e
  (or/e (fin/e 0)
        (pam/e (λ (pr) (/ (car pr) (cdr pr)))
               (cons/e (nat+/e 1) (nat+/e 2))
               #:contract (and/c rational? exact?))))
         
(define two-way-real/e (or/e integer/e float/e))
(define real/e (or/e float/e exact-rational/e))

(define (make-non-real/e rp ip ctc)
  (map/e make-rectangular
         (λ (z)
           (values (real-part z)
                   (imag-part z)))
         rp ip
         #:contract ctc))

(define (complex-with-exact-integer-parts? x)
  (and (number? x)
       (exact-integer? (real-part x))
       (exact-integer? (imag-part x))))
(define exact-integer-non-real/e
  (make-non-real/e (except/e int/e 0) (except/e int/e 0)
                   (and/c complex-with-exact-integer-parts? (not/c real?))))
(define float-non-real/e 
  (make-non-real/e float/e float/e
                   (and/c number? inexact? (not/c real?))))

;; only one-way, so don't need to skip 0
(define exact-rational-complex/e 
  (make-non-real/e exact-rational/e exact-rational/e
                   (and/c number? exact?)))

(define num/e
   (or/e real/e
         float-non-real/e
         exact-rational-complex/e))
(define (complex-with-exact-zero-real-part? x)
  (and (number? x)
       (equal? 0 (real-part x))))

(define two-way-num/e
  (or/e two-way-real/e
        (map/e (λ (x) (make-rectangular 0 x)) 
               imag-part
               two-way-real/e 
               #:contract complex-with-exact-zero-real-part?)
        exact-integer-non-real/e
        float-non-real/e))

(define bool/e (fin/e #t #f))

(define symbol/e
  (map/e
   (compose string->symbol list->string)
   (compose string->list symbol->string)
   (listof/e char/e)
   #:contract symbol?))

(define base/e
  (or/e (fin/e '())
        (cons num/e number?)
        string/e
        bool/e
        symbol/e))

(define any/e
  (fix/e #:size +inf.0
         (λ (any/e)
            (or/e (cons base/e (negate pair?))
                  (cons (cons/e any/e any/e) pair?)))))


(provide
 (contract-out
  [vector/e
   (->* ()
        (#:ordering (or/c 'diagonal 'square)) 
        #:rest (listof enum?)
        enum?)]))

(define (vector/e #:ordering [ordering 'square] . es)
  (map/e list->vector
         vector->list
         (apply list/e #:ordering ordering es)
         #:contract (apply vector/c (map enum-contract es))))


