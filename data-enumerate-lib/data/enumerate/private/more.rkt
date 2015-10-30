#lang racket/base
(require racket/contract
         racket/function
         racket/generator
         racket/bool
         racket/match
         racket/set
         (only-in racket/list remove-duplicates partition)
         syntax/location
         math/base
         math/distributions
         math/number-theory
         math/flonum
         "../unsafe.rkt"
         (prefix-in core: "../private/core.rkt")
         (for-syntax racket/base))

(provide cons/de
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
         flip-dep/e
         random-index
         infinite-sequence/e
         set/e
         permutations/e
         permutations-of-n/e
         nat+/e
         fold-enum
         range/e
         listof/e
         non-empty-listof/e
         listof-n/e
         take/e
         slice/e
         hash-traverse/e
         cons/e
         vector/e
         single/e
         fin/e
         
         ;; for testing
         BPP-digits
         10-sequence->K-sequence)

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
  (if (infinite-enum? e)
      (random-natural-w/o-limit)
      (random-natural (enum-count e))))

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
  (cond [(= 0 (enum-count inner/e)) empty/e]
        [else
         (define seed/e natural/e)
         (define K (enum-count inner/e))
         (define (seed->seq N)
           (define K-seq
             (10-sequence->K-sequence K (in-generator (BPP-digits (+ 1 N)))))
           (in-generator
            (for ([k K-seq])
              (yield (from-nat inner/e k)))))
         (pam/e seed->seq seed/e #:contract sequence?)]))

#|
Finite set enumeration: use the natural isomorphism between subsets A ⊆ X and X -> {0,1}; i.e. for
all A ⊆ X, there exists an f : X -> {0,1} (and for all f : X -> {0,1} there exists an A ⊆ X) s.t.

  x ∈ A <-> f(x) = 1

An f : X -> {0,1} is called an "indicator function."

If A is finite, then f(x) = 1 for at most finitely many x ∈ X. If X is enumerable, we can encode
any such f as a natural number n ∈ [0,2^|X|). Further, every n ∈ [0,2^|X|) encodes an f that is
isomorphic to a finite A ⊆ X, so the encoding is efficient.

In plain English, we'll
 * Decode by using the bits of n to determine whether each element of X is present.
 * Encode by setting each bit of n to 1 iff its corresponding element of X is present.
|#
(define (set/e e)
  (define needed-nats/e 
    (cond [(infinite-enum? e) natural/e]
          [else
           (take/e natural/e (expt 2 (enum-count e)))]))
  ;; The greatest number with 31 bits is n = 2^31 - 1, for which 2^n takes about 5 seconds
  ;; to compute on my machine. Further, trying to compute 2^(2^32) bombs out with
  ;; "Interactions disabled".
  ;; I have no idea how to make this sensitive to memory limits, nor whether that's even
  ;; desirable.
  (define from-nat-fun (λ (i) (indicator->set e i)))
  (define to-nat-fun   (λ (s) (set->indicator e s)))
  (define set-contract (set/c (enum-contract e)))
  (cond [(two-way-enum? e)
         (map/e 
          from-nat-fun
          to-nat-fun          
          needed-nats/e
          #:contract set-contract)]
        [else 
         (pam/e
          from-nat-fun
          needed-nats/e
          #:contract set-contract)]))

(define (indicator->set e i)
  ;; Limit n to (size e) to try to make up for the fact that set/e might claim to have size +inf.0
  ;; when it actually has finite size
  (define n
    (min (integer-length i)
         (if (finite-enum? e) (enum-count e) +inf.0)))
  (for/fold ([acc  (set)]) ([d  (in-range n)])
    (if (bitwise-bit-set? i d)
        (set-add acc (from-nat e d))
        acc)))

(define (set->indicator e s)
  ;; Another way to do this is loop over the enumeration and remove elements of s as they're
  ;; encountered, stopping when s is empty. It's probably a lot slower, though.
  (for/fold ([i 0]) ([m  (in-set s)])
    ;; Set bit number (to-nat e m) to 1 in i
    (bitwise-ior i (arithmetic-shift 1 (to-nat e m)))))

(define-syntax (cons/de stx)
  (define dep-expression-finite #f)
  (define flat #f)
  (define one-way #f)
  (define (parse-options options)
    (let loop ([options options])
      (syntax-case options ()
        [() (void)]
        [(#:dep-expression-finite? exp . options)
         (begin
           (when dep-expression-finite
             (raise-syntax-error 'cons/de "expected only one use of #:dep-expression-finite?"
                                 stx
                                 dep-expression-finite
                                 (list #'exp)))
           (set! dep-expression-finite #'exp)
           (loop #'options))]
        [(#:flat? exp . options)
         (begin
           (when flat
             (raise-syntax-error 'cons/de "expected only one use of #:flat"
                                 stx
                                 flat
                                 (list #'exp)))
           (set! flat #'exp)
           (loop #'options))]
        [(#:one-way? exp . options)
         (begin
           (when one-way
             (raise-syntax-error 'cons/de "expected only one use of #:one-way"
                                 stx
                                 one-way
                                 (list #'exp)))
           (set! one-way #'exp)
           (loop #'options))]
        [(x . y)
         (let ()
           (when (keyword? (syntax-e #'x))
             (raise-syntax-error 'cons/de "unknown keyword" stx #'x))
         (raise-syntax-error 'cons/de "bad syntax" stx #'x))])))
  (define the-srcloc
    #`(srcloc '#,(syntax-source stx)
              #,(syntax-line stx)
              #,(syntax-column stx)
              #,(syntax-position stx)
              #,(syntax-span stx)))
  (define other-party-name (syntax-local-lift-expression #'(quote-module-name)))
  (syntax-case stx ()
    [(_ [hd e1] [tl (hd2) e2] . options)
     (begin
       (unless (free-identifier=? #'hd #'hd2)
         (raise-syntax-error 'cons/de "expected the identifiers to be the same"
                             stx
                             #'hd
                             (list #'hd2)))
       (parse-options #'options)
       #`(cons/de/proc e1 (λ (hd2) e2) #,dep-expression-finite #,(or flat #'#t)
                       #,(or one-way #''default) #f #,the-srcloc #,other-party-name))]
    [(_ [hd (tl2) e1] [tl e2] . options)
     (begin
       (unless (free-identifier=? #'tl #'tl2)
         (raise-syntax-error 'cons/de "expected the identifiers to be the same"
                             stx
                             #'tl
                             (list #'tl2)))
       (parse-options #'options)
       #`(cons/de/proc e2 (λ (tl2) e1) #,dep-expression-finite #,(or flat #'#t)
                       #,(or one-way #''default) #t #,the-srcloc #,other-party-name))]))
                       
(define (cons/de/proc e _f f-range-finite? flat? _one-way? flip? the-srcloc other-party-name)
  (define one-way? (if (equal? _one-way? 'default)
                       (one-way-enum? e)
                       _one-way?))
  (define f-range-ctc
    (and/c (if f-range-finite?
               finite-enum?
               infinite-enum?)
           (if (two-way-enum? e)
               two-way-enum?
               one-way-enum?)))
  (define (f v)
    (contract f-range-ctc
              (_f v) 
              other-party-name 
              'data/enumerate 
              'cons/de/dependent-expression
              the-srcloc))
  (define forward (core:dep/e-internal e f f-range-finite? flat? one-way?))
  (if flip?
      (flip-it forward e f flat?)
      forward))


(define (flip-dep/e e f
                    #:f-range-finite? [f-range-finite? #f]
                    #:flat? [flat? #t]
                    #:one-way? [one-way? (one-way-enum? e)])
  (flip-it (core:dep/e-internal e f f-range-finite? flat? one-way?) e f flat?))
(define (flip-it to-flip e f flat?)
  (define (flip-pr ab) (cons (cdr ab) (car ab)))
  (map/e
   flip-pr flip-pr 
   to-flip
   #:contract
   (if flat?
       (cons/dc [hd (tl) (enum-contract (f tl))] [tl (enum-contract e)] #:flat)
       (cons/dc [hd (tl) (enum-contract (f tl))] [tl (enum-contract e)]))))

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
      (cons/de
       [v (below/e n)]
       [tl (v)
           (map/e
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
            any/c)]
       #:dep-expression-finite? #t)
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

(define (range/e low high)
  (cond 
    [(and (infinite? high) (infinite? low))
     integer/e]
    [(infinite? high)
     (map/e
      (λ (n)
        (+ n low))
      (λ (n)
        (- n low))
      natural/e
      #:contract (and/c exact-integer? (>=/c low)))]
    [(infinite? low)
     (map/e
      (λ (n) (- high n))
      (λ (n) (- high n))
      natural/e
      #:contract (and/c exact-integer? (<=/c high)))]
    [else
     (map/e (λ (n) (+ n low))
            (λ (n) (- n low))
            (below/e (+ 1 (- high low)))
            #:contract (and/c (between/c low high)
                              exact-integer?))]))

(define (nat+/e n)
  (map/e (λ (k) (+ k n))
         (λ (k) (- k n))
         natural/e
         #:contract
         (and/c (>=/c n) exact-integer?)))





;; fold-enum : ((listof a), b -> enum a), (listof b) -> enum (listof a)
(define (fold-enum f l #:f-range-finite? [f-range-finite? #f])
  (define e
    (let loop ([l l]
               [acc (fin/e '())])
      (cond [(null? l) acc]
            [else
             (loop
              (cdr l)
              (cons/de [hd (xs) (f xs (car l))]
                       [xs acc]
                       #:dep-expression-finite? f-range-finite?))])))
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

(define (listof/e e #:simple-recursive? [simple-recursive? #t])
  (cond
    [simple-recursive?
     (define fix-size
       (if (and (finite-enum? e) (= 0 (enum-count e)))
           1
           +inf.0))
     (define result-e
       (delay/e
        (or/e (cons (fin/e '()) null?)
              (cons (cons/e e result-e) pair?))
        #:count fix-size
        #:two-way-enum? (two-way-enum? e)
        #:flat-enum? (flat-enum? e)))
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
      (cons/de
       [i natural/e]
       [tl (i) (apply list/e (build-list (+ i 1) (λ (_) e)))])
      #:contract (non-empty-listof (enum-contract e)))]))


(define (listof-n/e e n)
  (apply list/e (build-list n (const e))))


(define (take/e e n #:contract [contract 
                                (λ (x)
                                  (and ((enum-contract e) x)
                                       (< (to-nat e x) n)))])
  (slice/e e 0 n))

(define (slice/e e lo hi 
                 #:contract 
                 [contract 
                  (and/c (enum-contract e)
                         (let ([in-the-slice?
                                (λ (x)
                                  (define n (to-nat e x))
                                  (and (<= lo n)
                                       (< n hi)))])
                           in-the-slice?))])
  (map/e
   (λ (n) (from-nat e (n . + . lo)))
   (λ (x) (- (to-nat e x) lo))
   (below/e (hi . - . lo))
   #:contract contract))


;; Hash Traversal
;; hash-traverse/e : (a -> enum b), (hash[k] -o> a) -> enum (hash[k] -o> b)
(define (hash-traverse/e f ht #:get-contract get-contract)
  ;; as-list : listof (cons k a)
  (define as-list (hash->list ht))
  ;; on-cdr : (cons k a) -> enum (cons k b)
  (define/match (on-cdr pr)
    [((cons k v))
     (map/e (λ (x) (cons k x))
            cdr
            (f v)
            #:contract any/c)])
  ;; enum (listof (cons k b))
  (define assoc/e
    (apply list/e (map on-cdr as-list)))
  (define (hash-that-maps-correct-keys? x) #t)
  (map/e make-immutable-hash
         hash->list
         assoc/e
         #:contract (and/c
                     hash?
                     hash-that-maps-correct-keys?
                     (hash/dc [k any/c]
                              [v (k) (get-contract k)]))))



;; cons/e : enum a, enum b ... -> enum (cons a b ...)
(define (cons/e e1 e2 #:ordering [ordering 'square])
  (map/e (λ (x) (cons (car x) (cadr x)))
         (λ (x-y) (list (car x-y) (cdr x-y)))
         (list/e e1 e2 #:ordering ordering)
         #:contract (cons/c (enum-contract e1) (enum-contract e2))))


(define-syntax (delay/e stx)
  (syntax-case stx ()
    [(_ expr . kwd-args)
     (let ()
       (when (keyword? (syntax-e #'expr))
         (raise-syntax-error 'delay/e 
                             "expected an expression argument first, not a keyword"
                             stx #'expr))
       (define other-party-name (syntax-local-lift-expression #'(quote-module-name)))
       (define the-srcloc
         #`(srcloc '#,(syntax-source stx)
                   #,(syntax-line stx)
                   #,(syntax-column stx)
                   #,(syntax-position stx)
                   #,(syntax-span stx)))
       #`((delay/e/proc #,other-party-name #,the-srcloc (λ () expr)) . kwd-args))]))

(define (delay/e/proc other-party-name the-srcloc thunk)
  ;; do this curried thing to get better error reporting for keyword arity errors
  (define (delay/e #:count [count +inf.0]
                   #:two-way-enum? [is-two-way-enum? #t]
                   #:flat-enum? [is-flat-enum? #t])
    
    (define ctc
      (and/c (if (= count +inf.0)
                 infinite-enum?
                 (and/c finite-enum?
                        (let ([matching-count? (λ (e) (= (enum-count e) count))])
                          matching-count?)))
             (if is-two-way-enum?
                 two-way-enum?
                 one-way-enum?)
             (if is-flat-enum?
                 flat-enum?
                 (not/c flat-enum?))))
    (unless (or (exact-nonnegative-integer? count)
                (and (number? count) (= count +inf.0)))
      (raise-argument-error 'delay/e 
                            (format "~s" '(or/c exact-nonnegative-integer? +inf.0))
                            count))
    (thunk/e (λ () (contract ctc
                             (thunk)
                             other-party-name 
                             'data/enumerate/lib 
                             'delay/e-expression
                             the-srcloc))
              #:count count
              #:two-way-enum? is-two-way-enum?
              #:flat-enum? is-flat-enum?))
  delay/e)

(define two-way-arg?
  (or/c symbol? boolean? char? keyword? null?
        string? bytes? number?))

(define (fin/e . args)
  (cond
    [(null? args) empty/e]
    [else
     (define vec (list->vector args))
     (define (use-=? x) (and (number? x) (not (memv x '(+nan.0 +nan.f)))))
     (define-values (use-= use-equal?) (partition use-=? args))
     (cond
       [(andmap two-way-arg? args)
        (define rev-map (make-hash))
        (define num-rev-map (list))
        (for ([i (in-naturals)]
              [x (in-list args)])
          (cond
            [(use-=? x)
             (set! num-rev-map (cons (cons x i) num-rev-map))]
            [else
             (hash-set! rev-map x i)]))
        (set! num-rev-map (reverse num-rev-map))
        (map/e (λ (n) (vector-ref vec n))
               (λ (x)
                 (cond
                   [(use-=? x)
                    (for/first ([pr (in-list num-rev-map)]
                                #:when (= x (car pr)))
                      (cdr pr))]
                   [else (hash-ref rev-map x)]))
               (below/e (vector-length vec))
               #:contract (apply or/c args))]
    [else
     (define (fin/e-argument? x)
       (cond
         [(number? x)
          (ormap (λ (y) (= x y)) use-=)]
         [else
          (ormap (λ (y) (equal? x y)) use-equal?)]))
     (pam/e #:contract fin/e-argument?
            (λ (n) (vector-ref vec n))
            (below/e (vector-length vec)))])]))


;; Base Type enumerators



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
   (append/e low/e-p
             up/e-p
             bottom/e-p
             mid/e-p
             above1/e-p
             above2/e-p)
   #:contract char?))

(define better-ordering-for-sequences-of-chars/e
  (append/e (list/e char/e)
            (fin/e '())
            (cons/e char/e (cons/e char/e (listof/e char/e)))))

(define string/e
  (map/e
   list->string
   string->list
   better-ordering-for-sequences-of-chars/e
   #:contract string?))

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
           natural/e
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

(define flonum/e
  (append/e (fin/e +inf.0 -inf.0 +nan.0)
            normal-flonums/e-p))

(define exact-rational/e
  (or/e (fin/e 0)
        (let ([pos-exact-rational/e
               (pam/e (λ (pr) (/ (car pr) (cdr pr)))
                      (cons/e (nat+/e 1) (nat+/e 2))
                      #:contract (and/c rational? positive?))])
          (or/e pos-exact-rational/e
                (pam/e - pos-exact-rational/e
                       #:contract (and/c rational? exact? negative?))))))
         
(define two-way-real/e (or/e integer/e flonum/e))
(define real/e (or/e flonum/e exact-rational/e))

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
  (make-non-real/e (except/e integer/e 0) (except/e integer/e 0)
                   (and/c complex-with-exact-integer-parts? (not/c real?))))

(define (real-part-inexact? x) (inexact? (real-part x)))
(define float-non-real/e 
  (make-non-real/e flonum/e flonum/e
                   (and/c number?
                          inexact?
                          (not/c real?)
                          real-part-inexact?)))

;; only one-way, so don't need to skip 0
(define exact-rational-complex/e 
  (make-non-real/e exact-rational/e exact-rational/e
                   (and/c number? exact?)))

(define number/e
   (or/e real/e
         float-non-real/e
         exact-rational-complex/e))
(define (complex-with-exact-zero-real-part? x)
  (and (number? x)
       (equal? 0 (real-part x))))

(define (not-equal-to-0? x) (not (equal? x 0)))
(define two-way-number/e
  (or/e (except/e two-way-real/e 0
                  #:contract
                  (and/c not-equal-to-0? (enum-contract two-way-real/e)))
        (map/e (λ (x) (make-rectangular 0 x)) 
               imag-part
               two-way-real/e 
               #:contract complex-with-exact-zero-real-part?)
        float-non-real/e))

(define bool/e (fin/e #t #f))

(define symbol/e
  (map/e
   (compose string->symbol list->string)
   (compose string->list symbol->string)
   better-ordering-for-sequences-of-chars/e
   #:contract symbol?))



(define (vector/e #:ordering [ordering 'square] . es)
  (map/e list->vector
         vector->list
         (apply list/e #:ordering ordering es)
         #:contract
         (apply vector/c
                (map enum-contract es)
                #:flat? (andmap flat-enum? es))))

(define (single/e v #:equal? [_same? #f])
  (define same? (or _same? equal?))
  (define single/e-contract
    (cond
      [(and (not _same?)
            (contractable? v))
       (to-contract v)]
      [else
       (λ (a) (same? v a))]))
  (map/e (λ (_) v)
         (λ (_) 0)
         (below/e 1)
         #:contract single/e-contract))

(define (contractable? v)
  (cond
    [(contract? v) #t]
    [(pair? v) (and (contractable? (car v))
                    (contractable? (cdr v)))]
    [else #f]))

(define (to-contract v)
  (cond
    [(pair? v) (cons/c (to-contract (car v))
                       (to-contract (cdr v)))]
    [else v]))
