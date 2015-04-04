#lang racket/base
(require racket/contract
         racket/function
         racket/list
         racket/math
         racket/match
         racket/promise
         syntax/location
         data/gvector
         (only-in math/number-theory
                  binomial
                  integer-root
                  factorize))

(module+ test (require rackunit))

#|

changes:
 - add contracts to enumeration values
 - allow only finite-enum? for enum-count
 - map/e gets a #:contract argument (other ones?)
 - added one-way enumerations (as opposed to bijective)
 - added flat-enum? predicate

todo:
 - criterion for "less checked": avoid all checks that call from-nat/to-nat
 - coerce valid `fin/e` arguments as singleton enumerations (except #f)
 - provide false/e (from data/enumerate/lib)
 - document unsafe properly 
    => export the parameter that disables the fancy contract checks
       from data/enumerate/unsafe

|#

(provide 
 enum?
 enum-count
 from-nat
 to-nat
 enum-contract
 in-enum
 map/e
 pam/e
 except/e
 enum->list
 below/e
 empty/e
 natural/e
 or/e
 append/e
 fin-cons/e
 dep/e
 dep/e-internal
 dep/e-contract
 thunk/e
 list/e
 cantor-list/e
 box-list/e
 prime-length-box-list/e
 bounded-list/e
 box-tuples/e
 below/e
 
 give-up-escape
 
 two-way-enum?
 one-way-enum? 
 flat-enum?
 finite-enum?
 infinite-enum?)


(define give-up-escape (make-parameter #f))
(define (give-up-on-bijection-checking promise)
  (unless (promise-forced? promise)
    (define esc (give-up-escape))
    (when esc (esc))))

(define (enum-write-proc enum port mode)
  (define recur
    (case mode
      [(#t) write]
      [(#f) display]
      [else (lambda (p port) (print p port mode))]))
  (display "#<" port)
  (define the-size (enum-count enum))
  (cond [(infinite-enum? enum) 
         (display "infinite-" port)]
        [(zero? the-size) 
         (display "empty-" port)]
        [(the-size . < . 100000000) ;; arbitrary cutoff to not print giant sizes
         (display the-size port)
         (display "-count-" port)]
        [else
         (display "finite-" port)])
  (when (one-way-enum? enum) (display "one-way-" port))
  (display "enum" port)
  (define more-to-go?
    (cond
      [(zero? the-size) #f]
      [else
       (let/ec failed
         (parameterize ([enum-printing (+ 1 (enum-printing))])
           (let loop ([i 0] [chars 0])
             ;; chars is an approximation on how much
             ;; we've printed so far.
             (cond
               [(not (< i the-size)) #f]
               [(> (enum-printing) 10)
                ;; we appear to be in some kind of a bad loop here; just give up
                #f]
               [(<= chars 20)
                (define ele 
                  ;; if something goes wrong while trying to extract
                  ;; an element, just give up (since we could very
                  ;; well be trying to print an error message here!)
                  (with-handlers ([exn:fail? (λ (x) (failed #t))])
                    (from-nat enum i)))
                (define sp (open-output-string))
                (recur ele sp)
                (define s (get-output-string sp))
                (cond
                  [(equal? s "")
                   ;; if any enumeration values print as empty 
                   ;; strings, then we just give up so as to avoid
                   ;; 'i' never incrementing and never terminating
                   #t]
                  [else
                   (if (zero? i)
                       (display ": " port)
                       (display " " port))
                   
                   ;; only print twice up to depth 2 in order to avoid bad
                   ;; algorithmic behavior (so enumerations of enumerations
                   ;; of enumerations might look less beautiful in drracket)
                   (cond
                     [(<= (enum-printing) 2)
                      (display s port)]
                     [else
                      (recur ele port)])
                   
                   (loop (+ i 1)
                         (+ chars (string-length s) 1))])]
               [else #t]))))]))
  (if more-to-go?
      (display "...>" port)
      (display ">" port)))
(define enum-printing (make-parameter 0))

(define (two-way-enum? x) (and (enum? x) (enum-to x) #t))
(define (one-way-enum? x) (and (enum? x) (not (enum-to x))))
(define (flat-enum? e) (and (enum? e) (flat-contract? (enum-contract e))))
(define (finite-enum? e) (and (enum? e) (not (infinite? (enum-count e)))))
(define (infinite-enum? e) (and (enum? e) (infinite? (enum-count e))))

(define (from-nat e n) ((enum-from e) n))
(define (to-nat e a) ((enum-to e) a))
(define (enum-contract e) (enum-ctc e))

;; helper to find arity errors at compile time
(require (for-syntax racket/base))
(define-syntax (-enum stx)
  (syntax-case stx ()
    [(_ a b c d) #'(enum a b c d)]))

(define in-enum/proc
  (let ([in-enum
         (λ (enum)
           (check-sequence-enum enum)
           (cond
             [(finite-enum? enum)
              (define size (enum-count enum))
              (make-do-sequence
               (λ ()
                 (values 
                  (λ (pos) (from-nat enum pos))
                  add1
                  0
                  (λ (pos) (< pos size))
                  #f #f)))]
             [else
              (make-do-sequence
               (λ ()
                 (values 
                  (λ (pos) (from-nat enum pos))
                  add1
                  0
                  (λ (pos) #t)
                  #f #f)))]))])
    in-enum))

(define (check-sequence-enum enum)
  (unless (enum? enum)
    (raise-argument-error 'in-enum "enum?" enum)))

(define-sequence-syntax in-enum
  (λ () #'in-enum/proc)
  (λ (stx)
    (syntax-case stx ()
      [[(enum-val) (_ enum)]
       #'[(id) (:do-in ([(e the-size) 
                         (let ([e enum])
                           (values e
                                   (if (finite-enum? enum)
                                       (enum-count enum)
                                       +inf.0)))])
                       (check-sequence-enum e)
                       ([index 0])
                       (< index the-size)
                       ([(enum-val) (from-nat e index)])
                       #t #t 
                       [(add1 index)])]]
      [_ #f])))

;; an enum a is a struct of < Nat or +Inf, Nat -> a, a -> Nat >
(struct enum (count from to ctc)
  #:methods gen:custom-write
  [(define write-proc enum-write-proc)]
  #:property prop:sequence in-enum/proc)

(define (map/e #:contract [ctc any/c] f inv-f e . es)
  (cond 
    [(or (one-way-enum? e) (ormap one-way-enum? es))
     (apply pam/e #:contract ctc f e es)]
    [else
     (define (map1/e f inv-f e)
       (define e-from (enum-from e))
       (define e-to (enum-to e))
       (-enum (enum-count e)
              (λ (x) 
                (f (e-from x)))
              (λ (n)
                (e-to (inv-f n)))
              ctc))
     (cond
       [(empty? es) (map1/e f inv-f e)]
       [else
        (map1/e
         (λ (xs)
           (apply f xs))
         (λ (ys)
           (call-with-values (λ () (inv-f ys)) list))   
         (apply list/e (cons e es)))])]))

(define (pam/e #:contract ctc f e . es)
  (define (pam1/e f e)
    (-enum (enum-count e)
           (λ (x) (f (from-nat e x)))
           #f
           ctc))
  (cond 
    [(empty? es) (pam1/e f e)]
    [else
     (pam1/e
      (λ (xs) (apply f xs))   
      (apply list/e (cons e es)))]))

(define (except/e e #:contract [_contract #f] . excepts)
  (define contract
    (cond
      [_contract _contract]
      [else
       (define orig-ctc (enum-contract e))
       (cond
         [(flat-contract? orig-ctc)
          (define (an-excepted-value? x) (member x excepts))
          (and/c (not/c an-excepted-value?)
                 orig-ctc)]
         [else
          (error 'expect/e
                 (string-append
                  "expected an explicit #:contract argument" 
                  " or a flat contract on the enumerator argument"))])]))
  (define (except1/e x e)
    (cond [(= (enum-count e) 0) e]
          [else
           (define xi (to-nat e x))
           (define (from-nat2 n)
             (cond [(< n xi) (from-nat e n)]
                   [else (from-nat e (add1 n))]))
           (define (to-nat2 y)
             (define yi (to-nat e y))
             (cond [(< yi xi) yi]
                   [(> yi xi) (sub1 yi)]
                   [else (error 'except/e "attempted to encode an excepted value")]))
           (-enum (max 0 (sub1 (enum-count e))) from-nat2 to-nat2 any/c)]))
  (define w/wrong-contract
    (foldr except1/e
           e
           excepts))
  (-enum (enum-count w/wrong-contract)
         (enum-from w/wrong-contract)
         (enum-to w/wrong-contract)
         contract))

(define (enum->list e [n (enum-count e)])
  (for/list ([i (in-range n)])
    (from-nat e i)))

(define (below/e n)
  (-enum n values values (integer-in 0 (- n 1))))

(define empty/e
  (-enum 0
         void
         (λ (x)
           (error 'to-nat "no elements in the enumerator"))
         none/c))

(define natural/e (-enum +inf.0 values values exact-nonnegative-integer?))

(define (empty/e? e)
  (= 0 (enum-count e)))

(define (exact-min . xs)
  (define (exact-min-2 x y)
    (if (x . <= . y)
        x
        y))
  (foldl exact-min-2 +inf.0 xs))

(struct fin-layer
  (bound  ;; nat
   enums) ;; Vectorof (Enum a, list-index)
  #:transparent)

(struct upper-bound
  (total-bound      ;; Nat
   individual-bound ;; Nat
   enumerators      ;; Vectorof (Enum a, Nat)
   )
  #:transparent)

(struct list-layer
   ;; Nat = layer-size + prev-layer-max-index: This is the maximum index into decode for this layer
  (max-index
   ;; Nat, = min (map size inexhausteds): This is the maximum index in the tuple for encode
   inexhausted-bound
   exhausteds   ;; Vectorof (Enum a, Nat)
   inexhausteds ;; Vectorof (Enum a, Nat)
   )
  #:transparent)

(define (mk-fin-layers es)
  (define (loop eis prev)
    (define non-emptys (filter (negate (compose empty/e? car)) eis))
    (match non-emptys
      ['() '()]
      [_
       (define min-size
         (apply exact-min (map (compose enum-count car) non-emptys)))
       (define (not-min-size? e)
         (not (= (enum-count (car e)) min-size)))
       (define leftover
         (filter not-min-size? non-emptys))
       (define veis
         (apply vector non-emptys))
       (define cur-layer (fin-layer min-size veis))
       (define remaining-layers
         (loop leftover cur-layer))
       (cons cur-layer
             remaining-layers)]))
  (define eis
    (for/list [(i (in-naturals))
               (e (in-list es))]
      (cons e i)))
  (loop eis (fin-layer 0 eis)))

;; layers : Listof Enum -> Listof Upper-Bound
(define (disj-sum-layers es)
  (define fin-layers (mk-fin-layers es))
  (define (loop fin-layers prev)
    (match fin-layers
      ['() '()]
      [(cons (fin-layer cur-bound eis) rest-fin-layers)
       (match-define (upper-bound prev-tb
                                  prev-ib
                                  _)
                     prev)
       (define min-size cur-bound)
       (define diff-min-size
         (min-size . - . prev-ib))
       (define total-bound
         (prev-tb . + . (diff-min-size . * . (vector-length eis))))
       (define cur-layer
         (upper-bound total-bound
                      cur-bound
                      eis))
       (define rest-layers (loop rest-fin-layers cur-layer))
       (cons cur-layer
             rest-layers)]))
  (define eis
    (for/list [(i (in-naturals))
               (e (in-list es))]
      (cons e i)))
  (apply vector (loop fin-layers (upper-bound 0 0 eis))))

(define (mk-list-layers es)
  (define eis
    (for/list [(i (in-naturals))
               (e (in-list es))]
      (cons e i)))
  (define (loop fin-layers prev-layer)
    (match fin-layers
      ['() '()]
      [(cons (fin-layer cur-bound vec-cur-inexhausteds) rest-fins)
       (match-define (list-layer prev-max-index
                                 prev-bound
                                 prev-exhausteds
                                 prev-inexhausteds)
                     prev-layer)
       (define cur-inexhausteds (vector->list vec-cur-inexhausteds))
       (define cur-exhausteds
         (append (remove* cur-inexhausteds prev-inexhausteds)
                 prev-exhausteds))
       (define num-inexhausted
         (length cur-inexhausteds))
       (define max-index
         (prev-max-index
          . + . 
          (apply *
                 ((expt cur-bound num-inexhausted) . - . (expt prev-bound num-inexhausted))
                 (map (compose enum-count car) cur-exhausteds))))
       (define cur-layer
         (list-layer max-index
                     cur-bound
                     cur-exhausteds
                     cur-inexhausteds))
       (define rest-layers (loop rest-fins cur-layer))
       (cons cur-layer rest-layers)]))
  (loop (mk-fin-layers es)
        (list-layer 0 0 '() eis)))

;; find-dec-layer : Nat, Nonempty-Listof Upper-bound -> Upper-bound, Upper-bound
;; Given an index, find the first layer 
(define (find-dec-layer i layers)
  (find-layer-by-size i
                      upper-bound-total-bound
                      (upper-bound 0 0 (vector))
                      layers))

(define (find-index x e-ps [cur-index 0])
  (match e-ps
    ['() (error 'to-nat "invalid term")]
    [(cons (cons e in-e?)
           more-e-ps)
     (cond [(in-e? x)
            (values (to-nat e x)
                    cur-index)]
           [else
            (find-index x more-e-ps (add1 cur-index))])]))

(define (find-enc-layer i e-i layers)
  (define-values (prev cur)
    (find-layer-by-size i
                        upper-bound-individual-bound
                        (upper-bound 0 0 (vector))
                        layers))
  (define/match (find-e-index l e-i)
    [((upper-bound tb ib eis) e-i)
     (define (loop low hi)
       (when (> low hi)
         (error 'to-nat "internal bin search bug"))
       (define mid
         (quotient (low . + . hi) 2))
       (define cur
         (cdr (vector-ref eis mid)))
       (cond [(low . = . mid)
              (unless (cur . = . e-i)
                (error 'to-nat "internal binary search bug"))
              mid]
             [(cur . = . e-i) mid]
             [(cur . < . e-i) (loop (add1 mid) hi)]
             [else            (loop low mid)]))
     (loop 0 (vector-length eis))])
  (values prev
          cur
          (find-e-index cur e-i)))

(define (find-layer-by-size i get-size zeroth ls)
  ;; Find the lowest indexed elt that is still greater than i
  (define (loop lo hi)
    (define mid (quotient (lo . + . hi) 2))
    (define cur (get-size (vector-ref ls mid)))
    (cond [(i  . = . cur) (add1 mid)]
          [(i  . > . cur) (loop (add1 mid) hi)]
          [(lo . = . mid) lo]
          [else           (loop lo         mid)]))
  (define n (loop 0 (vector-length ls)))
  (define prev
    (cond [(n . > . 0) (vector-ref ls (sub1 n))]
          [else        zeroth]))
  (values prev (vector-ref ls n)))

(define (find-list-dec-layer layers n eis)
  (define-values (prev cur)
    (find-layer-by-size n
                        list-layer-max-index
                        (list-layer 0 0 '() eis)
                        (list->vector layers)))
  (match-define (list-layer prev-max-index _ _ _) prev)
  (match-define (list-layer _  tuple-bound exhs inexhs) prev)
  (values prev-max-index tuple-bound exhs inexhs))

;; fairly interleave a list of enumerations
(define (or/e #:one-way-enum? [one-way-enum? #f] . e-or-e/ps)
  (define e-ps (for/list ([x (in-list e-or-e/ps)])
                 (cond
                   [(enum? x) (cons x (enum-contract x))]
                   [else x])))
  (define (non-empty-e-p? e-p)
    (not (= 0 (enum-count (car e-p)))))
  (match (filter non-empty-e-p? e-ps)
    ['() empty/e]
    [`(,e-p) (car e-p)]
    [non-empty-e-ps
     (define layers
       (disj-sum-layers (map car non-empty-e-ps)))
     (define (dec i)
       (define-values (prev-up-bound cur-up-bound)
         (find-dec-layer i layers))
       (match-define (upper-bound so-far prev-ib _)  prev-up-bound)
       (match-define (upper-bound ctb    cib     es) cur-up-bound)
       (define this-i (i . - . so-far))
       (define len (vector-length es))
       (define-values (q r) (quotient/remainder this-i len))
       (define this-e (car (vector-ref es r))) 
       (from-nat this-e (+ q prev-ib)))
     (define enc
       (and (not one-way-enum?)
            (andmap (λ (x) (two-way-enum? (car x))) e-ps)
            (λ (x)
              (define-values (index which-e)
                (find-index x non-empty-e-ps))
              (define-values (prev-up-bound cur-up-bound cur-e-index)
                (find-enc-layer index which-e layers))
              (match-define (upper-bound ptb pib pes) prev-up-bound)
              (match-define (upper-bound ctb cib ces) cur-up-bound)
              (+ ptb
                 cur-e-index
                 ((vector-length ces) . * . (index . - . pib))))))
     (-enum (apply + (map (compose enum-count car) non-empty-e-ps))
            dec
            enc
            (apply or/c (map (λ (x) (enum-contract (car x))) non-empty-e-ps)))]))

;; Like or/e, but sequences the enumerations instead of interleaving
(define (append/e e-p #:one-way-enum? [one-way-enum? #f] . e-ps)
  (define/match (disj-append2/e e-p1 e-p2)
    [((cons e1 1?) (cons e2 2?))
     (define s1 (enum-count e1))
     (define s2 (enum-count e2))
     (when (infinite? s1)
       (error 'disj-append/e "only the last enum argument to disj-append/e may be infinite"))
     (define (from-nat2 n)
       (cond [(< n s1) (from-nat e1 n)]
             [else (from-nat e2 (- n s1))]))
     (define to-nat2
       (and (not one-way-enum?)
            (two-way-enum? e1)
            (two-way-enum? e2)
            (λ (x)
              (cond [(1? x) (to-nat e1 x)]
                    [(2? x) (+ (to-nat e2 x) s1)]
                    [else (error 'to-nat "bad term")]))))
     (-enum (+ s1 s2) from-nat2 to-nat2 
            (or/c (enum-contract e1)
                  (enum-contract e2)))])
  (define all-eps
    (for/list ([eps (in-list (cons e-p e-ps))])
      (if (pair? eps)
          eps
          (cons eps (enum-contract eps)))))
  (car
   (foldr1 (λ (e-p1 e-p2)
             (match* (e-p1 e-p2)
                     [((cons e1 1?) (cons e2 2?))
                      (cons (disj-append2/e e-p1
                                            (cons e2 (negate 1?)))
                            (λ (x)
                               (or (1? x)
                                   (2? x))))]))
           all-eps)))

(define (foldr1 f l)
  (match l
    [(cons x '()) x]
    [(cons x  xs) (f x (foldr1 f xs))]))

(define (fin-cons/e e1 e2)
  (unless (finite-enum? e1)
    (raise-argument-error 'fin-cons/e
                          "finite-enum?"
                          0
                          e1 e2))
  (unless (finite-enum? e2)
    (raise-argument-error 'fin-cons/e
                          "finite-enum?"
                          1
                          e1 e2))
  (define s1 (enum-count e1))
  (define s2 (enum-count e2))
  (define the-size (* s1 s2))
  (cond [(zero? the-size) empty/e]
        [else
         (define-values (fst-smaller? min-size)
           (cond [(s1 . <= . s2) (values #t s1)]
                 [else          (values #f s2)]))
         (define (dec n)
           (define-values (q r)
             (quotient/remainder n min-size))
           (define-values (n1 n2)
             (if fst-smaller?
                 (values r q)
                 (values q r)))
           (cons (from-nat e1 n1)
                 (from-nat e2 n2)))
         (define enc 
           (and (two-way-enum? e1)
                (two-way-enum? e2)
                (λ (p)
                  (match p
                    [(cons x1 x2)
                     (define n1 (to-nat e1 x1))
                     (define n2 (to-nat e2 x2))
                     (define-values (q r)
                       (if fst-smaller?
                           (values n2 n1)
                           (values n1 n2)))
                     (+ (* min-size q)
                        r)]))))
         (-enum the-size dec enc
                (cons/c (enum-contract e1) (enum-contract e2)))]))

;; the nth triangle number
(define (tri n)
  (/ (* n (+ n 1))
     2))

;; the floor of the inverse of tri
;; returns the largest triangle number less than k
;; always returns an integer
(define (floor-untri k)
  (let ([n (integer-sqrt (+ 1 (* 8 k)))])
    (/ (- n 
          (if (even? n)
              2
              1))
       2)))

(define (dep/e e f
               #:f-range-finite? [f-range-finite? #f]
               #:flat? [flat? #t]
               #:one-way? [one-way? (one-way-enum? e)])
  (dep/e-internal e f f-range-finite? flat? one-way?))

(define (dep/e-internal e f f-range-finite? flat? one-way?)
  (define the-ctc
    (if flat?
        (cons/dc [hd (enum-contract e)] [tl (hd) (enum-contract (f hd))] #:flat)
        (cons/dc [hd (enum-contract e)] [tl (hd) (enum-contract (f hd))])))
  (cond
    [(= 0 (enum-count e)) empty/e]
    [f-range-finite?
     (cons/de-dependent-ranges-all-finite e f the-ctc one-way?)]
    [(finite-enum? e)
     (-enum +inf.0
            (λ (n)
              (define-values (q r) (quotient/remainder n (enum-count e)))
              (cons (from-nat e r)
                    (from-nat (f (from-nat e r)) q)))
            (and (not one-way?)
                 (λ (ab)
                   (+ (* (enum-count e) (to-nat (f (car ab)) (cdr ab)))
                      (to-nat e (car ab)))))
            the-ctc)]
    [else ;; both infinite, same as cons/e
     (define 2nums->num (box-tuple 2))
     (define num->2nums (box-untuple 2))
     (-enum +inf.0               
            (λ (n)
              (define 2nums (num->2nums n))
              (define a (from-nat e (car 2nums)))
              (cons a
                    (from-nat (f a) (cadr 2nums))))
            (and (not one-way?)
                 (λ (xs) ;; bijection from nxn -> n, inverse of previous
                   ;; (n,m) -> (n+m)(n+m+1)/2 + n
                   (unless (pair? xs)
                     (error 'dep2/e "not a pair"))
                   (let ([l (to-nat e (car xs))]
                         [m (to-nat (f (car xs)) (cdr xs))])
                     (2nums->num (list l m)))))
            the-ctc)]))

(define dep/e-contract
  (->i ([e (flat?) (if (or (unsupplied-arg? flat?) flat?)
                       flat-enum?
                       (not/c flat-enum?))]
        [f (e f-range-finite? flat? one-way?)
           (-> (enum-contract e)
               (and/c (if (or (unsupplied-arg? f-range-finite?)
                              (not f-range-finite?))
                          infinite-enum?
                          finite-enum?)
                      (cond
                        [(unsupplied-arg? one-way?)
                         (if (one-way-enum? e)
                             one-way-enum?
                             two-way-enum?)]
                        [else
                         (if one-way?
                             one-way-enum?
                             two-way-enum?)])
                      (if (or (unsupplied-arg? flat?) flat?)
                          flat-enum?
                          (not/c flat-enum?))))])
       (#:f-range-finite? 
        [f-range-finite? boolean?]
        #:flat? [flat? boolean?]
        #:one-way? [one-way? boolean?])
       [res enum?]))

(define (cons/de-dependent-ranges-all-finite e f the-ctc one-way?)
  ;; 'sizes' is a memo table that caches the size of the dependent enumerators
  ;; sizes[n] = # of terms with left side index <= n
  ;; sizes : gvector int
  (define sizes (gvector (enum-count (f (from-nat e 0)))))
  (define (search-size sizes n)
    (when (zero? (gvector-count sizes))
      (gvector-add! sizes (enum-count (f (from-nat e 0)))))
    (define (loop cur)
      (let* ([lastSize (gvector-ref sizes (- cur 1))]
             [e2 (f (from-nat e cur))]
             [s  (+ lastSize (enum-count e2))])
        (gvector-add! sizes s)
        (if (> s n)
            cur
            (loop (+ cur 1)))))
    (loop (gvector-count sizes)))
  ;; fill-table - find sizes[n], filling the table as it goes
  ;; assumption: n >= (gvector-count sizes)
  (define (fill-table sizes n)
    (let loop ([cur (gvector-count sizes)])
      (let* ([prevSize (gvector-ref sizes (- cur 1))]
             [curE (f (from-nat e cur))]
             [s (+ prevSize (enum-count curE))])
        (gvector-add! sizes s)
        (if (= cur n)
            s
            (loop (+ cur 1))))))
  
  (define the-enum-count
    (if (infinite? (enum-count e))
        +inf.0
        (foldl
         (λ (curSize acc)
           (let ([sum (+ curSize acc)])
             (gvector-add! sizes sum)
             sum))
         (gvector-ref sizes 0)
         (map (compose enum-count f) (cdr (enum->list e (enum-count e)))))))
  
  (-enum the-enum-count
         (λ (n)
           (let* ([ind (or (find-size sizes n)
                           (search-size sizes n))]
                  [l (if (= ind 0)
                         0
                         (gvector-ref sizes (- ind 1)))]
                  [m (- n l)]
                  [x (from-nat e ind)]
                  [e2 (f x)]
                  [y (from-nat e2 m)])
             (cons x y)))
         (and (not one-way?)
              (λ (ab)
                (let* ([a (car ab)]
                       [b (cdr ab)]
                       [ai (to-nat e a)]
                       [ei (f a)]
                       [nextSize (enum-count ei)]
                       [sizeUpTo (if (= ai 0)
                                     0
                                     (or (gvector-ref sizes (- ai 1) #f)
                                         (let ([sizeUp
                                                (fill-table sizes (- ai 1))])
                                           (begin0
                                             sizeUp
                                             (gvector-add! sizes
                                                           (+ nextSize
                                                              sizeUp))))))])
                  (+ sizeUpTo
                     (to-nat ei b)))))
         the-ctc))
  

;; find-size : gvector int, int -> either int #f
;; binary search for the index of the smallest element of vec greater
;; than n or #f if no such element exists
(define (find-size vec n)
  (define (bin-search min max)
    (cond [(= min max) min]
          [(= (- max min) 1)
           (cond [(> (gvector-ref vec min) n)
                  min]
                 [else max])]
          [else
           (let ([mid (quotient (+ max min)
                                2)])
             (cond [(> (gvector-ref vec mid) n)
                    (bin-search min mid)]
                   [else
                    (bin-search mid max)]))]))
  (let ([size (gvector-count vec)])
    (cond [(or (= size 0)
               (<= (gvector-ref vec (- size 1))
                   n))
           #f]
          [else (bin-search 0 (- size 1))])))
(module+ test
  (check-equal? (find-size (gvector) 5) #f)
  (check-equal? (find-size (gvector 5) 4) 0)
  (check-equal? (find-size (gvector 1 5 7) 0) 0)
  (check-equal? (find-size (gvector 1 5 7) 1) 1)
  (check-equal? (find-size (gvector 1 5 7) 4) 1)
  (check-equal? (find-size (gvector 1 5 7) 5) 2)
  (check-equal? (find-size (gvector 1 5 7) 6) 2)
  (check-equal? (find-size (gvector 1 5 7) 7) #f))


;; thunk/e : Nat or +-Inf, ( -> enum a) -> enum a
(define (thunk/e thunk
                 #:count [count +inf.0]
                 #:two-way-enum? [two-way? #t]
                 #:flat-enum? [flat-enum? #t])
  (define promise/e (delay (thunk)))
  (-enum count
         (λ (n)
           (give-up-on-bijection-checking promise/e)
           (from-nat (force promise/e) n))
         (and two-way?
              (λ (x)
                (give-up-on-bijection-checking promise/e)
                (to-nat (force promise/e) x)))
         (if flat-enum?
             (recursive-contract
              (enum-contract
               (force promise/e))
              #:flat)
             (recursive-contract
              (enum-contract
               (force promise/e))))))

(define (cantor-untuple k)
  ;; Paul Tarau Deriving a Fast Inverse of the Generalized Cantor N-tupling Bijection
  (λ (n)
     (inc-set->list (combinatorial-number-decode k n))))

(define (combinatorial-number-decode k n)
  (define (loop k n acc)
    (cond [(k . < . 0) (error 'combinatorial-number-decode-bug)]
          [(k . = . 0) acc]
          [else
           (define k2 (sub1 k))
           (define i  (k . + . n))
           (define d
             (let/ec kont
               (for ([j (in-range k2 (add1 i))])
                 (define b (binomial j k))
                 (when (b . > . n)
                   (kont (sub1 j))))
               (error 'ididntfindit)))
           (define n2 (n . - . (binomial d k)))
           (loop k2 n2 (cons d acc))]))
  (loop k n '()))

(define (cantor-tuple k)
  (λ (xs)
     (unless ((length xs) . = . k)
       (error 'cantor-tuple "bad-length-cantor-tuple"))
     ;; Section 6 of Tarau Cantor n-tupling inverse
     (define sums
       (list->inc-set xs))
     (for/sum ([sum_i (in-list sums)]
               [n     (in-naturals)])
       (binomial sum_i (add1 n)))))

(define (list->inc-set xs)
  (define (loop xs count acc)
    (match xs
      ['() (reverse acc)]
      [(cons hd tl)
       (define acc-hd
         (+ hd count 1))
       (loop tl
             acc-hd
             (cons acc-hd acc))]))
  (loop xs -1 '()))

(define (inc-set->list xs)
  (define (loop xs count acc)
    (match xs
      ['() (reverse acc)]
      [(cons hd tl)
       (define acc-hd
         (- hd count 1))
       (loop tl
             hd
             (cons acc-hd acc))]))
  (loop xs -1 '()))

(module+ test
  (check-equal? (list->inc-set '(2 0 1 2)) '(2 3 5 8))
  (check-equal? (inc-set->list '(2 3 5 8)) '(2 0 1 2)))

(define (tuple-constructors infs fins)
  (define inf?s (inf-slots (map cdr infs)
                           (map cdr fins)))
  (define (decon xs)
    (let loop ([xs xs]
               [inf-acc '()]
               [fin-acc '()]
               [inf?s   inf?s])
      (match* (xs inf?s)
              [('() '()) (cons (reverse inf-acc)
                               (reverse fin-acc))]
              [((cons x rest-xs) (cons inf? rest-inf?s))
               (cond [inf?
                      (loop rest-xs
                            (cons x inf-acc)
                            fin-acc
                            rest-inf?s)]
                     [else
                      (loop rest-xs
                            inf-acc
                            (cons x fin-acc)
                            rest-inf?s)])])))
  (define (recon infs-fins)
    (match-define (cons infs fins) infs-fins)
    (let loop ([infs infs]
               [fins fins]
               [inf?s inf?s]
               [acc '()])
      (match inf?s
        ['() (reverse acc)]
        [(cons inf? rest)
         (cond [inf?
                (loop (cdr infs)
                      fins
                      rest
                      (cons (car infs) acc))]
               [else
                (loop infs
                      (cdr fins)
                      rest
                      (cons (car fins) acc))])])))
  (values decon recon))

(define (inf-slots infs fins)
  (define sorted-infs (sort infs <))
  (define sorted-fins (sort fins <))
  (reverse
   (let loop ([inf-is sorted-infs]
              [fin-is sorted-fins]
              [acc    '()])
     (match* (inf-is fin-is)
             [('() '()) acc]
             [((cons _ _) '())
              (append (for/list ([_ (in-list inf-is)]) #t) acc)]
             [('() (cons _ _))
              (append (for/list ([_ (in-list fin-is)]) #f) acc)]
             [((cons ii rest-iis) (cons fi rest-fis))
              (cond [(ii . < . fi)
                     (loop rest-iis
                           fin-is
                           (cons #t acc))]
                    [else
                     (loop inf-is
                           rest-fis
                           (cons #f acc))])]))))

(define (inf-fin-cons/e e1 e2)
  (define s1 (enum-count e1))
  (define s2 (enum-count e2))
  (define fst-finite? (not (infinite? s1)))
  (define fin-size
    (cond [fst-finite? s1]
          [else s2]))
  (define (dec n)
    (define-values (q r)
      (quotient/remainder n fin-size))
    (define x1 (from-nat e1 (if fst-finite? r q)))
    (define x2 (from-nat e2 (if fst-finite? q r)))
    (cons x1 x2))
  (define enc
    (and (enum-to e1)
         (enum-to e2)
         (λ (p)
           (match p
             [(cons x1 x2)
              (define n1 (to-nat e1 x1))
              (define n2 (to-nat e2 x2))
              (define q (if fst-finite? n2 n1))
              (define r (if fst-finite? n1 n2))
              (+ (* fin-size q)
                 r)]))))
  (-enum (* s1 s2) dec enc (cons/c (enum-contract e1) (enum-contract e2))))

(define singleton-empty-list/e
  (-enum 1 (λ (x) '()) (λ (e) 0) (list/c)))

(define (list/e #:ordering [ordering 'square] . es)
  (define l (length es))
  (cond
    [(= l 0) singleton-empty-list/e]
    [(= l 1) (map/e list car (car es) #:contract (list/c (enum-contract (car es))))]
    [(all-infinite? es)
     (if (equal? ordering 'square)
         (apply box-list/e es)
         (apply cantor-list/e es))]
    [(all-finite? es) (apply nested-cons-list/e es)]
    [else
     (define tagged-es
       (for/list ([i (in-naturals)]
                  [e (in-list es)])
         (cons e i)))
     (define-values (inf-eis fin-eis)
       (partition (λ (x) (infinite-enum? (car x))) tagged-es))
     (define inf-es (map car inf-eis))
     (define inf-is (map cdr inf-eis))
     (define fin-es (map car fin-eis))
     (define fin-is (map cdr fin-eis))
     (define inf-slots
       (reverse
        (let loop ([inf-is inf-is]
                   [fin-is fin-is]
                   [acc '()])
          (match* (inf-is fin-is)
            [('() '()) acc]
            [((cons _ _) '())
             (append (for/list ([_ (in-list inf-is)]) #t) acc)]
            [('() (cons _ _))
             (append (for/list ([_ (in-list fin-is)]) #f) acc)]
            [((cons ii rest-iis) (cons fi rest-fis))
             (cond [(ii . < . fi)
                    (loop rest-iis
                          fin-is
                          (cons #t acc))]
                   [else
                    (loop inf-is
                          rest-fis
                          (cons #f acc))])]))))
     (define/match (reconstruct infs-fins)
       [((cons infs fins))
        (let loop ([infs infs]
                   [fins fins]
                   [inf?s inf-slots]
                   [acc '()])
          (match inf?s
            ['() (reverse acc)]
            [(cons inf? rest)
             (cond [inf?
                    (loop (cdr infs)
                          fins
                          rest
                          (cons (car infs) acc))]
                   [else
                    (loop infs
                          (cdr fins)
                          rest
                          (cons (car fins) acc))])]))])
     (define (deconstruct xs)
       (let loop ([xs xs]
                  [inf-acc '()]
                  [fin-acc '()]
                  [inf?s inf-slots])
         (match* (xs inf?s)
           [('() '()) (cons (reverse inf-acc)
                            (reverse fin-acc))]
           [((cons x rest-xs) (cons inf? rest-inf?s))
            (cond [inf?
                   (loop rest-xs
                         (cons x inf-acc)
                         fin-acc
                         rest-inf?s)]
                  [else
                   (loop rest-xs
                         inf-acc
                         (cons x fin-acc)
                         rest-inf?s)])])))
     (map/e reconstruct
            deconstruct
            (inf-fin-cons/e (apply list/e #:ordering ordering inf-es)
                            (apply list/e fin-es))
            #:contract (apply list/c (map enum-contract es)))]))

(define (nested-cons-list/e . es)
  (define l (length es))
  (define split-point (quotient l 2))
  (define-values (left right) (split-at es split-point))
  (define left-list/e (apply list/e left))
  (define right-list/e (apply list/e right))
  (map/e
   (λ (pr) (append (car pr) (cdr pr)))
   (λ (lst)
      (define-values (left right) (split-at lst split-point))
      (cons left right))
   (fin-cons/e left-list/e right-list/e)
   #:contract (apply list/c (map enum-contract es))))

(define (all-infinite? es) (all-something? infinite-enum? es))
(define (all-finite? es) (all-something? finite-enum? es))
(define (all-something? p? es)
  (for/and ([e (in-list es)])
    (p? e)))

;; Fair tupling via generalized cantor n-tupling
;; ordering is monotonic in the sum of the elements of the list
(define (cantor-list/e . es)
  (for ([e (in-list es)]
        [i (in-naturals)])
    (unless (infinite-enum? e)
      (apply raise-argument-error 
             'cantor-list/e
             "infinite-enum?"
             i
             es)))
  (define two-way-result?
    (for/and ([e (in-list es)])
      (two-way-enum? e)))
  (cond [(empty? es) singleton-empty-list/e]
        [else
         (define k (length es))
         (define dec
           (compose
            (λ (xs) (map from-nat es xs))
            (cantor-untuple k)))
         (define enc
           (and two-way-result?
                (compose
                 (cantor-tuple k)
                 (λ (xs) (map to-nat es xs)))))
         (-enum +inf.0 dec enc 
                (apply list/c (map enum-contract es)))]))

(define (prime-factorize k)
  (apply append
         (for/list ([d-e (in-list (factorize k))])
           (define divisor (first d-e))
           (define exponent (second d-e))
           (for/list ([_ (in-range exponent)])
             divisor))))
(module+ test
  (check-equal? (prime-factorize 14) '(2 7))
  (check-equal? (prime-factorize 24) '(2 2 2 3)))
(define (chunks-of l k)
  (let loop ([l l]
             [acc '()])
    (cond [(empty? l) (reverse acc)]
          [else
           (define-values (chunk rest) (split-at l k))
           (loop rest (cons chunk acc))])))
(module+ test
  (define 1-6 '(1 2 3 4 5 6))
  (check-equal? (chunks-of 1-6 1) '((1) (2) (3) (4) (5) (6)))
  (check-equal? (chunks-of 1-6 2) '((1 2) (3 4) (5 6)))
  (check-equal? (chunks-of 1-6 3) '((1 2 3) (4 5 6)))
  (check-equal? (chunks-of 1-6 6) '((1 2 3 4 5 6))))

;; Fair tupling via generalized
;; ordering is monotonic in the max of the elements of the list
(define (box-list/e . es)
  (for ([e (in-list es)]
        [i (in-naturals)])
    (unless (infinite-enum? e)
      (apply raise-argument-error 
             'box-list/e
             "infinite-enum?"
             i
             es)))
  (define k (length es))
  (cond [(= k 0) singleton-empty-list/e]
        [(= k 1) (map/e list car (car es))]
        [else
         (define factors (prime-factorize k))
         (let loop ([factors factors]
                    [es es]
                    [k k])
           (match factors
             [(cons factor '())
              (prime-length-box-list/e es)]
             [(cons factor factors)
              (define chunk-size (/ k factor))
              (define chunk/es
                (for/list ([es (in-list (chunks-of es chunk-size))])
                  (loop factors es chunk-size)))
              (map/e
               (λ (chunks)
                  (apply append chunks))
               (λ (xs)
                  (chunks-of xs chunk-size))
               (prime-length-box-list/e chunk/es)
               #:contract (apply list/c (map enum-contract es)))]))]))

(define (prime-length-box-list/e es)
  (cond
    [(ormap one-way-enum? es)
     (pam/e (curry map from-nat es)
            (box-tuples/e (length es))
            #:contract
            (apply list/c (map enum-contract es)))]
    [else
     (map/e (curry map from-nat es)
            (curry map to-nat es)
            (box-tuples/e (length es))
            #:contract
            (apply list/c (map enum-contract es)))]))

(define (box-tuples/e k)
  (-enum +inf.0 (box-untuple k) (box-tuple k) 
         (apply list/c (build-list k (λ (_) exact-nonnegative-integer?)))))

;; Enumeration of lists of length `len` of nats <= bound, 
;; containing bound at least once
;; 
;; (enum->list (bounded-list/e 2 3))
;; => '((0 3) (1 3) (2 3) (3 0) (3 1) (3 2) (3 3))
(define (bounded-list/e len bound)
  (define (loop len)
    (match len
      [0 singleton-empty-list/e]
      [1 
       (define lst (list bound))
       (map/e (λ (x) lst) (λ (lst) 0) (below/e 1) #:contract (list/c bound))]
      [_
       (define smallers/e (loop (sub1 len)))
       (define bounded/e (below/e (add1 bound)))
       (define first-max/e
         (map/e
          (curry cons bound)
          cdr
          (apply list/e
           (for/list ([_ (in-range (sub1 len))])
             bounded/e))
          #:contract 
          (apply list/c (build-list len (λ (_) (and/c (between/c 0 bound)
                                                      exact-integer?))))))
       (define first-not-max/e
         (match bound
           [0 empty/e]
           [_ (fin-cons/e (below/e bound)
                          smallers/e)]))
       (define (first-max? l)
         ((first l) . = . bound))
       (append/e (cons first-not-max/e (negate first-max?))
                 (cons first-max/e     first-max?))]))
  (loop len))

(define (box-tuple k)
  (λ (xs)
     (define layer (apply max xs))
     (define smallest (expt layer k))
     (define layer/e (bounded-list/e k layer))
     (smallest . + . (to-nat layer/e xs))))

(define (box-untuple k)
  (λ (n)
     (define layer (integer-root n k))
     (define smallest (expt layer k))
     (define layer/e (bounded-list/e k layer))
     (from-nat layer/e (n . - . smallest))))

