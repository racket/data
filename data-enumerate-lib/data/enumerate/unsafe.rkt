#lang racket/base
(require racket/bool
         racket/contract
         racket/function
         racket/list
         racket/math
         racket/match
         racket/promise
         racket/vector
         racket/generic
         data/gvector
         (only-in math/number-theory
                  binomial
                  integer-root
                  factorize))

(module+ test (require rackunit))

#|

changes:
 - add contracts to enumeration values
 - allow only finite-enum? for enum-size
 - map/e gets a #:contract argument (other ones?)
 - added one-way enumerations (as opposed to bijective)
 - added flat-enum? predicate

todo:
 - criterion for "less checked": avoid all checks that call from-nat/to-nat
 - add a coercion function to turn lists into enumerations of
   their elements automatically and non-lists into constant
   enumerations.
 - split data/enum into two libraries, one smaller with "essential" stuff called
   data/enumerate and one larger with other stuff, called data/enumerate/lib

 - vector/e -- make it like list/e
 - enum-to field-check:
   dep/e (3 of them....)

 - add argument to thunk/e, check uses

 - add contract to fix/e to check
     that the sizes are right
     change the argument order so optional arguments work....


 - get rid of the printfs in lib.rkt
 - coerce lists and base values (ones accepted by fin/e) into enumerations
   automatically. 
 - change disj-append/e to work like sum/e (allowing enumerators with
   flat contract to double as the predicates)
 - find a better name than `unsafe.rkt`


notes for eventual email:
 - finite vs infinite enumerations
 - invertible or not
 - contracts in enumerations (property: bijection)
 - take/e as an example for how flatness and bijection
   come together to automate some of the contract specification


|#

(provide 
 enum
 enum?
 enum-size
 from-nat
 to-nat
 enum-contract
 map/e
 pam/e
 except/e
 approximate
 to-list
 take/e
 slice/e
 below/e
 empty/e
 fin/e
 nat/e
 int/e
 sum/e
 disj-append/e
 fin-cons/e
 cons/e
 traverse/e
 hash-traverse/e
 dep/e
 flip-dep/e
 thunk/e
 fix/e
 many/e
 many1/e
 cantor-vec/e
 vec/e
 box-vec/e
 list/e
 cantor-list/e
 box-list/e
 prime-length-box-list/e
 bounded-list/e
 nat+/e
 fail/e
 box-tuples/e
 
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
  (display "#<enum" port)
  (define the-size (enum-size enum))
  (define more-to-go?
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
           (define ele (from-nat enum i))
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
          [else #t]))))
  (if more-to-go?
      (display "...>" port)
      (display ">" port)))
(define enum-printing (make-parameter 0))

(define (two-way-enum? x) (and (enum? x) (enum-to x) #t))
(define (one-way-enum? x) (and (enum? x) (not (enum-to x))))
(define (flat-enum? e) (and (enum? e) (flat-contract? (enum-contract e))))
(define (finite-enum? e) (and (enum? e) (not (infinite? (enum-size e)))))
(define (infinite-enum? e) (and (enum? e) (infinite? (enum-size e))))

(define (from-nat e n) ((enum-from e) n))
(define (to-nat e a) ((enum-to e) a))
(define (enum-contract e) (enum-ctc e))

;; helper to find arity errors at compile time
(require (for-syntax racket/base))
(define-syntax (-enum stx)
  (syntax-case stx ()
    [(_ a b c d) #'(enum a b c d)]))

;; an enum a is a struct of < Nat or +Inf, Nat -> a, a -> Nat >
(struct enum (size from to ctc)
  #:methods gen:custom-write
  [(define write-proc enum-write-proc)])


(define (map/e #:contract [ctc any/c] f inv-f e . es)
  (cond 
    [(or (one-way-enum? e) (ormap one-way-enum? es))
     (apply pam/e #:contract ctc f e es)]
    [else
     (define (map1/e f inv-f e)
       (-enum (enum-size e)
              (λ (x) 
                (f (from-nat e x)))
              (λ (n)
                (to-nat e (inv-f n)))
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
    (-enum (enum-size e)
           (λ (x) (f (from-nat e x)))
           #f
           ctc))
  (cond 
    [(empty? es) (pam1/e f e)]
    [else
     (pam1/e
      (λ (xs) (apply f xs))   
      (apply list/e (cons e es)))]))

;; except/e : (enum a) a* -> (enum a)
;; Everything inside e MUST be in the enumerator or you will get an error
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
    (cond [(= (enum-size e) 0) e]
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
           (-enum (max 0 (sub1 (enum-size e))) from-nat2 to-nat2 any/c)]))
  (define w/wrong-contract
    (foldr except1/e
           e
           excepts))
  (-enum (enum-size w/wrong-contract)
         (enum-from w/wrong-contract)
         (enum-to w/wrong-contract)
         contract))

(define (approximate e n)
  (for/list ([i (in-range n)])
    (from-nat e i)))

(define (to-list e)
  (for/list ([i (in-range (enum-size e))])
    (from-nat e i)))

(define (take/e e n #:contract [contract 
                                (λ (x)
                                  (and ((enum-contract e) x)
                                       (< (to-nat e x) n)))])
  (-enum n
         (λ (k)
           (from-nat e k))
         (and (enum-to e)
              (λ (x)
                (let ([k (to-nat e x)])
                  (unless (< k n)
                    (error 'take/e "attempted to encode an element not in an enumerator"))
                  k)))
         contract))

(define (slice/e e lo hi 
                 #:contract 
                 [contract 
                  (let ([c (enum-contract e)])
                    (unless (flat-contract? c)
                      (error 'slice/e
                             (string-append
                              "expected either an explicit #:contract"
                              " argument or an enumerator with a flat contract, got ~v" e)))
                    (and/c c
                           (let ([in-the-slice?
                                  (λ (x)
                                    (for/or ([i (in-range lo hi)])
                                      (equal? (from-nat e i) x)))])
                             in-the-slice?)))])
  (-enum (hi . - . lo)
         (λ (n)
           (from-nat e (n . + . lo)))
         (and (enum-to e)
              (λ (x)
                (define n (to-nat e x))
                (unless (and (n . >= . lo)
                             (n . <  . hi))
                  (error 'slice/e
                         (string-append
                          "attempted to encode an element removed by slice/e:"
                          " ~s was excepted, originally ~s, but sliced between ~s and ~s" x n lo hi)))
                (n . - . lo)))
         contract))

;; below/e
(define (below/e n)
  (take/e nat/e n #:contract (integer-in 0 (- n 1))))

(define empty/e
  (-enum 0
         void
         (λ (x)
           (error 'to-nat "no elements in the enumerator"))
         none/c))

(define no-contract (box #f))
(define (fin/e . args)
  (cond
    [(null? args) empty/e]
    [else
     (define (use-=? x) (and (number? x) (not (memv x '(+nan.0 +nan.f)))))
     (define-values (use-= use-equal?) (partition use-=? args))
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
     (define vec (list->vector args))
     (-enum (vector-length vec)
            (λ (n) (vector-ref vec n))
            (λ (x) 
              (cond
                [(use-=? x)
                 (for/first ([pr (in-list num-rev-map)]
                             #:when (= x (car pr)))
                   (cdr pr))]
                [else (hash-ref rev-map x)]))
            (apply or/c args))]))

(define nat/e (-enum +inf.0 values values exact-nonnegative-integer?))


(define int/e
  (-enum +inf.0
         (λ (n)
           (if (even? n)
               (* -1 (/ n 2))
               (/ (+ n 1) 2)))
         (λ (n)
           (if (> n 0)
               (- (* 2 n) 1)
               (* 2 (abs n))))
         exact-integer?))

(define (empty/e? e)
  (= 0 (enum-size e)))

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
         (apply exact-min (map (compose enum-size car) non-emptys)))
       (define (not-min-size? e)
         (not (= (enum-size (car e)) min-size)))
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
                 (map (compose enum-size car) cur-exhausteds))))
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
(define (sum/e . e-or-e/ps)
  (define e-ps (for/list ([x (in-list e-or-e/ps)])
                 (cond
                   [(enum? x) (cons x (enum-contract x))]
                   [else x])))
  (define (non-empty-e-p? e-p)
    (not (= 0 (enum-size (car e-p)))))
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
       (and (andmap (λ (x) (two-way-enum? (car x))) e-ps)
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
     (-enum (apply + (map (compose enum-size car) non-empty-e-ps))
            dec
            enc
            (apply or/c (map (λ (x) (enum-contract (car x))) non-empty-e-ps)))]))

;; Like sum/e, but sequences the enumerations instead of interleaving
(define (disj-append/e e-p . e-ps)
  (define/match (disj-append2/e e-p1 e-p2)
    [((cons e1 1?) (cons e2 2?))
     (define s1 (enum-size e1))
     (define s2 (enum-size e2))
     (when (infinite? s1)
       (error 'disj-append/e "only the last enum argument to disj-append/e may be infinite"))
     (define (from-nat2 n)
       (cond [(< n s1) (from-nat e1 n)]
             [else (from-nat e2 (- n s1))]))
     (define to-nat2
       (and (two-way-enum? e1)
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
  (define s1 (enum-size e1))
  (define s2 (enum-size e2))
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

;; cons/e : enum a, enum b ... -> enum (cons a b ...)
(define (cons/e e1 e2 #:ordering [ordering 'square])
  (map/e (λ (x)
            (cons (first  x)
                  (second x)))
         (λ (x-y)
            (list (car x-y) (cdr x-y)))
         (list/e e1 e2 #:ordering ordering)
         #:contract (cons/c (enum-contract e1) (enum-contract e2))))

;; Traversal (maybe come up with a better name
;; traverse/e : (a -> enum b), (listof a) -> enum (listof b)
(define (traverse/e f xs)
  (apply list/e (map f xs)))

;; Hash Traversal
;; hash-traverse/e : (a -> enum b), (hash[k] -o> a) -> enum (hash[k] -o> b)
(define (hash-traverse/e f ht)
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
    (traverse/e on-cdr as-list))
  (define (hash-that-maps-correct-keys? candidate-ht)
    (define b (box #f))
    (for/and ([(k v) (in-hash ht)])
      (not (eq? (hash-ref candidate-ht k b) b))))
  (map/e make-immutable-hash
         hash->list
         assoc/e
         #:contract 
         (and/c
          hash?
          hash-that-maps-correct-keys?
          (hash/dc [k any/c]
                   [v (k) (enum-contract (f k))]))))

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


(define (dep/e e f #:f-range-finite? [f-range-finite? #f])
  (define the-ctc (cons/dc [hd (enum-contract e)] [tl (hd) (enum-contract (f hd))]))
  (cond
    [(= 0 (enum-size e)) empty/e]
    [f-range-finite?
     (dep/e-dependent-ranges-all-finite e f the-ctc)]
    [(finite-enum? e)
     (-enum +inf.0
            (λ (n)
              (define-values (q r) (quotient/remainder n (enum-size e)))
              (cons (from-nat e r)
                    (from-nat (f (from-nat e r)) q)))
            (λ (ab)
              (+ (* (enum-size e) (to-nat (f (car ab)) (cdr ab)))
                 (to-nat e (car ab))))
            the-ctc)]
    [else ;; both infinite, same as cons/e
     (-enum +inf.0               
            (λ (n)
              (let* ([k (floor-untri n)]
                     [t (tri k)]
                     [l (- n t)]
                     [m (- k l)]
                     [a (from-nat e l)])
                (cons a
                      (from-nat (f a) m))))
            (λ (xs) ;; bijection from nxn -> n, inverse of previous
              ;; (n,m) -> (n+m)(n+m+1)/2 + n
              (unless (pair? xs)
                (error 'dep2/e "not a pair"))
              (let ([l (to-nat e (car xs))]
                    [m (to-nat (f (car xs)) (cdr xs))])
                (+ (/ (* (+ l m) (+ l m 1))
                      2)
                   l)))
            the-ctc)]))

(define (dep/e-dependent-ranges-all-finite e f the-ctc)
  ;; 'sizes' is a memo table that caches the size of the dependent enumerators
  ;; sizes[n] = # of terms with left side index <= n
  ;; sizes : gvector int
  (define sizes (gvector (enum-size (f (from-nat e 0)))))
  (define (search-size sizes n)
    (when (zero? (gvector-count sizes))
      (gvector-add! sizes (enum-size (f (from-nat e 0)))))
    (define (loop cur)
      (let* ([lastSize (gvector-ref sizes (- cur 1))]
             [e2 (f (from-nat e cur))]
             [s  (+ lastSize (enum-size e2))])
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
             [s (+ prevSize (enum-size curE))])
        (gvector-add! sizes s)
        (if (= cur n)
            s
            (loop (+ cur 1))))))
  
  (define the-enum-size
    (if (infinite? (enum-size e))
        +inf.0
        (foldl
         (λ (curSize acc)
           (let ([sum (+ curSize acc)])
             (gvector-add! sizes sum)
             sum))
         (gvector-ref sizes 0)
         (map (compose enum-size f) (cdr (to-list e))))))
  
  (-enum the-enum-size
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
         (λ (ab)
           (let* ([a (car ab)]
                  [b (cdr ab)]
                  [ai (to-nat e a)]
                  [ei (f a)]
                  [nextSize (enum-size ei)]
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
                (to-nat ei b))))
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


;; flip-dep/e : enum a (a -> enum b) -> enum (b,a)
(define (flip-dep/e e f #:f-range-finite? [f-range-finite? #f])
  (map/e
   (λ (ab)
      (cons (cdr ab)
            (car ab)))
   (λ (ba)
      (cons (cdr ba)
            (car ba)))
   (dep/e e f #:f-range-finite? f-range-finite?)
   #:contract
   (cons/dc [hd (tl) (enum-contract (f tl))] [tl (enum-contract e)])))


;; thunk/e : Nat or +-Inf, ( -> enum a) -> enum a
(define (thunk/e s thunk #:two-way-enum? [two-way? #t])
  (define promise/e (delay (thunk)))
  (-enum s
         (λ (n)
           (give-up-on-bijection-checking promise/e)
           (from-nat (force promise/e) n))
         (and two-way?
              (λ (x)
                (give-up-on-bijection-checking promise/e)
                (to-nat (force promise/e) x)))
         (recursive-contract
          (enum-contract
           (force promise/e)))))

;; fix/e : [size] (enum a -> enum a) -> enum a
(define fix/e
  (case-lambda
    [(f/e) (fix/e +inf.0 f/e)]
    [(size f/e)
     (define self (delay (f/e (fix/e size f/e))))
     (-enum size
            (λ (n)
              (give-up-on-bijection-checking self)
              (from-nat (force self) n))
            (λ (x)
              (give-up-on-bijection-checking self)
              (to-nat (force self) x))
            (recursive-contract 
             (enum-contract 
              (force self))))]))

;; many/e : enum a -> enum (listof a)
;;       or : enum a, #:length natural -> enum (listof a)
(define many/e
  (case-lambda
    [(e)
     (define fix-size
       (if (= 0 (enum-size e))
           1
           +inf.0))
     (define result-e
       (fix/e fix-size
              (λ (self)
                (sum/e (cons (fin/e '()) null?)
                       (cons (cons/e e self) pair?)))))
     (struct-copy enum result-e
                  [ctc (listof (enum-contract e))])]
    [(e n)
     (apply list/e (build-list n (const e)))]))

;; many1/e : enum a -> enum (nonempty listof a)
(define (many1/e e)
  (except/e (many/e e) '()
            #:contract (non-empty-listof (enum-contract e))))

(define (cantor-vec/e . es)
  (map/e list->vector
         vector->list
         (apply cantor-list/e es)
         #:contract (apply vector/c (map enum-contract es))))

;; vec/e : listof (enum any) -> enum (vectorof any)
(define vec/e cantor-vec/e)

(define (box-vec/e . es)
  (map/e list->vector
         vector->list
         (apply box-list/e es)
         #:contract
         (apply vector/c (map enum-contract es))))

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
  (define s1 (enum-size e1))
  (define s2 (enum-size e2))
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

(define (list/e #:ordering [ordering 'square] . es)
  (define l (length es))
  (cond
    [(= l 0) (fin/e '())]
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
            (inf-fin-cons/e (apply list/e #:ordering 'ordering inf-es)
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
  (cond [(empty? es) (fin/e '())]
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
  (cond [(= k 0) (fin/e '())]
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
  (map/e (curry map from-nat es)
         (curry map to-nat es)
         (box-tuples/e (length es))
         #:contract
         (apply list/c (map enum-contract es))))

(define (box-tuples/e k)
  (-enum +inf.0 (box-untuple k) (box-tuple k) 
         (apply list/c (build-list k (λ (_) exact-nonnegative-integer?)))))

;; Tuples of length k with maximum bound
(define (bounded-list/e len bound)
  (define (loop len)
    (match len
      [0 (fin/e '())]
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
       (disj-append/e (cons first-not-max/e (negate first-max?))
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

(define (nat+/e n)
  (map/e (λ (k)
            (+ k n))
         (λ (k)
            (- k n))
         nat/e
         #:contract
         (and/c (>=/c n) exact-integer?)))

;; fail/e : exn -> enum ()
(define (fail/e e)
  (define (t _) (raise e))
  (-enum 1 t t none/c))
