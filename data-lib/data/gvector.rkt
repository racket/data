#lang racket/base
;; written by ryanc
(require (for-syntax racket/base
                     syntax/contract
                     syntax/for-body)
         racket/contract/base
         racket/dict
         racket/vector
         racket/struct)

(define DEFAULT-CAPACITY 10)

(define (make-gvector #:capacity [capacity DEFAULT-CAPACITY])
  (gvector (make-vector capacity #f) 0))

(define gvector*
  (let ([gvector
         (lambda init-elements
           (let ([gv (make-gvector)])
             (apply gvector-add! gv init-elements)
             gv))])
    gvector))

(define (check-index who gv index set-to-add?)
  ;; if set-to-add?, the valid indexes include one past the current end
  (define n (gvector-n gv))
  (define hi (if set-to-add? (add1 n) n))
  (unless (< index hi)
    (raise-range-error who "gvector" "" index gv 0 (sub1 hi))))

;; ensure-free-space! : GVector Nat -> Void
(define (ensure-free-space! gv needed-free-space)
  (define vec (gvector-vec gv))
  (define n (gvector-n gv))
  (define cap (vector-length vec))
  (define needed-cap (+ n needed-free-space))
  (unless (<= needed-cap cap)
    (define new-cap
      (let loop ([new-cap (max DEFAULT-CAPACITY cap)])
        (if (<= needed-cap new-cap) new-cap (loop (* 2 new-cap)))))
    (define new-vec (make-vector new-cap #f))
    (vector-copy! new-vec 0 vec)
    (set-gvector-vec! gv new-vec)))

(define gvector-add!
  (case-lambda
    [(gv item)
     (ensure-free-space! gv 1)
     (define n (gvector-n gv))
     (define v (gvector-vec gv))
     (vector-set! v n item)
     (set-gvector-n! gv (add1 n))]
    [(gv . items)
     (define item-count (length items))
     (ensure-free-space! gv item-count)
     (define n (gvector-n gv))
     (define v (gvector-vec gv))
     (for ([index (in-naturals n)] [item (in-list items)])
       (vector-set! v index item))
     (set-gvector-n! gv (+ n item-count))]))

;; SLOW!
(define (gvector-insert! gv index item)
  ;; This does (n - index) redundant copies on resize, but that
  ;; happens rarely and I prefer the simpler code.
  (define n (gvector-n gv))
  (check-index 'gvector-insert! gv index #t)
  (ensure-free-space! gv 1)
  (define v (gvector-vec gv))
  (vector-copy! v (add1 index) v index n)
  (vector-set! v index item)
  (set-gvector-n! gv (add1 n)))

;; Shrink when vector length is > SHRINK-ON-FACTOR * #elements
(define SHRINK-ON-FACTOR 4)
;; ... unless it would shrink to less than SHRINK-MIN
(define SHRINK-MIN 10)

;; Shrink by SHRINK-BY-FACTOR
(define SHRINK-BY-FACTOR 2)

(define (trim! gv)
  (define n (gvector-n gv))
  (define v (gvector-vec gv))
  (define cap (vector-length v))
  (define new-cap
    (let loop ([new-cap cap])
      (cond [(and (>= new-cap (* SHRINK-ON-FACTOR n))
                  (>= (quotient new-cap SHRINK-BY-FACTOR) SHRINK-MIN))
             (loop (quotient new-cap SHRINK-BY-FACTOR))]
            [else new-cap])))
  (when (< new-cap cap)
    (define new-v (make-vector new-cap #f))
    (vector-copy! new-v 0 v 0 n)
    (set-gvector-vec! gv new-v)))

;; SLOW!
(define (gvector-remove! gv index)
  (define n (gvector-n gv))
  (define v (gvector-vec gv))
  (check-index 'gvector-remove! gv index #f)
  (vector-copy! v index v (add1 index) n)
  (vector-set! v (sub1 n) #f)
  (set-gvector-n! gv (sub1 n))
  (trim! gv))

(define (gvector-remove-last! gv)
  (let ([n (gvector-n gv)]
        [v (gvector-vec gv)])
    (unless (> n 0) (error 'gvector-remove-last! "empty"))
    (define last-val (vector-ref v (sub1 n)))
    (gvector-remove! gv (sub1 n))
    last-val))

(define (gvector-count gv)
  (gvector-n gv))

(define none (gensym 'none))

(define (gvector-ref gv index [default none])
  (unless (exact-nonnegative-integer? index)
    (raise-type-error 'gvector-ref "exact nonnegative integer" index))
  (if (< index (gvector-n gv))
      (vector-ref (gvector-vec gv) index)
      (cond [(eq? default none)
             (check-index 'gvector-ref gv index #f)]
            [(procedure? default) (default)]
            [else default])))

;; gvector-set! with index = |gv| is interpreted as gvector-add!
(define (gvector-set! gv index item)
  (let ([n (gvector-n gv)])
    (check-index 'gvector-set! gv index #t)
    (if (= index n)
        (gvector-add! gv item)
        (vector-set! (gvector-vec gv) index item))))

;; creates a snapshot vector
(define (gvector->vector gv)
  (vector-copy (gvector-vec gv) 0 (gvector-n gv)))

(define (gvector->list gv)
  (vector->list (gvector->vector gv)))

;; constructs a gvector
(define (vector->gvector v)
  (define lv (vector-length v))
  (define gv (make-gvector #:capacity lv))
  (define nv (gvector-vec gv))
  (vector-copy! nv 0 v)
  (set-gvector-n! gv lv)
  gv)

(define (list->gvector v)
  (vector->gvector (list->vector v)))

;; Iteration methods

;; A gvector position is represented as an exact-nonnegative-integer.

(define (gvector-iterate-first gv)
  (and (positive? (gvector-n gv)) 0))

(define (gvector-iterate-next gv iter)
  (check-index 'gvector-iterate-next gv iter #f)
  (let ([n (gvector-n gv)])
    (and (< (add1 iter) n)
         (add1 iter))))

(define (gvector-iterate-key gv iter)
  (check-index 'gvector-iterate-key gv iter #f)
  iter)

(define (gvector-iterate-value gv iter)
  (check-index 'gvector-iterate-value gv iter #f)
  (gvector-ref gv iter))

(define (in-gvector gv)
  (unless (gvector? gv)
    (raise-type-error 'in-gvector "gvector" gv))
  (in-dict-values gv))

(define-sequence-syntax in-gvector*
  (lambda () #'in-gvector)
  (lambda (stx)
    (syntax-case stx ()
      [[(var) (in-gv gv-expr)]
       (with-syntax ([gv-expr-c (wrap-expr/c #'gvector? #'gv-expr #:macro #'in-gv)])
         (syntax/loc stx
           [(var)
            (:do-in ([(gv) gv-expr-c])
                    (void) ;; outer-check; handled by contract
                    ([index 0] [vec (gvector-vec gv)] [n (gvector-n gv)]) ;; loop bindings
                    (< index n) ;; pos-guard
                    ([(var) (vector-ref vec index)]) ;; inner bindings
                    #t ;; pre-guard
                    #t ;; post-guard
                    ((add1 index) (gvector-vec gv) (gvector-n gv)))]))]
      [[(var ...) (in-gv gv-expr)]
       (with-syntax ([gv-expr-c (wrap-expr/c #'gvector? #'gv-expr #:macro #'in-gv)])
         (syntax/loc stx
           [(var ...) (in-gvector gv-expr-c)]))]
      [_ #f])))

(define-syntax (for/gvector stx)
  (syntax-case stx ()
    [(_ (clause ...) . body)
     (with-syntax ([((pre-body ...) post-body) (split-for-body stx #'body)])
       (quasisyntax/loc stx
         (let ([gv (make-gvector)])
           (for/fold/derived #,stx () (clause ...)
            pre-body ...
            (call-with-values (lambda () . post-body)
              (lambda args (apply gvector-add! gv args) (values))))
           gv)))]))

(define-syntax (for*/gvector stx)
  (syntax-case stx ()
    [(_ (clause ...) . body)
     (with-syntax ([((pre-body ...) post-body) (split-for-body stx #'body)])
       (quasisyntax/loc stx
         (let ([gv (make-gvector)])
           (for*/fold/derived #,stx () (clause ...)
            pre-body ...
            (call-with-values (lambda () . post-body)
              (lambda args (apply gvector-add! gv args) (values))))
           gv)))]))

(struct gvector (vec n)
  #:mutable
  #:property prop:dict/contract
             (list (vector-immutable gvector-ref
                                     gvector-set!
                                     #f ;; set
                                     gvector-remove!
                                     #f ;; remove
                                     gvector-count
                                     gvector-iterate-first
                                     gvector-iterate-next
                                     gvector-iterate-key
                                     gvector-iterate-value)
                   (vector-immutable exact-nonnegative-integer?
                                     any/c
                                     exact-nonnegative-integer?
                                     #f #f #f))
  #:methods gen:equal+hash
  [(define (equal-proc x y recursive-equal?)
     (let ([vx (gvector-vec x)]
           [vy (gvector-vec y)]
           [nx (gvector-n x)]
           [ny (gvector-n y)])
       (and (= nx ny)
            (for/and ([index (in-range nx)])
              (recursive-equal? (vector-ref vx index)
                                (vector-ref vy index))))))
   (define (hash-code x hc)
     (let ([v (gvector-vec x)]
           [n (gvector-n x)])
       (for/fold ([h 1]) ([i (in-range n)])
         ;; FIXME: better way of combining hashcodes
         (+ h (hc (vector-ref v i))))))
   (define hash-proc  hash-code)
   (define hash2-proc hash-code)]
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (obj) 'gvector)
      (lambda (obj) (gvector->list obj))))]
  #:property prop:sequence in-gvector)

(provide/contract
 [gvector?
  (-> any/c any)]
 [rename gvector* gvector
  (->* () () #:rest any/c gvector?)]
 [make-gvector
  (->* () (#:capacity exact-positive-integer?) gvector?)]
 [gvector-ref
  (->* (gvector? exact-nonnegative-integer?) (any/c) any)]
 [gvector-set!
  (-> gvector? exact-nonnegative-integer? any/c any)]
 [gvector-add!
  (->* (gvector?) () #:rest any/c any)]
 [gvector-insert!
  (-> gvector? exact-nonnegative-integer? any/c any)]
 [gvector-remove!
  (-> gvector? exact-nonnegative-integer? any)]
 [gvector-remove-last!
  (-> gvector? any)]
 [gvector-count
  (-> gvector? any)]
 [gvector->vector
  (-> gvector? vector?)]
 [gvector->list
  (-> gvector? list?)]
 [vector->gvector
  (-> vector? gvector?)]
 [list->gvector
  (-> list? gvector?)])

(provide (rename-out [in-gvector* in-gvector])
         for/gvector
         for*/gvector)
