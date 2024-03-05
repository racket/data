#lang racket/base
;; written by ryanc
(require (for-syntax racket/base
                     syntax/contract
                     syntax/for-body)
	 racket/performance-hint
         racket/serialize
         racket/fixnum
         racket/contract/base
         racket/dict
	 racket/unsafe/ops
         racket/vector
         racket/struct)

(define DEFAULT-CAPACITY 10)

(define MIN-CAPACITY 8)

(define (make-gvector #:capacity [capacity DEFAULT-CAPACITY])
  (unless (exact-nonnegative-integer? capacity)
    (raise-argument-error* 'make-gvector 'data/gvector "exact-nonnegative-integer?" capacity))
  (gvector (make-vector (max capacity MIN-CAPACITY) 0) 0))

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

(begin-encourage-inline

  (define (check-gvector who gv)
    (unless (gvector? gv)
      (raise-argument-error* who 'data/gvector "gvector?" gv)))


  ;; ensure-free-space-vec! : Vector Nat Nat -> Vector/#f
  (define (ensure-free-space-vec! vec n needed-free-space)
    (define cap (unsafe-vector*-length vec))
    (define needed-cap (unsafe-fx+ n needed-free-space))
    (cond [(<= needed-cap cap) #f]
	  [else
	   ;; taken from Rust's raw_vec implementation
	   (let* ([new-cap (unsafe-fxmax (unsafe-fx* 2 cap) needed-cap)]
		  [new-cap (unsafe-fxmax new-cap MIN-CAPACITY)])
	     (vector*-extend vec new-cap 0))]))

  (define (ensure-free-space! gv needed-free-space)
    (define v (ensure-free-space-vec! (gvector-vec gv) (gvector-n gv) needed-free-space))
    (when v (set-gvector-vec! gv v)))

  (define-syntax-rule (gv-ensure-space! gv n v needed-free-space)
    (begin (define n (gvector-n gv))
	   (define v1 (gvector-vec gv))
	   (define v2 (ensure-free-space-vec! v1 n needed-free-space))
	   (define v (if v2 (begin (set-gvector-vec! gv v2) v2) v1))))

  ;; only safe on unchaperoned gvectors
  (define (unsafe-gvector-add! gv item)
    (gv-ensure-space! gv n v 1)
    (unsafe-vector*-set! v n item)
    (set-gvector-n! gv (unsafe-fx+ 1 n)))

  (define gvector-add!
    (case-lambda
      [(gv item)
       (check-gvector 'gvector-add! gv)
       (gv-ensure-space! gv n v 1)
       (unsafe-vector*-set! v n item)
       (set-gvector-n! gv (unsafe-fx+ 1 n))]
      [(gv . items)
       (check-gvector 'gvector-add! gv)
       (define item-count (length items))
       (gv-ensure-space! gv n v item-count)
       (for ([index (in-naturals n)] [item (in-list items)])
	 (unsafe-vector*-set! v index item))
       (set-gvector-n! gv (+ n item-count))])))

;; SLOW!
(define (gvector-insert! gv index item)
  ;; This does (n - index) redundant copies on resize, but that
  ;; happens rarely and I prefer the simpler code.
  (check-gvector 'gvector-insert! gv)
  (check-index 'gvector-insert! gv index #t)
  (define n (gvector-n gv))
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
  (check-gvector 'gvector-remove! gv)
  (define n (gvector-n gv))
  (define v (gvector-vec gv))
  (check-index 'gvector-remove! gv index #f)
  (vector-copy! v index v (add1 index) n)
  (vector-set! v (sub1 n) #f)
  (set-gvector-n! gv (sub1 n))
  (trim! gv))

(define (gvector-remove-last! gv)
  (check-gvector 'gvector-remove-last! gv)
  (let ([n (gvector-n gv)]
        [v (gvector-vec gv)])
    (unless (> n 0) (error 'gvector-remove-last! "empty"))
    (define last-val (vector-ref v (sub1 n)))
    (gvector-remove! gv (sub1 n))
    last-val))

(define (gvector-count gv)
  (check-gvector 'gvector-count gv)
  (gvector-n gv))

(define none (gensym 'none))

(define (gvector-ref gv index [default none])
  (check-gvector 'gvector-ref gv)
  (unless (exact-nonnegative-integer? index)
    (raise-type-error 'gvector-ref "exact nonnegative integer" index))
  (if (< index (gvector-n gv))
      (unsafe-vector*-ref (gvector-vec gv) index)
      (cond [(eq? default none)
             (check-index 'gvector-ref gv index #f)]
            [(procedure? default) (default)]
            [else default])))

;; gvector-set! with index = |gv| is interpreted as gvector-add!
(define (gvector-set! gv index item)
  (check-gvector 'gvector-set gv)
  (let ([n (gvector-n gv)])
    (check-index 'gvector-set! gv index #t)
    (if (unsafe-fx= index n)
        (unsafe-gvector-add! gv item)
        (unsafe-vector*-set! (gvector-vec gv) index item))))

;; creates a snapshot vector
(define (gvector->vector gv)
  (check-gvector 'gvector->vector gv)
  (vector*-copy (gvector-vec gv) 0 (gvector-n gv)))

(define (gvector->list gv)
  (check-gvector 'gvector->list gv)
  (vector->list (gvector->vector gv)))

;; constructs a gvector
(define (vector->gvector v)
  (unless (vector? v)
    (raise-argument-error* vector->gvector 'data/gvector "vector?" v))
  (define lv (vector-length v))
  (define gv (make-gvector #:capacity (max lv DEFAULT-CAPACITY)))
  (define nv (gvector-vec gv))
  (vector-copy! nv 0 v)
  (set-gvector-n! gv lv)
  gv)

(define (list->gvector v)
  (unless (list? v)
    (raise-argument-error* list->gvector 'data/gvector "list?" v))
  (vector->gvector (list->vector v)))

;; Iteration methods

;; A gvector position is represented as an exact-nonnegative-integer.

(define (gvector-iterate-first gv)
  (and (positive? (gvector-n gv)) 0))

(define (gvector-iterate-next gv iter)
  (check-index 'gvector-iterate-next gv iter #f)
  (let ([n (gvector-n gv)])
    (and (< (unsafe-fx+ 1 iter) n)
         (unsafe-fx+ 1 iter))))

(define (gvector-iterate-key gv iter)
  (check-index 'gvector-iterate-key gv iter #f)
  iter)

(define (gvector-iterate-value gv iter)
  (check-index 'gvector-iterate-value gv iter #f)
  (gvector-ref gv iter))

(define (in-gvector gv)
  (check-gvector 'in-gvector gv)
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
                    (unsafe-fx< index n) ;; pos-guard
                    ([(var) (unsafe-vector*-ref vec index)]) ;; inner bindings
                    #t ;; pre-guard
                    #t ;; post-guard
                    ((unsafe-fx+ 1 index) vec n))]))]
      [[(var ...) (in-gv gv-expr)]
       (with-syntax ([gv-expr-c (wrap-expr/c #'gvector? #'gv-expr #:macro #'in-gv)])
         (syntax/loc stx
           [(var ...) (in-gvector gv-expr-c)]))]
      [_ #f])))

(define-syntax (for/gvector stx)
  (syntax-case stx ()
    [(_ (clause ...) . body)
     #'(for/gvector #:capacity DEFAULT-CAPACITY (clause ...) . body)]
    [(_ #:capacity cap (clause ...) . body)
     (with-syntax ([((pre-body ...) post-body) (split-for-body stx #'body)])
       (quasisyntax/loc stx
         (let ([gv (make-gvector #:capacity cap)])
           (for/fold/derived #,stx () (clause ...)
            pre-body ...
	     (call-with-values (lambda () . post-body)
			       (case-lambda
				 [(one) (unsafe-gvector-add! gv one)]
				 [args (apply gvector-add! gv args)]))
	     (values))
           gv)))]))

(define-syntax (for*/gvector stx)
  (syntax-case stx ()
    [(_ (clause ...) . body)
     #'(for/gvector #:capacity DEFAULT-CAPACITY (clause ...) . body)]
    [(_ #:capacity cap (clause ...) . body)
     (with-syntax ([((pre-body ...) post-body) (split-for-body stx #'body)])
       (quasisyntax/loc stx
         (let ([gv (make-gvector #:capacity cap)])
           (for*/fold/derived #,stx () (clause ...)
            pre-body ...
            (call-with-values (lambda () . post-body)
                              (case-lambda
                                [(one) (begin (unsafe-gvector-add! gv one) (values))]
                                [args (begin (apply gvector-add! gv args) (values))])))
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
  #:property prop:sequence in-gvector
  #:property prop:serializable
  (make-serialize-info
   (λ (this)
     (vector (gvector->vector this)))
   (cons 'deserialize-gvector (module-path-index-join '(submod data/gvector deserialize) #f))
   #t
   (or (current-load-relative-directory) (current-directory))))

(provide
 gvector?
 (rename-out [gvector* gvector])
 make-gvector
 gvector-ref
 gvector-set!
 gvector-add!
 gvector-insert!
 gvector-remove!
 gvector-remove-last!
 gvector-count
 gvector->vector
 gvector->list
 vector->gvector
 list->gvector
 (rename-out [in-gvector* in-gvector])
 for/gvector
 for*/gvector)

(module+ deserialize
  (provide deserialize-gvector)
  (define deserialize-gvector
    (make-deserialize-info
     (λ (vec)
       (vector->gvector vec))
     (λ ()
       (define gvec (make-gvector))
       (values
        gvec
        (λ (other)
          (for ([i (in-gvector other)])
            (gvector-add! gvec i))))))))
