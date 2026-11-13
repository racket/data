#lang racket/base
;; written by ryanc

;; Memory safety under concurrent access:
;;
;; This data structure is NOT thread-safe: concurrent mutation may
;; lose updates or produce incorrect results. It must never corrupt
;; memory, however, and it uses unchecked vector operations, so each
;; of them has to be safe whatever other threads do.
;;
;; No reader can rely on (<= (gvector-n gv) (vector-length (gvector-vec gv)))
;; for the two values it reads, even though writers keep it when they
;; can. Another thread may change either field between the two reads:
;; a grower installs a larger vec and then a larger n, so a reader that
;; reads vec first can see the old vec with the new n, and a shrinker
;; stores n and then vec, so a reader that reads n first can see the old
;; n with the new vec. No one order of reads serves both. Nor do the
;; writers' orders reach other threads intact: Racket does not promise
;; that one thread sees another's stores in program order (see "Machine
;; Memory Order" in the reference), and on ARM it may not.
;;
;; So every unchecked access tests its index against a vector it holds:
;;
;; - gvector-ref, gvector-set! and in-gvector read vec once and test the
;;   index against that vector's length as well as against n.
;; - gvector-add! writes at the n it read, into the vector that
;;   define/ensure-space! checked has room past that n.
;; - Indexes from callers are checked to be natural numbers before any
;;   unchecked operation sees them.
;;
;; The writers' ordering and CAS keep concurrent adds and removes from
;; losing elements in most races:
;;
;; - Growing (gvector-add!, gvector-insert!, gvector-append!):
;;   Update vec first (to a larger vector), then update n.
;;
;; - Shrinking (gvector-remove! + trim!):
;;   Update n first (to a smaller value), then update vec.
;;
;; - CAS on vec (unsafe-struct*-cas! gv 0 old-vec new-vec):
;;   When growing, define/ensure-space! uses CAS to install the new
;;   vector. If another thread replaced vec concurrently (e.g. two
;;   concurrent gvector-add! calls both creating new vectors), the
;;   CAS fails and the operation retries with the current vec.
;;   Without CAS, thread T1 could install a small vector while T2
;;   installs a large n.
;;   Similarly, trim! uses CAS when installing a smaller vector.
;;
;; - n re-read in trim!:
;;   trim! re-reads n before creating the smaller vector. If n has
;;   grown past the target capacity (from concurrent adds that didn't
;;   need to resize vec), trim! aborts. After CAS succeeds, trim!
;;   checks again and grows back via ensure-free-space! if needed.
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

(struct gvector (vec n)
  #:mutable
  #:authentic
  #:property prop:dict/contract
             ;; expand these so they are not referenced before definition
             (list (vector-immutable (case-lambda
                                       [(gv i) (gvector-ref gv i)]
                                       [(gv i d) (gvector-ref gv i d)])
                                     (lambda (gv i v) (gvector-set! gv i v))
                                     #f ;; set
                                     (lambda (gv i) (gvector-remove! gv i))
                                     #f ;; remove
                                     (lambda (gv) (gvector-count gv))
                                     (lambda (gv) (gvector-iterate-first gv))
                                     (lambda (gv it) (gvector-iterate-next gv it))
                                     (lambda (gv it) (gvector-iterate-key gv it))
                                     (lambda (gv it) (gvector-iterate-value gv it)))
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
  #:property prop:sequence (lambda (gv) (in-gvector gv))
  #:property prop:serializable
  (make-serialize-info
   (λ (this)
     (vector (gvector->vector this)))
   (cons 'deserialize-gvector (module-path-index-join '(submod data/gvector deserialize) #f))
   #t
   (or (current-load-relative-directory) (current-directory))))

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

  ;; for an index argument, which unchecked operations may later use
  (define (check-natural who index)
    (unless (exact-nonnegative-integer? index)
      (raise-argument-error* who 'data/gvector "exact-nonnegative-integer?" index)))


  ;; grow-vec : Vector Nat Nat -> Vector/#f
  ;; Returns a new, larger vector if more space is needed, or #f if
  ;; the existing vector has enough capacity.
  (define (grow-vec vec n needed-free-space)
    (define cap (unsafe-vector*-length vec))
    (define needed-cap (unsafe-fx+ n needed-free-space))
    (cond [(unsafe-fx<= needed-cap cap) #f]
	  [else
	   ;; taken from Rust's raw_vec implementation
	   (let* ([new-cap (unsafe-fxmax (unsafe-fx* 2 cap) needed-cap)]
		  [new-cap (unsafe-fxmax new-cap MIN-CAPACITY)])
	     (vector*-extend vec new-cap 0))]))

  ;; vec-cas! : GVector Vector Vector -> Boolean
  ;; Installs new as gv's vec if gv's vec is still old.
  (define (vec-cas! gv old new)
    (unsafe-struct*-cas! gv 0 old new))

  ;; ensure-free-space! : GVector Nat -> Void
  ;; Ensures the gvector's vec has room for needed-free-space more
  ;; elements beyond the current n. Uses CAS to install the new vector
  ;; so that concurrent growers don't clobber each other.
  (define (ensure-free-space! gv needed-free-space)
    (let loop ()
      (define v (gvector-vec gv))
      (define new-v (grow-vec v (gvector-n gv) needed-free-space))
      (when new-v
	;; CAS: only install if vec hasn't been replaced by another thread.
	;; If CAS fails, another thread installed a different vec; retry
	;; to check if the new vec is big enough.
	(unless (vec-cas! gv v new-v)
	  (loop)))))

  ;; define/ensure-space! : binds n and v after ensuring the gvector
  ;; has room. Uses CAS on vec so concurrent ensure-space! calls
  ;; don't clobber each other.
  (define-syntax-rule (define/ensure-space! (n v) gv needed-free-space)
    (begin (define n (gvector-n gv))
	   (define v
	     (let loop ([v1 (gvector-vec gv)])
	       (define v2 (grow-vec v1 n needed-free-space))
	       (cond [(not v2) v1]   ; already big enough
		     ;; CAS: install new vec, retry if another thread changed it
		     [(vec-cas! gv v1 v2) v2]
		     [else (loop (gvector-vec gv))])))))

  ;; gvector-add! of one item, without checking that gv is a gvector
  (define (unsafe-gvector-add! gv item)
    (define/ensure-space! (n v) gv 1)
    ;; define/ensure-space! returned a v with room past the n it read
    (unsafe-vector*-set! v n item)
    (set-gvector-n! gv (unsafe-fx+ 1 n)))

  (define gvector-add!
    (case-lambda
      [(gv item)
       (check-gvector 'gvector-add! gv)
       (define/ensure-space! (n v) gv 1)
       (unsafe-vector*-set! v n item)
       (set-gvector-n! gv (unsafe-fx+ 1 n))]
      [(gv . items)
       (check-gvector 'gvector-add! gv)
       (define item-count (length items))
       (define/ensure-space! (n v) gv item-count)
       (for ([index (in-naturals n)] [item (in-list items)])
	 (unsafe-vector*-set! v index item))
       (set-gvector-n! gv (+ n item-count))])))

;; SLOW!
(define (gvector-insert! gv index item)
  ;; This does (n - index) redundant copies on resize, but that
  ;; happens rarely and I prefer the simpler code.
  (check-gvector 'gvector-insert! gv)
  (check-natural 'gvector-insert! index)
  (check-index 'gvector-insert! gv index #t)
  (define/ensure-space! (n v) gv 1)
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
  ;; n has already been decremented before calling trim!, so a smaller
  ;; vec still holds every element, provided n hasn't grown since we
  ;; read it. We re-read n before creating the new vec to abort if
  ;; concurrent adds have grown n past our target capacity. After CAS,
  ;; we check again and grow back if a concurrent add slipped through.
  (let loop ()
    (define n0 (gvector-n gv))
    (define v (gvector-vec gv))
    (define cap (vector-length v))
    (define new-cap
      (let shrink ([new-cap cap])
	(cond [(and (>= new-cap (* SHRINK-ON-FACTOR n0))
		    (>= (quotient new-cap SHRINK-BY-FACTOR) SHRINK-MIN))
	       (shrink (quotient new-cap SHRINK-BY-FACTOR))]
	      [else new-cap])))
    (when (< new-cap cap)
      ;; Re-read n: if concurrent adds grew n past new-cap, abort.
      (define n (gvector-n gv))
      (when (<= n new-cap)
	(define new-v (make-vector new-cap #f))
	(vector-copy! new-v 0 v 0 n)
	;; CAS: only install smaller vec if no other thread replaced vec
	(when (vec-cas! gv v new-v)
	  ;; Safety net: if a concurrent add pushed n past new-cap
	  ;; between our re-read and the CAS, grow back immediately.
	  (when (> (gvector-n gv) new-cap)
	    (ensure-free-space! gv 0)))))))

;; SLOW!
(define (gvector-remove! gv index)
  (check-gvector 'gvector-remove! gv)
  (check-natural 'gvector-remove! index)
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
  (let loop ()
    (define v (gvector-vec gv))
    (define n (gvector-n gv))
    (cond
      [(< index n)
       ;; n does not bound v: a concurrent add may have grown the gvector
       ;; between the two reads, and then v is the old, shorter vector.
       ;; Read again rather than past its end.
       (if (unsafe-fx< index (unsafe-vector*-length v))
           (unsafe-vector*-ref v index)
           (loop))]
      [(eq? default none)
       (raise-range-error 'gvector-ref "gvector" "" index gv 0 (sub1 n))]
      [(procedure? default) (default)]
      [else default])))

(define (gvector-append! gv gv*)
  (check-gvector 'gvector-append! gv)
  (check-gvector 'gvector-append! gv*)
  ;; gv* may be gv itself, whose vector the space check below may replace;
  ;; the vector read here still holds the same elements
  (define-values (v* n*) (gvector-vec+count gv*))
  (define/ensure-space! (n v) gv n*)
  (vector-copy! v n v* 0 n*)
  (set-gvector-n! gv (+ n n*)))

(define (gvector-append gv gv*)
  (check-gvector 'gvector-append gv)
  (check-gvector 'gvector-append gv*)
  (define-values (v n) (gvector-vec+count gv))
  (define-values (v* n*) (gvector-vec+count gv*))
  ;; retain the spare capacity of gv*
  (define gv0 (make-gvector #:capacity (+ n (vector-length v*))))
  (define v0 (gvector-vec gv0))
  (vector-copy! v0 0 v 0 n)
  (vector-copy! v0 n v* 0 n*)
  (set-gvector-n! gv0 (+ n n*))
  gv0)


;; gvector-set! with index = |gv| is interpreted as gvector-add!
(define (gvector-set! gv index item)
  (check-gvector 'gvector-set! gv)
  (check-natural 'gvector-set! index)
  (let loop ()
    (define v (gvector-vec gv))
    (define n (gvector-n gv))
    (cond
      [(< index n)
       ;; as in gvector-ref, n does not bound v; write into the vector
       ;; that holds index, never past the end of an old one
       (if (unsafe-fx< index (unsafe-vector*-length v))
           (unsafe-vector*-set! v index item)
           (loop))]
      [(= index n) (unsafe-gvector-add! gv item)]
      [else (raise-range-error 'gvector-set! "gvector" "" index gv 0 n)])))

;; creates a snapshot vector
(define (gvector->vector gv)
  (check-gvector 'gvector->vector gv)
  (define-values (v n) (gvector-vec+count gv))
  (vector*-copy v 0 n))

(define (gvector->list gv)
  (check-gvector 'gvector->list gv)
  (vector->list (gvector->vector gv)))

;; constructs a gvector
(define (vector->gvector v)
  (unless (vector? v)
    (raise-argument-error* 'vector->gvector 'data/gvector "vector?" v))
  (define lv (vector-length v))
  (define gv (make-gvector #:capacity (max lv DEFAULT-CAPACITY)))
  (define nv (gvector-vec gv))
  (vector-copy! nv 0 v)
  (set-gvector-n! gv lv)
  gv)

(define (list->gvector v)
  (unless (list? v)
    (raise-argument-error* 'list->gvector 'data/gvector "list?" v))
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

;; The vector and the number of elements in it: at most n, and never more
;; than the vector holds, since n does not bound a vector read before it
;; (see gvector-ref).
(define (gvector-vec+count gv)
  (define v (gvector-vec gv))
  (values v (unsafe-fxmin (gvector-n gv) (unsafe-vector*-length v))))

(define-sequence-syntax in-gvector*
  (lambda () #'in-gvector)
  (lambda (stx)
    (syntax-case stx ()
      [[(var) (in-gv gv-expr)]
       (with-syntax ([gv-expr-c (wrap-expr/c #'gvector? #'gv-expr #:macro #'in-gv)])
         (syntax/loc stx
           [(var)
            ;; vec and n are read again at every step, so that the loop sees
            ;; changes the body makes, as documented; n does not bound vec
            ;; (see gvector-ref), so the guard tests the index against both
            (:do-in ([(gv) gv-expr-c])
                    (void) ;; outer-check; handled by contract
                    ([index 0] [vec (gvector-vec gv)] [n (gvector-n gv)]) ;; loop bindings
                    (and (unsafe-fx< index n) (unsafe-fx< index (unsafe-vector*-length vec))) ;; pos-guard
                    ([(var) (unsafe-vector*-ref vec index)]) ;; inner bindings
                    #t ;; pre-guard
                    #t ;; post-guard
                    ((unsafe-fx+ 1 index) (gvector-vec gv) (gvector-n gv)))]))]
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
     #'(for*/gvector #:capacity DEFAULT-CAPACITY (clause ...) . body)]
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
 gvector-append
 gvector-append!
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
