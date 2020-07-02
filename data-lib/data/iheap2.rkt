#lang racket/base
(require racket/contract/base
         racket/vector
         racket/match)

(define MIN-SIZE 4)

(struct iheap2 ([vec #:mutable] [count #:mutable] <=? set-index! get-index))
;; length(vec)/4 <= size <= length(vec), except size >= MIN-SIZE
;; size = next available index

;; A VT is a binary tree represented as a vector.

;; VT Index functions

(define (vt-root) 0)

(define (vt-parent n) (quotient (sub1 n) 2))
(define (vt-leftchild n) (+ (* n 2) 1))
(define (vt-rightchild n) (+ (* n 2) 2))

(define (vt-root? n) (zero? n))
(define (vt-leftchild? n) (odd? n))
(define (vt-rightchild? n) (even? n))

;; Operations

;; Instead of exchanging the parent and the child at each iteration,
;; only the child is updated, whereas the parent needs to be update
;; only once, after the loop.
(define (iheap2ify-up <=? vec n set-index!)
  (define n-key (vector-ref vec n))
  (define new-n
    (let loop ([n n])
      (cond
        [(vt-root? n) n]
        [else
         (define parent (vt-parent n))
         (define parent-key (vector-ref vec parent))
         (cond
           [(<=? parent-key n-key)
            n]
           [else
            (vector-set! vec n parent-key)
            (set-index! parent-key n)
            #;(vector-set! vec parent key) ; this can wait until after the loop
            (loop parent)])])))
  (unless (= n new-n)
    ; All parent updates are collapsed into this one:
    (vector-set! vec new-n n-key)
    (set-index! n-key new-n)))

;; See comment for iheap2ify-up
(define (iheap2ify-down <=? vec n size set-index!)
  (define n-key (vector-ref vec n))
  (define new-n
    (let loop ([n n])
      (define left (vt-leftchild n))
      (define right (vt-rightchild n))
      (cond
        [(< left size)
         (define left-key (vector-ref vec left))
         (define-values (child child-key)
           (if (< right size)
             (let ([right-key (vector-ref vec right)])
               (if (<=? left-key right-key)
                 (values left left-key)
                 (values right right-key)))
             (values left left-key)))
         (cond
           [(<=? n-key child-key) n]
           [else
            (vector-set! vec n child-key)
            #;(vector-set! vec child n-key) ; this can wait until after the loop
            (set-index! child-key n)
            (loop child)])]
        [else n])))
  (unless (= n new-n)
    (vector-set! vec new-n n-key)
    (set-index! n-key new-n)))

(define (fittest-block-size n)
  (max MIN-SIZE
       (expt 2 (integer-length (- n 1))
             #;(exact-ceiling (log (max 1 n) 2)))))

;; Grow the vector to the fittest 2^n ≥ new-size-min
(define (grow-vector v1 new-size-min)
  (define new-size
    (max (vector-length v1)
         (fittest-block-size new-size-min)))
  (define v2 (make-vector new-size #f))
  (vector-copy! v2 0 v1 0)
  v2)

;; Shrink to the fittest vector of size 2^n ≥ new-size-min
(define (shrink-vector v1 new-size-min)
  (define new-size (fittest-block-size new-size-min))
  (define v2 (make-vector new-size #f))
  (vector-copy! v2 0 v1 0 new-size)
  v2)

;; iheap2s

(define (make-iheap2 <=? #:set-index! set-index! #:get-index get-index)
  (iheap2 (make-vector MIN-SIZE #f) 0 <=? set-index! get-index))

(define (list->iheap2 <=? lst)
  (vector->iheap2 <=? (list->vector lst)))

(define (vector->iheap2 <=? vec0
                      [start 0] [end (vector-length vec0)]
                      #:set-index! set-index!
                      #:get-index get-index)
  (define size (- end start))
  (define vec (make-vector (fittest-block-size size) #f))
  ;; size <= length(vec)
  (vector-copy! vec 0 vec0 start end)
  (for ([n (in-range (sub1 size) -1 -1)])
    (iheap2ify-down <=? vec n size set-index!))
  (iheap2 vec size <=? set-index! get-index))

(define (iheap2-copy h)
  (match h
    [(iheap2 vec count <=? set-index! get-index)
     (iheap2 (vector-copy vec) count <=? set-index! get-index)]))

(define (iheap2-add! h . keys)
  (iheap2-add-all! h (list->vector keys)))

(define (iheap2-add-all! h keys)
  (let-values ([(keys keys-size)
                (cond [(list? keys)
                       (let ([keys-v (list->vector keys)])
                         (values keys-v (vector-length keys-v)))]
                      [(vector? keys)
                       (values keys (vector-length keys))]
                      [(iheap2? keys)
                       (values (iheap2-vec keys) (iheap2-count keys))])])
    (match h
      [(iheap2 vec size <=? set-index! _)
       (let* ([new-size (+ size keys-size)]
              [vec (if (> new-size (vector-length vec))
                       (let ([vec (grow-vector vec new-size)])
                         (set-iheap2-vec! h vec)
                         vec)
                       vec)])
         (vector-copy! vec size keys 0 keys-size)
         (for ([n (in-range size new-size)]
               [item (in-vector vec size)])
           (set-index! item n)
           (iheap2ify-up <=? vec n set-index!))
         (set-iheap2-count! h new-size))])))

(define (iheap2-min h)
  (match h
    [(iheap2 vec size <=? set-index! _)
     (when (zero? size)
       (error 'iheap2-min "empty iheap2"))
     (vector-ref vec 0)]))

(define (iheap2-remove-min! h)
  (when (zero? (iheap2-count h))
    (error 'iheap2-remove-min! "empty iheap2"))
  (iheap2-remove-index! h 0))

(define (iheap2-remove-index! h index)
  (match h
    [(iheap2 vec size <=? set-index! _)
     (unless (< index size)
       (if (zero? size)
           (error 'iheap2-remove-index!
                  "empty iheap2: ~s" index)
           (error 'iheap2-remove-index!
                  "index out of bounds [0,~s]: ~s" (sub1 size) index)))
     (define sub1-size (sub1 size))
     (define last-item (vector-ref vec sub1-size))
     (define removed-item (vector-ref vec index))
     (vector-set! vec index last-item)
     (vector-set! vec sub1-size #f)
     (when set-index!
       (set-index! last-item index)
       (set-index! removed-item #f))
     (cond
       [(= sub1-size index)
        ;; easy to remove the right-most leaf
        (void)]
       [(= index 0)
        ;; can only go down when at the root
        (iheap2ify-down <=? vec index sub1-size set-index!)]
       [else
        (define index-parent (vt-parent index))
        (cond
          ;; if we are in the right relationship with our parent,
          ;; try to iheap2ify down
          [(<=? (vector-ref vec index-parent) (vector-ref vec index))
           (iheap2ify-down <=? vec index sub1-size set-index!)]
          [else
           ;; otherwise we need to iheap2ify up
           (iheap2ify-up <=? vec index set-index!)])])
     (when (< MIN-SIZE size (quotient (vector-length vec) 4))
       (set-iheap2-vec! h (shrink-vector vec size)))
     (set-iheap2-count! h sub1-size)]))

;; Returns whether the removal was successful, that is,
;; whether v was indeed in the iheap2.
(define (iheap2-remove! h v)
  (define idx ((iheap2-get-index h) v))
  (cond [idx
         (unless (eq? v (vector-ref (iheap2-vec h) idx))
           (error "Key does not belong to iheap" v))
         (iheap2-remove-index! h idx)
         #t]
        [else #f]))

(define (in-iheap2 h)
  (in-iheap2/consume! (iheap2-copy h)))

(define (in-iheap2/consume! h)
  (make-do-sequence
   (lambda ()
     (values (lambda (_) (iheap2-min h))
             (lambda (_) (iheap2-remove-min! h) #t)
             #t
             (lambda (_) (> (iheap2-count h) 0))
             (lambda _ #t)
             (lambda _ #t)))))

;; --------

;; preferred order is (iheap2-sort vec <=?), but allow old order too
(define (iheap2-sort! x y)
  (cond [(and (vector? x) (procedure? y))
         (iheap2-sort!* x y)]
        [(and (vector? y) (procedure? x))
         (iheap2-sort!* y x)]
        [else
         (unless (vector? x)
           (raise-argument-error 'iheap2-sort! "vector?" x))
         (raise-argument-error 'iheap2-sort! "procedure?" y)]))

(define (iheap2-sort!* v <=?)
  ;; to get ascending order, need max-iheap2, so reverse comparison
  (define (>=? x y) (<=? y x))
  (define size (vector-length v))
  (for ([n (in-range (sub1 size) -1 -1)])
    (iheap2ify-down >=? v n size #f))
  (for ([last (in-range (sub1 size) 0 -1)])
    (let ([tmp (vector-ref v 0)])
      (vector-set! v 0 (vector-ref v last))
      (vector-set! v last tmp))
    (iheap2ify-down >=? v 0 last #f)))

(define (iheap2->vector h)
  (match h
    [(iheap2 vec size <=? set-index! _)
     (let ([v (vector-copy vec 0 size)])
       (iheap2-sort!* v <=?)
       v)]))

;; --------

(provide/contract
 [make-iheap2 (->* ((procedure-arity-includes/c 2)
                    #;(and/c (procedure-arity-includes/c 2)
                             (unconstrained-domain-> any/c))
                    #:set-index! (procedure-arity-includes/c 2)
                    #;(-> any/c (or/c #f exact-nonnegative-integer?) any/c)
                    #:get-index  (procedure-arity-includes/c 1)
                    #;(-> any/c (or/c #f exact-nonnegative-integer?)))
                 iheap2?)]
 [iheap2? (-> any/c boolean?)]
 [iheap2-count (-> iheap2? exact-nonnegative-integer?)]
 [iheap2-add! (->* (iheap2?) () #:rest list? void?)]
 [iheap2-add-all! (-> iheap2? (or/c list? vector? iheap2?) void?)]
 [iheap2-min (-> iheap2? any/c)]
 [iheap2-remove-min! (-> iheap2? void?)]
 [iheap2-remove! (->* (iheap2? any/c) boolean?)]
 [iheap2-remove-index! (-> iheap2? exact-nonnegative-integer? void?)]
 [vector->iheap2 (->* ((-> any/c any/c any/c)
                       vector?
                       #:set-index! (procedure-arity-includes/c 2)
                       #;(-> any/c exact-nonnegative-integer? any/c)
                       #:get-index (procedure-arity-includes/c 1)
                       #;(-> any/c (or/c #f exact-nonnegative-integer?)))
                      []
                    iheap2?)]
 [iheap2->vector (-> iheap2? vector?)]
 [iheap2-copy (-> iheap2? iheap2?)]

 [in-iheap2 (-> iheap2? sequence?)]
 [in-iheap2/consume! (-> iheap2? sequence?)])

(provide iheap2-sort!)

(module+ test-util
  (provide valid-iheap2?
           fittest-block-size
           MIN-SIZE)
  (define (valid-iheap2? a-iheap2)
    (match a-iheap2
      [(iheap2 vec size <=? set-index! _)
       (let loop ([i 0]
                  [parent -inf.0])
         (cond
           [(< i size)
            (define this (vector-ref vec i))
            (and (<=? parent this)
                 (loop (vt-leftchild i) this)
                 (loop (vt-rightchild i) this))]
           [else #t]))])))
