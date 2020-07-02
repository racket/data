#lang racket/base
(require racket/contract/base
         racket/vector
         racket/match)

(define MIN-SIZE 4)

(struct iheap3 ([vec #:mutable] [count #:mutable] <=? [elt=>idx #:mutable]))
;; length(vec)/4 <= size <= length(vec), except size >= MIN-SIZE
;; size = next available index
;; elt=>idx : #f or Hasheq[Element => Nat], not initialized until used by
;;   get-index (that is, by heap-remove!)

;; If heap contains duplicate elements, then the hash will lose some.
;; Could detect, could handle duplicates (more complicated), or could
;; just warn user "don't do that".

;; Allow user to select hash type (hasheq vs hasheqv vs hash)?

;; A VT is a binary tree represented as a vector.

;; VT Index functions

(define (vt-root) 0)

(define (vt-parent n) (quotient (sub1 n) 2))
(define (vt-leftchild n) (+ (* n 2) 1))
(define (vt-rightchild n) (+ (* n 2) 2))

(define (vt-root? n) (zero? n))
(define (vt-leftchild? n) (odd? n))
(define (vt-rightchild? n) (even? n))

(define (set-index! elt=>idx k n)
  (when elt=>idx (hash-set! elt=>idx k n)))

(define (remove-index! elt=>idx k)
  (when elt=>idx (hash-remove! elt=>idx k)))

#;(define (get-index h k)
  (define (get-elt=>idx h)
    (match h
      [(iheap3 vec size <=? elt=>idx)
       (or elt=>idx
           (let ([elt=>idx (make-hasheq)])
             (for ([idx (in-range size)] [elt (in-vector vec)])
               (hash-set! elt=>idx elt idx))
             (set-iheap3-elt=>idx! h elt=>idx)
             elt=>idx))]))
  (hash-ref (get-elt=>idx h) k #f))

(define (get-index h k)
  (define elt=>idx
    (or (iheap3-elt=>idx h)
        (match h
          [(iheap3 vec size <=? elt=>idx)
           (let ([elt=>idx (make-hasheq)])
             (for ([idx (in-range size)] [elt (in-vector vec)])
               (hash-set! elt=>idx elt idx))
             (set-iheap3-elt=>idx! h elt=>idx)
             elt=>idx)])))
  (hash-ref elt=>idx k #f))

;; Operations

;; Instead of exchanging the parent and the child at each iteration,
;; only the child is updated, whereas the parent needs to be update
;; only once, after the loop.
(define (iheap3ify-up <=? vec n elt=>idx)
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
            (set-index! elt=>idx parent-key n)
            #;(vector-set! vec parent key) ; this can wait until after the loop
            (loop parent)])])))
  (unless (= n new-n)
    ; All parent updates are collapsed into this one:
    (vector-set! vec new-n n-key)
    (set-index! elt=>idx n-key new-n)))

;; See comment for iheap3ify-up
(define (iheap3ify-down <=? vec n size elt=>idx)
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
            (set-index! elt=>idx child-key n)
            (loop child)])]
        [else n])))
  (unless (= n new-n)
    (vector-set! vec new-n n-key)
    (set-index! elt=>idx n-key new-n)))

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

;; iheap3s

(define (make-iheap3 <=?)
  (iheap3 (make-vector MIN-SIZE #f) 0 <=? #f))

(define (list->iheap3 <=? lst)
  (vector->iheap3 <=? (list->vector lst)))

(define (vector->iheap3 <=? vec0
                      [start 0] [end (vector-length vec0)])
  (define size (- end start))
  (define vec (make-vector (fittest-block-size size) #f))
  ;; size <= length(vec)
  (vector-copy! vec 0 vec0 start end)
  (for ([n (in-range (sub1 size) -1 -1)])
    (iheap3ify-down <=? vec n size #f))
  (iheap3 vec size <=? #f))

(define (iheap3-copy h)
  (match h
    [(iheap3 vec count <=? _)
     ;; Should elt=>idx (if initialized) be copied over too?
     ;; Only worthwhile if heap-remove! will be used on new heap,
     ;; which it isn't in the in-heap use case.
     (iheap3 (vector-copy vec) count <=? #f)]))

(define (iheap3-add! h . keys)
  (iheap3-add-all! h (list->vector keys)))

(define (iheap3-add-all! h keys)
  (let-values ([(keys keys-size)
                (cond [(list? keys)
                       (let ([keys-v (list->vector keys)])
                         (values keys-v (vector-length keys-v)))]
                      [(vector? keys)
                       (values keys (vector-length keys))]
                      [(iheap3? keys)
                       (values (iheap3-vec keys) (iheap3-count keys))])])
    (match h
      [(iheap3 vec size <=? elt=>idx)
       (let* ([new-size (+ size keys-size)]
              [vec (if (> new-size (vector-length vec))
                       (let ([vec (grow-vector vec new-size)])
                         (set-iheap3-vec! h vec)
                         vec)
                       vec)])
         (vector-copy! vec size keys 0 keys-size)
         (for ([n (in-range size new-size)]
               [item (in-vector vec size)])
           (set-index! elt=>idx item n)
           (iheap3ify-up <=? vec n elt=>idx))
         (set-iheap3-count! h new-size))])))

(define (iheap3-min h)
  (match h
    [(iheap3 vec size <=? _)
     (when (zero? size)
       (error 'iheap3-min "empty iheap3"))
     (vector-ref vec 0)]))

(define (iheap3-remove-min! h)
  (when (zero? (iheap3-count h))
    (error 'iheap3-remove-min! "empty iheap3"))
  (iheap3-remove-index! h 0))

(define (iheap3-remove-index! h index)
  (match h
    [(iheap3 vec size <=? elt=>idx)
     (unless (< index size)
       (if (zero? size)
           (error 'iheap3-remove-index!
                  "empty iheap3: ~s" index)
           (error 'iheap3-remove-index!
                  "index out of bounds [0,~s]: ~s" (sub1 size) index)))
     (define sub1-size (sub1 size))
     (define last-item (vector-ref vec sub1-size))
     (define removed-item (vector-ref vec index))
     (vector-set! vec index last-item)
     (vector-set! vec sub1-size #f)
     (when elt=>idx
       (set-index! elt=>idx last-item index)
       (remove-index! elt=>idx removed-item))
     (cond
       [(= sub1-size index)
        ;; easy to remove the right-most leaf
        (void)]
       [(= index 0)
        ;; can only go down when at the root
        (iheap3ify-down <=? vec index sub1-size elt=>idx)]
       [else
        (define index-parent (vt-parent index))
        (cond
          ;; if we are in the right relationship with our parent,
          ;; try to iheap3ify down
          [(<=? (vector-ref vec index-parent) (vector-ref vec index))
           (iheap3ify-down <=? vec index sub1-size elt=>idx)]
          [else
           ;; otherwise we need to iheap3ify up
           (iheap3ify-up <=? vec index elt=>idx)])])
     (when (< MIN-SIZE size (quotient (vector-length vec) 4))
       (set-iheap3-vec! h (shrink-vector vec size)))
     (set-iheap3-count! h sub1-size)]))

;; Returns whether the removal was successful, that is,
;; whether v was indeed in the iheap3.
(define (iheap3-remove! h v)
  (define idx (get-index h v))
  (cond [idx
         (unless (eq? v (vector-ref (iheap3-vec h) idx))
           (error "Key does not belong to iheap" v))
         (iheap3-remove-index! h idx)
         #t]
        [else #f]))

(define (in-iheap3 h)
  (in-iheap3/consume! (iheap3-copy h)))

(define (in-iheap3/consume! h)
  (make-do-sequence
   (lambda ()
     (values (lambda (_) (iheap3-min h))
             (lambda (_) (iheap3-remove-min! h) #t)
             #t
             (lambda (_) (> (iheap3-count h) 0))
             (lambda _ #t)
             (lambda _ #t)))))

;; --------

;; preferred order is (iheap3-sort vec <=?), but allow old order too
(define (iheap3-sort! x y)
  (cond [(and (vector? x) (procedure? y))
         (iheap3-sort!* x y)]
        [(and (vector? y) (procedure? x))
         (iheap3-sort!* y x)]
        [else
         (unless (vector? x)
           (raise-argument-error 'iheap3-sort! "vector?" x))
         (raise-argument-error 'iheap3-sort! "procedure?" y)]))

(define (iheap3-sort!* v <=?)
  ;; to get ascending order, need max-iheap3, so reverse comparison
  (define (>=? x y) (<=? y x))
  (define size (vector-length v))
  (for ([n (in-range (sub1 size) -1 -1)])
    (iheap3ify-down >=? v n size #f))
  (for ([last (in-range (sub1 size) 0 -1)])
    (let ([tmp (vector-ref v 0)])
      (vector-set! v 0 (vector-ref v last))
      (vector-set! v last tmp))
    (iheap3ify-down >=? v 0 last #f)))

(define (iheap3->vector h)
  (match h
    [(iheap3 vec size <=? _)
     (let ([v (vector-copy vec 0 size)])
       (iheap3-sort!* v <=?)
       v)]))

;; --------

(provide/contract
 [make-iheap3 (->* ((procedure-arity-includes/c 2)
                    #;(and/c (procedure-arity-includes/c 2)
                             (unconstrained-domain-> any/c)))
                 iheap3?)]
 [iheap3? (-> any/c boolean?)]
 [iheap3-count (-> iheap3? exact-nonnegative-integer?)]
 [iheap3-add! (->* (iheap3?) () #:rest list? void?)]
 [iheap3-add-all! (-> iheap3? (or/c list? vector? iheap3?) void?)]
 [iheap3-min (-> iheap3? any/c)]
 [iheap3-remove-min! (-> iheap3? void?)]
 [iheap3-remove! (->* (iheap3? any/c) boolean?)]
 [iheap3-remove-index! (-> iheap3? exact-nonnegative-integer? void?)]
 [vector->iheap3 (->* ((procedure-arity-includes/c 2)
                       #;(-> any/c any/c any/c)
                       vector?)
                      []
                    iheap3?)]
 [iheap3->vector (-> iheap3? vector?)]
 [iheap3-copy (-> iheap3? iheap3?)]

 [in-iheap3 (-> iheap3? sequence?)]
 [in-iheap3/consume! (-> iheap3? sequence?)])

(provide iheap3-sort!)

(module+ test-util
  (provide valid-iheap3?
           fittest-block-size
           MIN-SIZE)
  (define (valid-iheap3? a-iheap3)
    (match a-iheap3
      [(iheap3 vec size <=? _)
       (let loop ([i 0]
                  [parent -inf.0])
         (cond
           [(< i size)
            (define this (vector-ref vec i))
            (and (<=? parent this)
                 (loop (vt-leftchild i) this)
                 (loop (vt-rightchild i) this))]
           [else #t]))])))
