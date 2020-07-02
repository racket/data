#lang racket/base
(require racket/contract/base
         racket/vector
         racket/match)

(define MIN-SIZE 4)

(struct iheap ([vec #:mutable] [count #:mutable] <=?))
;; length(vec)/4 <= size <= length(vec), except size >= MIN-SIZE
;; size = next available index

(struct node (elt [index #:mutable]))
(define set-index! set-node-index!)
(define get-index node-index)

(define iheap-node-key node-elt)

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
(define (iheapify-up <=? vec n)
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

;; See comment for iheapify-up
(define (iheapify-down <=? vec n size)
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
            (set-index! child-key n)
            #;(vector-set! vec child n-key) ; this can wait until after the loop
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

;; Heaps

(define (make-iheap <=?)
  (iheap (make-vector MIN-SIZE #f)
         0
         (λ (a b) (<=? (node-elt a) (node-elt b)))))

(define (list->iheap <=? lst)
  (vector->iheap <=? (list->vector lst)))

(define (vector->iheap <=? vec0 [start 0] [end (vector-length vec0)])
  (define size (- end start))
  (define vec (make-vector (fittest-block-size size) #f))
  ;; size <= length(vec)
  (vector-copy! vec 0 vec0 start end)
  (for ([n (in-range (sub1 size) -1 -1)])
    (iheapify-down <=? vec n size))
  (iheap vec size <=?))


(define (iheap-copy h)
  (error "NEEDS UPDATING")
  (match h
    [(iheap vec count <=?)
     ; CAN'T JUST COPY VEC
     (iheap (vector-copy vec) count <=?)]))

(define (iheap-add! h . keys)
  (iheap-add-all! h (list->vector keys)))

(define (iheap-add-all! h keys)
  (let-values ([(keys keys-size)
                (cond [(list? keys)
                       (let ([keys-v (list->vector keys)])
                         (values keys-v (vector-length keys-v)))]
                      [(vector? keys)
                       (values keys (vector-length keys))]
                      #;[(heap? keys) ; no access to heap-vec
                       (values (heap-vec keys) (heap-count keys))]
                      #;[(iheap? keys)
                         ; must extract the keys from the nodes
                       (values (iheap-vec keys) (iheap-count keys))])])
    (match h
      [(iheap vec size <=?)
       (let* ([new-size (+ size keys-size)]
              [vec (if (> new-size (vector-length vec))
                     (let ([vec (grow-vector vec new-size)])
                       (set-iheap-vec! h vec)
                       vec)
                     vec)])
         #;(vector-copy! vec size keys 0 keys-size)
         (define nodes
           (for/list ([n (in-range size new-size)]
                      [item (in-vector keys size)])
             (define nd (node item n))
             (vector-set! vec n nd)
             (iheapify-up <=? vec n)
             nd))
         ; A little risky to do that afterward only,
         ; but iheapify-up doesn't use.
         (set-iheap-count! h new-size) 
         nodes)])))

(define (iheap-min h)
  (match h
    [(iheap vec size <=?)
     (when (zero? size)
       (error 'iheap-min "empty iheap"))
     (node-elt (vector-ref vec 0))]))

(define (iheap-remove-min! h)
  (when (zero? (iheap-count h))
    (error 'iheap-remove-min! "empty iheap"))
  (iheap-remove-index! h 0))

(define (iheap-remove-index! h index)
  (match h
    [(iheap vec size <=?)
     (unless (< index size)
       (if (zero? size)
           (error 'iheap-remove-index!
                  "empty iheap: ~s" index)
           (error 'iheap-remove-index!
                  "index out of bounds [0,~s]: ~s" (sub1 size) index)))
     (define sub1-size (sub1 size))
     (define last-item (vector-ref vec sub1-size))
     (define removed-item (vector-ref vec index))
     (vector-set! vec index last-item)
     (vector-set! vec sub1-size #f)
     (set-index! last-item index)
     (set-index! removed-item #f)
     (cond
       [(= sub1-size index)
        ;; easy to remove the right-most leaf
        (void)]
       [(= index 0)
        ;; can only go down when at the root
        (iheapify-down <=? vec index sub1-size)]
       [else
        (define index-parent (vt-parent index))
        (cond
          ;; if we are in the right relationship with our parent,
          ;; try to iheapify down
          [(<=? (vector-ref vec index-parent) (vector-ref vec index))
           (iheapify-down <=? vec index sub1-size)]
          [else
           ;; otherwise we need to iheapify up
           (iheapify-up <=? vec index)])])
     (when (< MIN-SIZE size (quotient (vector-length vec) 4))
       (set-iheap-vec! h (shrink-vector vec size)))
     (set-iheap-count! h sub1-size)]))


;; Returns whether the removal was successful, that is,
;; whether v was indeed in the iheap.
(define (iheap-remove! h nd)
  (define idx (get-index nd))
  (cond [idx
         (unless (eq? nd (vector-ref (iheap-vec h) idx))
           (error "Node does not belong to iheap" nd))
         (iheap-remove-index! h idx)
         #t]
        [else #f]))

(define (in-iheap h)
  (in-iheap/consume! (iheap-copy h)))

(define (in-iheap/consume! h)
  (make-do-sequence
   (lambda ()
     (values (lambda (_) (iheap-min h))
             (lambda (_) (iheap-remove-min! h) #t)
             #t
             (lambda (_) (> (iheap-count h) 0))
             (lambda _ #t)
             (lambda _ #t)))))

;; --------

;; preferred order is (iheap-sort vec <=?), but allow old order too
(define (iheap-sort! x y)
  (cond [(and (vector? x) (procedure? y))
         (iheap-sort!* x y)]
        [(and (vector? y) (procedure? x))
         (iheap-sort!* y x)]
        [else
         (unless (vector? x)
           (raise-argument-error 'iheap-sort! "vector?" x))
         (raise-argument-error 'iheap-sort! "procedure?" y)]))

(define (iheap-sort!* v <=?)
  ;; to get ascending order, need max-iheap, so reverse comparison
  (define (>=? x y) (<=? y x))
  (define size (vector-length v))
  (for ([n (in-range (sub1 size) -1 -1)])
    (iheapify-down >=? v n size #f))
  (for ([last (in-range (sub1 size) 0 -1)])
    (let ([tmp (vector-ref v 0)])
      (vector-set! v 0 (vector-ref v last))
      (vector-set! v last tmp))
    (iheapify-down >=? v 0 last #f)))

(define (iheap->vector h)
  (match h
    [(iheap vec size <=?)
     (let ([v (vector-copy vec 0 size)])
       (iheap-sort!* v <=?)
       v)]))

;; --------

(provide/contract
 [make-iheap (->* ((procedure-arity-includes/c 2)
                   #;(and/c (procedure-arity-includes/c 2)
                            (unconstrained-domain-> any/c)))
                 iheap?)]
 [iheap? (-> any/c boolean?)]
 [iheap-node-key (-> node? any/c)]
 [iheap-count (-> iheap? exact-nonnegative-integer?)]
 [iheap-add! (->* (iheap?) () #:rest list? list?)]
 [iheap-add-all! (-> iheap? (or/c list? vector? iheap?) list?)]
 [iheap-min (-> iheap? any/c)]
 [iheap-remove-min! (-> iheap? void?)]
 [iheap-remove! (->* (iheap? node?)  boolean?)]
 #;[iheap-remove-index! (-> iheap? exact-nonnegative-integer? void?)]
 [vector->iheap (->* ((-> any/c any/c any/c) vector?)
                    iheap?)]
 [iheap->vector (-> iheap? vector?)]
 [iheap-copy (-> iheap? iheap?)]

 [in-iheap (-> iheap? sequence?)]
 [in-iheap/consume! (-> iheap? sequence?)])

(provide iheap-sort!)

(module+ test-util
  (provide valid-iheap?
           fittest-block-size
           MIN-SIZE)
  (define (valid-iheap? a-iheap)
    (match a-iheap
      [(iheap vec size <=?)
       (let loop ([i 0]
                  [parent -inf.0])
         (cond
           [(< i size)
            (define this (vector-ref vec i))
            (and (<=? parent this)
                 (loop (vt-leftchild i) this)
                 (loop (vt-rightchild i) this))]
           [else #t]))])))
