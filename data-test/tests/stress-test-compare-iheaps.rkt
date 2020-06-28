#lang racket

(require data/iheap
         data/iheap2
         racket/unsafe/ops)

;;;; Using two priority queues with indexed heaps.

;;;; iheap:  exposes opaque nodes.
;;;; iheap2: exposes indices.

(define-syntax-rule (time+memory body ...)
  (begin
    (collect-garbage)
    (collect-garbage)
    (collect-garbage)
    (define pre (current-memory-use))
    (time body ...)
    #;(collect-garbage) ; don't do that, it may collect things that were created before
    #;(collect-garbage)
    #;(collect-garbage)
    (define post (current-memory-use))
    (printf "memory use: ~a\n" (- post pre))))


(for ([N (in-list '(1000 100000 1000000 10000000))])
  (printf "\n\nN=~a\n" N)
  (define lst (build-list N (λ (i) (random (expt 2 31)))))
  ;;; Indexed heaps with internal nodes.
  ;;; The user must keep the *nodes* returned by iheap-add-all!
  ;;; in the same structure containing the user's values.
  ;;; Nodes are opaque.
  (displayln "\n* iheap (opaque)")
  (define lres1
    (let ()
      (struct element (val [h1-node #:mutable] [h2-node #:mutable])
        #:transparent)
      (define h1 (make-iheap (lambda (e1 e2) (< (element-val e1) (element-val e2)))))
      (define h2 (make-iheap (lambda (e1 e2) (> (element-val e1) (element-val e2)))))

      (define elts (map (λ (x) (element x #f #f)) lst))

      ;; Add the nodes to both heaps and track them in `element`.
      (displayln "*** Add elements")
      (time+memory
       (iheap-add-all! h1 elts #:set-node! set-element-h1-node!)
       (iheap-add-all! h2 elts #:set-node! set-element-h2-node!))

      ; Remove min for h1, and remove same element in h2
      (displayln "*** Remove elements")
      (time+memory
       (for/list ([n (in-range N)])
         (define a (iheap-min h1))
         (iheap-remove-min! h1)
         (iheap-remove! h2 (element-h2-node a))
         (element-val a)))))


  ;;; Indexed heaps with getter and setter so the user keeps track of the indices.
  ;;; Indices are not opaque.
  (displayln "\n* iheap2 (visible indices)")
  (define lres2
    (let ()
      (struct element (val [h1-idx #:mutable] [h2-idx #:mutable])
        #:transparent)
      (define (idx1-set! elt idx)
        (unsafe-struct*-set! elt 1 idx))
      (define (idx2-set! elt idx)
        (unsafe-struct*-set! elt 2 idx))
      (define h1 (make-iheap2 (lambda (e1 e2) (< (element-val e1) (element-val e2)))
                              #:set-index!
                              #;idx1-set! ; makes the GC blow up??
                              set-element-h1-idx!
                              #:get-index element-h1-idx))
      (define h2 (make-iheap2 (lambda (e1 e2) (> (element-val e1) (element-val e2)))
                              #:set-index!
                              #;idx2-set!
                              set-element-h2-idx!
                              #:get-index element-h2-idx))

      (define elts (map (λ (x) (element x #f #f)) lst))

      ;; Add nodes to both heaps. Tracking is automatic.
      (displayln "*** Add elements")
      (time+memory
       (iheap2-add-all! h1 elts)
       (iheap2-add-all! h2 elts))

      ; Remove min for h1, and remove same element in h2
      (displayln "*** Remove elements")
      (time+memory
       (for/list ([n (in-range N)])
         (define a (iheap2-min h1))
         (iheap2-remove-min! h1)
         (iheap2-remove! h2 a)
         (element-val a)))))

  (unless (equal? lres1 lres2)
    (error "Results are not equal!")))

