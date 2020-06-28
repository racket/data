#lang racket

(require data/iheap
         data/iheap2
         data/iheap3)

;;;; Using three priority queues with indexed heaps.

;;;; iheap:  exposes opaque nodes.
;;;; iheap2: exposes indices.
;;;; iheap3: uses hash table (delayed initialization)

(define-syntax-rule (time+memory body ...)
  (begin
    (collect-garbage)
    (collect-garbage)
    (collect-garbage)
    (define pre (current-memory-use))
    (begin0 (time body ...)
      (let ([post (current-memory-use)])
        (printf "memory use: ~a\n" (- post pre))))))


(for ([N (in-list '(1000 100000 1000000 10000000))])
  (printf "\n\nN=~a\n" N)
  (define lst (build-list N (λ (i) (random (expt 2 31)))))
  (define sorted (sort lst <))

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
       (define h1elts (iheap-add-all! h1 elts))
       (define h2elts (iheap-add-all! h2 elts))
       (for ([h-elt (in-list h1elts)])
         (set-element-h1-node! (iheap-node-key h-elt) h-elt))
       (for ([h-elt (in-list h2elts)])
         (set-element-h2-node! (iheap-node-key h-elt) h-elt)))

      ; Remove min for h1, and remove same element in h2
      (displayln "*** Remove elements")
      (time+memory
       (for/list ([n (in-range N)])
         (define a (iheap-min h1))
         (iheap-remove-min! h1)
         (iheap-remove! h2 (element-h2-node a))
         (element-val a)))))
  (unless (equal? lres1 sorted)
    (error "iheap produced wrong result" lres1))


  ;;; Indexed heaps with getter and setter so the user keeps track of the indices.
  ;;; Indices are not opaque.
  (displayln "\n* iheap2 (visible indices)")
  (define lres2
    (let ()
      (struct element (val [h1-idx #:mutable] [h2-idx #:mutable])
        #:transparent)
      (define h1 (make-iheap2 (lambda (e1 e2) (< (element-val e1) (element-val e2)))
                              #:set-index! set-element-h1-idx!
                              #:get-index element-h1-idx))
      (define h2 (make-iheap2 (lambda (e1 e2) (> (element-val e1) (element-val e2)))
                              #:set-index! set-element-h2-idx!
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
  (unless (equal? lres2 sorted)
    (error "iheap2 produced wrong result"))

  ;; iheap3
  (displayln "\n* iheap3 (internal hash table)")
  (define lres3
    (let ()
      (struct element (val) #:transparent)
      (define h1 (make-iheap3 (lambda (e1 e2) (< (element-val e1) (element-val e2)))))
      (define h2 (make-iheap3 (lambda (e1 e2) (> (element-val e1) (element-val e2)))))

      (define elts (map (λ (x) (element x)) lst))

      ;; Add nodes to both heaps. Tracking is automatic.
      (displayln "*** Add elements")
      (time+memory
       (iheap3-add-all! h1 elts)
       (iheap3-add-all! h2 elts))

      ; Remove min for h1, and remove same element in h2
      (displayln "*** Remove elements")
      (time+memory
       (for/list ([n (in-range N)])
         (define a (iheap3-min h1))
         (iheap3-remove-min! h1)
         (iheap3-remove! h2 a)
         (element-val a)))))
  (unless (equal? lres3 sorted)
    (error "iheap3 produced wrong result"))

  ;; iheap3 forced first removal
  (displayln "\n* iheap3 with early get-index")
  (define lres3b
    (let ()
      (struct element (val) #:transparent)
      (define h1 (make-iheap3 (lambda (e1 e2) (< (element-val e1) (element-val e2)))))
      (define h2 (make-iheap3 (lambda (e1 e2) (> (element-val e1) (element-val e2)))))

      (define elts (map (λ (x) (element x)) lst))

      ;; Add nodes to both heaps. Tracking is automatic.
      (displayln "*** Add elements")
      (let ([x (first elts)])
        (iheap3-add! h1 x)
        (iheap3-remove! h1 x)
        (iheap3-add! h2 x)
        (iheap3-remove! h2 x))
      (time+memory
       (iheap3-add-all! h1 elts)
       (iheap3-add-all! h2 elts))

      ; Remove min for h1, and remove same element in h2
      (displayln "*** Remove elements")
      (time+memory
       (for/list ([n (in-range N)])
         (define a (iheap3-min h1))
         (iheap3-remove-min! h1)
         (iheap3-remove! h2 a)
         (element-val a)))))
  (unless (equal? lres3b sorted)
    (error "iheap3b produced wrong result"))

  ;; iheap3 w/o wrapper
  (displayln "\n* iheap3 w/o wrapper")
  (define lres3*
    (let ()
      (define h1 (make-iheap3 <))
      (define h2 (make-iheap3 >))

      (define elts lst)

      ;; Add nodes to both heaps. Tracking is automatic.
      (displayln "*** Add elements")
      (time+memory
       (iheap3-add-all! h1 elts)
       (iheap3-add-all! h2 elts))

      ; Remove min for h1, and remove same element in h2
      (displayln "*** Remove elements")
      (time+memory
       (for/list ([n (in-range N)])
         (define a (iheap3-min h1))
         (iheap3-remove-min! h1)
         (iheap3-remove! h2 a)
         (values a)))))
  (unless (equal? lres3* sorted)
    (error "iheap3 (w/o wrapper) produced wrong result" lres3*))

  (void))
