#lang racket

(require data/iheap
         data/iheap2)

;;;; Using two priority queues with indexed heaps.

;;;; iheap:  exposes opaque nodes.
;;;; iheap2: exposes indices.


;;;; Results:
;;;; N = 100000
;;;; cpu time: 153 real time: 152 gc time: 0
;;;; cpu time: 243 real time: 243 gc time: 0
;;;; N = 1000000
;;;; iheap:  cpu time: 3461 real time: 3457 gc time: 258
;;;; iheap2: cpu time: 3800 real time: 3797 gc time: 176
;;;; N = 10000000
;;;; iheap:  cpu time: 76872 real time: 76792 gc time: 19813
;;;; iheap2: cpu time: 67995 real time: 67937 gc time: 14472

;;;; As expected iheap2 is faster than iheap, in particular thanks to less GC,
;;;; but it also appears than iheap2 has a hidden cost. I suspect it's contract-checking
;;;; of `set-index!` which checks `element?`,
;;;; whereas for iheap the nodes are in the same module, avoiding the checks.

;;;; The interface for iheap2 is currently nicer when using multiple queues,
;;;; but this could be remedied in iheap by using a #:set-heap-node! argument
;;;; to iheap-add-all!. This would also avoid returning a list.

(define N 100000)
(define lst (build-list N (λ (i) (random (expt 2 31)))))

;;; Indexed heaps with internal nodes.
;;; The user must keep the *nodes* returned by iheap-add-all!
;;; in the same structure containing the user's values.
;;; Nodes are opaque.
(define lres1
  (let ()
    (struct element (val [h1-node #:mutable] [h2-node #:mutable])
      #:transparent)
    (define h1 (make-iheap (lambda (e1 e2) (< (element-val e1) (element-val e2)))))
    (define h2 (make-iheap (lambda (e1 e2) (> (element-val e1) (element-val e2)))))

    (define elts (map (λ (x) (element x #f #f)) lst))

    ;; Add the nodes to both heaps and track them in `element`.
    (define h1elts (iheap-add-all! h1 elts))
    (define h2elts (iheap-add-all! h2 elts))
    (for ([h-elt (in-list h1elts)])
      (set-element-h1-node! (iheap-node-key h-elt) h-elt))
    (for ([h-elt (in-list h2elts)])
      (set-element-h2-node! (iheap-node-key h-elt) h-elt))

    (collect-garbage)
    (collect-garbage)
    (time
     (for/list ([n (in-range N)])
       (define a (iheap-min h1))
       (iheap-remove-min! h1)
       (iheap-remove! h2 (element-h2-node a))
       (element-val a)))))


;;; Indexed heaps with getter and setter so the user keeps track of the indices.
;;; Indices are not opaque.
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
    (iheap2-add-all! h1 elts)
    (iheap2-add-all! h2 elts)

    (collect-garbage)
    (collect-garbage)
    (time
     (for/list ([n (in-range N)])
       (define a (iheap2-min h1))
       (iheap2-remove-min! h1)
       (iheap2-remove! h2 a)
       (element-val a)))))

(unless (equal? lres1 lres2)
  (error "Results are not equal!"))

