#lang racket

(require (file "../../data-lib/data/iheap.rkt")
         (file "../../data-lib/data/iheap2.rkt")
         (file "../../data-lib/data/iheap3.rkt")
         #;data/iheap
         #;data/iheap2
         #;data/iheap3
         #;racket/places)

;;;; Using two priority queues with indexed heaps.

;;;; iheap:  exposes opaque nodes.
;;;; iheap2: exposes indices.
;;;; iheap3: uses hash table (delayed initialization)

(define-syntax-rule (time+memory body ...)
  (let ()
    (collect-garbage)
    (collect-garbage)
    (collect-garbage)
    (define pre (current-memory-use))
    (begin0 (time body ...)
      (let ([post (current-memory-use)])
        (printf "memory use: ~a\n" (- post pre))))))

(define-syntax-rule (remove-elements [N h1 h2] [ha hb] body ... val)
  (begin
    ; Remove min for h1, and remove same element in h2
    (displayln "*** Remove elements")
    (time+memory
     (for/fold ([ha h1] [hb h2] [res '()] #:result res)
               ([n (in-range N)])
       body ...
       (values hb ha (cons val res))))))

#; ; Remove from the same heap all the time
(define-syntax-rule (remove-elements [N h1 h2] body ... val)
  (begin
    ; Remove min for h1, and remove same element in h2
    (displayln "*** Remove elements")
    (time+memory
     (for/fold ([ha h1] [hb h2] [res '()] #:result res)
               ([n (in-range N)])
       body ...
       (values ha hb (cons val res))))))

;;; Indexed heaps with internal nodes.
;;; The user must keep the *nodes* returned by iheap-add-all!
;;; in the same structure containing the user's values.
;;; Nodes are opaque.
(define (run-iheap lst)
  (define N (length lst))
  (displayln "\n* iheap (opaque)")
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

  (remove-elements
   [N h1 h2] [ha hb]
   (define a (iheap-min ha))
   (iheap-remove-min! ha)
   (iheap-remove! hb (element-h2-node a))
   (element-val a)))

;;; Indexed heaps with getter and setter so the user keeps track of the indices.
;;; Indices are not opaque.
(define (run-iheap2 lst)
  (define N (length lst))
  (displayln "\n* iheap2 (visible indices)")
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

  (remove-elements
   [N h1 h2] [ha hb]
   (define a (iheap2-min ha))
   (iheap2-remove-min! ha)
   (iheap2-remove! hb a)
   (element-val a)))

(define (run-iheap2+hash lst)
  (define N (length lst))
  (displayln "\n* iheap2 +hash")
  (define h1h (make-weak-hasheq))
  (define get1 (λ (obj) (hash-ref h1h obj)))
  (define set1 (λ (obj idx) (hash-set! h1h obj idx)))
  (define h2h (make-weak-hasheq))
  (define get2 (λ (obj) (hash-ref h2h obj)))
  (define set2 (λ (obj idx) (hash-set! h2h obj idx)))
  (struct element (val)
    #:transparent)
  (define h1 (make-iheap2 (lambda (e1 e2) (< (element-val e1) (element-val e2)))
                          #:set-index! set1
                          #:get-index get1))
  (define h2 (make-iheap2 (lambda (e1 e2) (> (element-val e1) (element-val e2)))
                          #:set-index! set2
                          #:get-index get2))

  (define elts (map (λ (x) (element x)) lst))

  ;; Add nodes to both heaps. Tracking is automatic.
  (displayln "*** Add elements")
  (time+memory
   (iheap2-add-all! h1 elts)
   (iheap2-add-all! h2 elts))

  (remove-elements
   [N h1 h2] [ha hb]
   (define a (iheap2-min ha))
   (iheap2-remove-min! ha)
   (iheap2-remove! hb a)
   (element-val a)))

;; iheap3 forced first removal
;; iheap3
(define (run-iheap3 lst)
  (define N (length lst))
  (displayln "\n* iheap3 (internal hash table)")
  (struct element (val) #:transparent)
  (define h1 (make-iheap3 (lambda (e1 e2) (< (element-val e1) (element-val e2)))))
  (define h2 (make-iheap3 (lambda (e1 e2) (> (element-val e1) (element-val e2)))))

  (define elts (map (λ (x) (element x)) lst))

  ;; Add nodes to both heaps. Tracking is automatic.
  (displayln "*** Add elements")
  (time+memory
   (iheap3-add-all! h1 elts)
   (iheap3-add-all! h2 elts))

  (remove-elements
   [N h1 h2] [ha hb]
   (define a (iheap3-min ha))
   (iheap3-remove-min! ha)
   (iheap3-remove! hb a)
   (element-val a)))

#;
(define (run-iheap3-early-get-index lst)
  (define N (length lst))
  (displayln "\n* iheap3 with early get-index")
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

  (remove-elements
   [N h1 h2] [ha hb]
   (define a (iheap3-min ha))
   (iheap3-remove-min! ha)
   (iheap3-remove! hb a)
   (element-val a)))

;; iheap3 w/o wrapper
(define (run-iheap3-w/o-wrapper lst)
  (define N (length lst))
  (displayln "\n* iheap3 w/o wrapper")
  (define h1 (make-iheap3 <))
  (define h2 (make-iheap3 >))

  (define elts lst)

  ;; Add nodes to both heaps. Tracking is automatic.
  (displayln "*** Add elements")
  (time+memory
   (iheap3-add-all! h1 elts)
   (iheap3-add-all! h2 elts))

  (remove-elements
   [N h1 h2] [ha hb]
   (define a (iheap3-min ha))
   (iheap3-remove-min! ha)
   (iheap3-remove! hb a)
   a))

(define-syntax-rule (make-fun-dict fun ...)
  (list (cons 'fun fun) ...))

(define fun-dict
  (make-fun-dict run-iheap run-iheap2
                 run-iheap2+hash
                 run-iheap3 #;run-iheap3-early-get-index run-iheap3-w/o-wrapper
                 ))

(provide main)
(define (main)
  (for ([N (in-list '(1000 100000 1000000 10000000))])
    (printf "\n\nN=~a\n" N)
    (define lst (build-list N (λ (i) (random (expt 2 31)))))
    #;(define sorted (sort lst <))

    (void
     (for/fold ([prev-lres #f])
               ([(fun-name fun) (in-dict fun-dict)])
       (define lres (fun lst))
       (when (and prev-lres (not (equal? lres prev-lres)))
         (error "result is different from the previous one" lres))
       lres))

    ;; Using places:
    #;
    (define ps
      (for/list ([fun-name (in-list (dict-keys fun-dict))])
        (define p
          (place/context ch
                 (displayln fun-name)
                 (define lres #f)
                 (define out
                   (with-output-to-string
                     (λ () (set! lres ((dict-ref fun-dict fun-name) lst)))))
                 (place-channel-put ch lres)
                 (place-channel-put ch out)))
        p))
    #;
    (for ([p (in-list ps)])
      (define lres (place-channel-get p))
      (define out (place-channel-get p))
      (displayln out)
      (unless (equal? lres sorted)
        (error "someone produced wrong result" lres)))

    (void)))