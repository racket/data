#lang racket/base
(require data/gvector
         racket/dict
         rackunit
         racket/serialize)

(test-equal? "gvector"
             (gvector->vector (gvector 1 2 3))
             '#(1 2 3))

(test-equal? "vector->gvector"
             (gvector->vector (vector->gvector #(1 2 3)))
             #(1 2 3))

(test-equal? "list->gvector"
             (gvector->vector (vector->gvector #(1 2 3)))
             #(1 2 3))

(test-equal? "gvector-add! (one)"
             (gvector->vector
              (let ([gv (make-gvector)])
                (for ([x '(1 2 3)])
                  (gvector-add! gv x))
                gv))
             '#(1 2 3))

(test-equal? "gvector-add! (multi)"
             (gvector->vector
              (let ([gv (make-gvector)])
                (gvector-add! gv 1 2 3)
                gv))
             '#(1 2 3))

(test-equal? "gvector-add! (lots)"
             (let ()
               (define g (gvector))
               (apply gvector-add! g (build-list 11 values))
               (gvector->vector g))
             (for/vector ([i 11]) i))

(test-equal? "gvector-insert! (one)"
             (let ()
               (define g (gvector 1 2 3 4 5 6 7 8 9 10))
               (gvector-insert! g 5 10)
               (gvector->vector g))
             #(1 2 3 4 5 10 6 7 8 9 10))

(test-equal? "gvector-insert (lots)"
             (let ()
               (define g (gvector 1 2 3 4))
               (for ([i (in-range 11)])
                 (gvector-insert! g (+ 2 i) i))
               (gvector->vector g))
             #(1 2 0 1 2 3 4 5 6 7 8 9 10 3 4))

(test-equal? "gvector-ref"
             (let ([gv (gvector 1 2 3)])
               ;; 3 valid refs + 1 not-found
               (for/list ([index '(0 1 2 3)])
                 (gvector-ref gv index #f)))
             '(1 2 3 #f))

(test-equal? "gvector-set! (in range)"
             (let ([gv (gvector 1 2 3)])
               (gvector-set! gv 1 'apple)
               (gvector->vector gv))
             '#(1 apple 3))

(test-equal? "gvector-set! as add"
             (let ([gv (gvector 1 2 3)])
               (gvector-set! gv 3 4)
               (gvector->vector gv))
             '#(1 2 3 4))

(test-equal? "gvector-remove! at end"
             (let ([gv (gvector 1 2 3)])
               (gvector-remove! gv 2)
               (gvector->vector gv))
             '#(1 2))

(test-equal? "gvector-remove! at beginning"
             (let ([gv (gvector 1 2 3)])
               (gvector-remove! gv 0)
               (gvector->vector gv))
             '#(2 3))

(test-equal? "gvector-remove-last!"
             (let ([gv (gvector 1 2 3)])
               (check-equal? (gvector-remove-last! gv) 3)
               (check-equal? (gvector-remove-last! gv) 2)
               (check-equal? (gvector-remove-last! gv) 1)
               (gvector->vector gv))
             '#())

(test-equal? "gvector-add and gvector-remove-last!"
             (let ([gv (gvector)])
               (gvector-add! gv 'rock)
               (gvector-add! gv 'paper)
               (check-equal? (gvector-remove-last! gv) 'paper)
               (gvector-add! gv 'scissor)
               (check-equal? (gvector-remove-last! gv) 'scissor)
               (check-equal? (gvector-remove-last! gv) 'rock)
               (gvector->vector gv))
             '#())

(test-equal? "gvector-count"
             (gvector-count (gvector 1 2 3))
             3)

(test-equal? "gvector-count / add"
             (let ([gv (gvector 1 2 3)])
               (gvector-add! gv 4 5 6)
               (gvector-count gv))
             6)

(test-equal? "in-gvector"
             (let ([gv (gvector 1 2 3)])
               (for/list ([x (in-gvector gv)]) x))
             '(1 2 3))

(test-equal? "in-gvector expression form"
             (let* ([gv (gvector 1 2 3)]
                    [gv-sequence (in-gvector gv)])
               (for/list ([x gv-sequence]) x))
             '(1 2 3))

(test-equal? "gvector as sequence"
             (let ([gv (gvector 1 2 3)])
               (for/list ([x gv]) x))
             '(1 2 3))

(test-equal? "for/gvector"
             (gvector->vector (for/gvector ([x '(1 2 3)]) x))
             '#(1 2 3))

(test-case "gvector-append and gvector-append!"
  (define a (gvector 1 2 3))
  (define b (gvector 4 5))
  (check-equal? (gvector->list (gvector-append a b)) '(1 2 3 4 5))
  (check-equal? (gvector->list a) '(1 2 3))
  (check-equal? (gvector->list b) '(4 5))
  (check-equal? (gvector-count (gvector-append (gvector) (gvector))) 0)
  (gvector-append! a b)
  (check-equal? (gvector->list a) '(1 2 3 4 5))
  (check-equal? (gvector->list b) '(4 5))
  (gvector-append! b b)
  (check-equal? (gvector->list b) '(4 5 4 5)))

(test-equal? "for*/gvector nests its clauses"
             (gvector->list (for*/gvector ([i 2] [j 3]) (list i j)))
             '((0 0) (0 1) (0 2) (1 0) (1 1) (1 2)))

(test-equal? "for/gvector and for*/gvector with #:capacity"
             (list (gvector->list (for/gvector #:capacity 100 ([i 3]) i))
                   (gvector->list (for*/gvector #:capacity 0 ([i 2] [j 2]) (+ i j))))
             '((0 1 2) (0 1 1 2)))

(test-case "a gvector made with a capacity of 0 grows"
  (define gv (make-gvector #:capacity 0))
  (for ([i 20]) (gvector-add! gv i))
  (check-equal? (gvector->list gv) (for/list ([i 20]) i)))

;; gvector-set! and gvector-ref read and write with unchecked vector
;; operations, so they must reject an index that is not a natural number
;; before using it.
(test-case "gvector-set! and gvector-ref reject indexes that are not naturals"
  (define gv (gvector 1 2 3))
  (for ([i (list -1 1.5 'a (expt 2 100))])
    (check-exn exn:fail:contract? (lambda () (gvector-set! gv i 'x)))
    (check-exn exn:fail:contract? (lambda () (gvector-ref gv i))))
  (check-equal? (gvector->vector gv) '#(1 2 3)))

;; in-gvector's fast path reads the gvector at every step, so it sees
;; changes that the body makes, as the documentation says.
(test-equal? "in-gvector sees a removal made while it runs"
             (let ([gv (gvector 0 1 2 3)])
               (for/list ([x (in-gvector gv)])
                 (when (eqv? x 1) (gvector-remove! gv 3))
                 x))
             '(0 1 2))
(test-equal? "in-gvector sees an add made while it runs"
             (let ([gv (gvector 0 1 2)])
               (for/list ([x (in-gvector gv)])
                 (when (eqv? x 1) (gvector-add! gv 9))
                 x))
             '(0 1 2 9))

(test-case "argument errors name the function"
  (check-exn #rx"vector->gvector" (lambda () (vector->gvector 5)))
  (check-exn #rx"list->gvector" (lambda () (list->gvector 5)))
  (for ([i (list -1 1.5)])
    (check-exn #rx"gvector-insert!" (lambda () (gvector-insert! (gvector 1 2) i 'x)))
    (check-exn #rx"gvector-remove!" (lambda () (gvector-remove! (gvector 1 2) i)))))

(test-case "gvector, lots of adds"
  (let ([gv (make-gvector)])
    (for ([x (in-range 0 1000)])
      (gvector-add! gv x))
    (for ([x (in-range 0 1000)])
      (check-equal? (gvector-ref gv x) x))
    (check-equal? (gvector-count gv) 1000)))

(test-equal? "gvector, dict-map"
             (dict-map (gvector 1 2 3) list)
             '((0 1) (1 2) (2 3)))
(test-equal? "gvector, dict-ref"
             (dict-ref (gvector 1 2 3) 0)
             1)

(test-equal? "gvector, dict-ref out of range"
             (dict-ref (gvector 1 2 3) 5 #f)
             #f)

(test-equal? "gvector, equals, empty"
             (gvector)
             (make-gvector #:capacity 50))

(test-case "gvector, equals"
  (let ([g1 (make-gvector)]
        [g2 (make-gvector)])
    (for ([x (in-range 1000)])
      (check-equal? g1 g2)
      (check-equal? (equal-hash-code g1) (equal-hash-code g2))
      (gvector-add! g1 x)
      (gvector-add! g2 x))))

(test-case "gvector, equals, w cycles"
  (let ([g1 (make-gvector)]
        [g2 (make-gvector)])
    (for ([x (in-range 10)])
      (check-equal? g1 g2)
      (check-equal? (equal-hash-code g1) (equal-hash-code g2))
      (gvector-add! g1 (if (zero? (modulo x 2)) g1 g2))
      (gvector-add! g2 (if (zero? (modulo x 3)) g1 g2)))))

(test-case "gvector, not equal, same length"
  (check-not-equal? (gvector 1) (gvector 2)))

(test-case "gvector, not equal, extension"
  (check-not-equal? (gvector 1) (gvector 1 2)))

(test-case "gvector on large list"
  (let ([g (apply gvector (for/list ([i 100]) i))])
    (check-pred gvector? g)
    (for ([i 100])
      (check-equal? (gvector-ref g i) i))))

(test-case "gvector remove all, shrinks"
  (let ([g (make-gvector)])
    (for ([i 100]) (gvector-add! g i))
    (for ([i 100])
      (gvector-remove-last! g))
    (check-equal? g (gvector))))

(test-equal? "gvector serialize"
            (gvector->vector (deserialize (serialize (gvector 1 2 3))))
            #(1 2 3))

(test-case "serialize non-atomic data"
  (let ()
    (define x (box #f))
    (define y (box #f))
    (define the-vec (deserialize (serialize (gvector x x y))))
    (check-eq? (gvector-ref the-vec 0)
               (gvector-ref the-vec 1))
    (check-not-eq? (gvector-ref the-vec 0)
                   (gvector-ref the-vec 2))))

(test-case "serialize-cycles"
  (let ()
    (define vec (make-gvector))
    (define other-vec (make-gvector))
    (gvector-add! vec vec)
    (gvector-add! vec other-vec)
    (deserialize (serialize vec))
    (check-eq? vec (gvector-ref vec 0))
    (check-not-eq? vec (gvector-ref vec 1))))
