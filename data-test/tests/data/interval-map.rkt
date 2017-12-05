#lang racket/base
(require racket/dict
         data/interval-map)
(provide (all-defined-out))

(begin
  (define KEY-MAX 5000)
  (define VALUE-MAX 5000)
  (define INTERVAL-CT 2000)
  (define CONTRACT-CT 50)
  (define EXPAND-CT 50)
  (define SPREAD 20))

#;
(begin
  (define KEY-MAX 40)
  (define VALUE-MAX 50)
  (define INTERVAL-CT 10)
  (define CONTRACT-CT 5)
  (define EXPAND-CT 5)
  (define SPREAD 2))

(define (check-equal? x y [msg #f]) ;; rackunit check-equal? is apparently slow
  (unless (equal? x y)
    (error 'check-equal? "not equal~a:\n~e\n~e"
           (if msg (string-append " (" msg ")") "") x y)))


(define (check-im im)
  (for/fold ([last -inf.0]) ([(k v) (in-dict im)])
    (unless (>= (car k) last)
      (error 'check-im "overlapping intervals: ~s, ~s" last k))
    (cdr k)))

;; ----

(define vec (make-vector KEY-MAX 0))
(define im (make-interval-map))

(define (last-key) (vector-length vec))

(define (vec-contract! a b)
  (define n (- (vector-length vec) (- b a)))
  ;; (eprintf "vec-contract!: a = ~s, b = ~s, n = ~s\n" a b n)
  (define vec* (make-vector n #f))
  (for ([i n])
    (vector-set! vec* i (vector-ref vec (if (< i a) i (+ i (- b a))))))
  (set! vec vec*))

(define (vec-expand! a b)
  (define n (+ (vector-length vec) (- b a)))
  (define vec* (make-vector n #f))
  (for ([i (vector-length vec)])
    (vector-set! vec* (if (< i a) i (+ i (- b a))) (vector-ref vec i)))
  (set! vec vec*))

(define (check-all-refs)
  ;; (printf "vec ~v\n" (vector->list vec))
  ;; (printf "im  ~v\n" (for/list ([i (vector-length vec)]) (interval-map-ref im i #f)))
  (check-im im)
  (check-equal? (for/last ([(k v) (in-dict im)]) (cdr k))
                (vector-length vec)
                "different lengths")
  (for ([i (vector-length vec)])
    (check-equal? (interval-map-ref im i #f)
                  (vector-ref vec i)
                  "different values")))

;; set up
(interval-map-set! im 0 KEY-MAX 0)
(for ([k INTERVAL-CT])
  (define-values (a b)
    (let ([a (random KEY-MAX)] [b (random KEY-MAX)])
      (values (min a b) (max a b))))
  (define v (random VALUE-MAX))
  (unless (= a b)
    (for ([i (in-range a b)])
      (vector-set! vec i v))
    (interval-map-set! im a b v)))

(printf "check set up\n")
(check-all-refs)

;; contract!
(printf "check contract!\n")
(for ([i CONTRACT-CT])
  (define a (random (- (last-key) 1 SPREAD)))
  (define b (+ a 1 (random SPREAD)))
  ;; (eprintf "a = ~s, b = ~s\n" a b)
  (interval-map-contract! im a b)
  (vec-contract! a b)
  (check-all-refs))

;; expand!
(printf "check expand!\n")
(for ([i EXPAND-CT])
  (define a (random (last-key)))
  (define b (+ a 1 (random SPREAD)))
  ;; (eprintf "a = ~s, b = ~s\n" a b)
  (interval-map-expand! im a b)
  (vec-expand! a b)
  (check-all-refs))

;; tests for interval-map-ref/bounds
(let ([im (make-interval-map '())])
  ;; check ref for empty map
  (let-values ([(s e v)
                (interval-map-ref/bounds im 5 #t)])
    (check-equal? s #f)
    (check-equal? e #f)
    (check-equal? v #t)))
(let ([im (make-interval-map '(((5 . 10) . "value")))])
  ;; check refs for map with one value
  (let-values ([(s e v)
                (interval-map-ref/bounds im 5)])
    (check-equal? s 5)
    (check-equal? e 10)
    (check-equal? v "value"))
  (let-values ([(s e v)
                (interval-map-ref/bounds im 10 #t)])
    (check-equal? s #f)
    (check-equal? e #f)
    (check-equal? v #t))
  (let-values ([(s e v)
                (interval-map-ref/bounds im 4 (λ () #t))])
    (check-equal? s #f)
    (check-equal? e #f)
    (check-equal? v #t)))
(let ([im (make-interval-map '(((5 . 10) . "value") ((20 . 30) . "other")))])
  ;; check refs for map with multiple values
  (let-values ([(s e v)
                (interval-map-ref/bounds im 4 #t)])
    (check-equal? s #f)
    (check-equal? e #f)
    (check-equal? v #t))
  (let-values ([(s e v)
                (interval-map-ref/bounds im 7)])
    (check-equal? s 5)
    (check-equal? e 10)
    (check-equal? v "value"))
  (let-values ([(s e v)
                (interval-map-ref/bounds im 15 #t)])
    (check-equal? s #f)
    (check-equal? e #f)
    (check-equal? v #t))
  (let-values ([(s e v)
                (interval-map-ref/bounds im 22)])
    (check-equal? s 20)
    (check-equal? e 30)
    (check-equal? v "other"))
  (let-values ([(s e v)
                (interval-map-ref/bounds im 30 #t)])
    (check-equal? s #f)
    (check-equal? e #f)
    (check-equal? v #t)))