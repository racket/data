#lang racket/base
(provide unfair-n+n->n
         unfair-n->n+n
         unfair-n*n->n
         unfair-n->n*n)

(define (fllog n)
  (let loop ([n n])
    (cond
      [(= n 1) 0]
      [else (+ 1 (loop (quotient n 2)))])))

(define (count-up n)
  (let loop ([n n]
             [group-size 1])
  (cond
    [(<= n 0) 1]
    [else
     (+ (loop (- n group-size)
              (- (* (+ group-size 1) 2) 1))
        1)])))

(define (unfair-n+n->n left? n)
  (if left?
      (if (zero? n)
          0
          (+ n (count-up n)))
      (expt 2 n)))

(define (unfair-n->n+n n)
  (cond
    [(zero? n) (values #t 0)]
    [else
     (define f (fllog n))
     (cond
       [(= (expt 2 f) n)
        (values #f f)]
       [else
        (values #t (- n (fllog n) 1))])]))

(define (unfair-n->n*n n)
  (define twos 0)
  (define leftover
    (let loop ([n (+ n 1)])
      (cond
        [(and (not (zero? n)) (even? n))
         (set! twos (+ twos 1))
         (loop (/ n 2))]
        [else n])))
  (values (/ (- leftover 1) 2) twos))

(define (unfair-n*n->n x y)
  (- (* (expt 2 y) (+ (* 2 x) 1)) 1))

(module+ test
  (require rackunit)
  
  ;; test alternation bijection
  (for ([i (in-range 100000)])
    (define-values (left? n) (unfair-n->n+n i))
    (define j (unfair-n+n->n left? n))
    (unless (= i j)
      (error 'bad-bijection-fails
             "~s => ~s ~s => ~s"
             i left? n j)))

  ;; test pairing bijection
  (for ([i (in-range 100000)])
    (define-values (x y) (unfair-n->n*n i))
    (define j (unfair-n*n->n x y))
    (unless (= i j)
      (error 'bad-bijection-fails "~s => ~s ~s => ~s"
             i x y j)))

  ;; make sure that we go left first
  ;; important for things like
  ;; (define x (thunk/e (or/e (single/e #f) (cons/e x x))))
  (check-true (call-with-values
               (λ () (unfair-n->n+n 0))
               (λ (x y) x)))

  ;; make sure that we get more on the left than
  ;; the right in the sum combinator.
  (check-true (let ([limit 1000])
                (define (get-sum count-left?)
                  (for/sum ([i (in-range limit)])
                    (define-values (left? n) (unfair-n->n+n i))
                    (if (equal? count-left? left?) 1 0)))
                (< (get-sum #f) (get-sum #t))))

  ;; make sure we go deeper into the left component than
  ;; the right in the pair combinator
  (check-true (let ([limit 1000])
                (define (get-pair count-left?)
                  (for/fold ([deep 0]) ([i (in-range limit)])
                    (define-values (left right) (unfair-n->n*n i))
                    (max deep (if count-left? left right))))
                (< (get-pair #f) (get-pair #t)))))
