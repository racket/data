#lang racket/base
(require data/bit-vector
         racket/dict
         rackunit
         racket/set)

(define (bit-vector->vector bv)
  (for/vector ([b (in-bit-vector bv)])
    b))

(test-equal? "bit-vector"
             (bit-vector->vector (bit-vector #t #f #t))
             '#(#t #f #t))

(test-equal? "make-bit-vector"
             (make-bit-vector 3)
             (bit-vector #f #f #f))

(test-equal? "make-bit-vector"
             (make-bit-vector 3 #t)
             (bit-vector #t #t #t))

(test-equal? "bit-vector-ref"
             (let ([bv (bit-vector #t #f #t)])
               ;; 3 valid refs + 1 not-found
               (for/list ([index '(0 1 2)])
                 (bit-vector-ref bv index)))
             '(#t #f #t))

(test-equal? "bit-vector-set!"
             (let ([bv (bit-vector #t #t #t)])
               (bit-vector-set! bv 1 #f)
               (bit-vector->vector bv))
             '#(#t #f #t))

(test-equal? "bit-vector-length"
             (bit-vector-length (bit-vector #t #f #t))
             3)

(test-equal? "in-bit-vector"
             (let ([bv (bit-vector #t #f #t)])
               (for/list ([x (in-bit-vector bv)]) x))
             '(#t #f #t))

(test-equal? "in-bit-vector expression form"
             (let* ([bv (bit-vector #t #f #t)]
                    [bv-sequence (in-bit-vector bv)])
               (for/list ([x bv-sequence]) x))
             '(#t #f #t))

(test-equal? "bit-vector as sequence"
             (let ([bv (bit-vector #t #f #t)])
               (for/list ([x bv]) x))
             '(#t #f #t))

(test-case "bitvector, lots of sets"
           (let ([bv (make-bit-vector 1000)])
             (for ([i (in-range 0 1000)])
               (bit-vector-set! bv i (odd? i)))
             (for ([i (in-range 0 1000)])
               (check-equal? (bit-vector-ref bv i) (odd? i)))))

(test-equal? "bit-vector, dict-map"
             (dict-map (bit-vector #t #f #t) list)
             '((0 #t) (1 #f) (2 #t)))

(test-equal? "bit-vector, dict-ref"
             (dict-ref (bit-vector #t #f #t) 0)
             #t)

(test-equal? "bit-vector, dict-ref out of range"
             (dict-ref (bit-vector #t #f #t) 5 'not-found)
             'not-found)

(test-case "bit-vector-copy"
           (let ([bv (bit-vector #t #f #t #f #t)])
             (check-equal? (bit-vector-copy bv) bv)))

(test-case "bit-vector, hash-equal"
           (check-equal? 
            (equal-hash-code (bit-vector #t #f #t #f #t))
            (equal-hash-code (bit-vector #t #f #t #f #t))))

(test-case "bit-vector, hash-eq"
           (check-equal? 
            (= (eq-hash-code (bit-vector #t #f #t #f #t))
               (eq-hash-code (bit-vector #t #f #t #f #t)))
            #f))

(test-case "bit-vector, equal-proc (via equal?)"
           ;; Zero length bit-vectors are equal...
           (equal? (make-bit-vector 0 #t)
                   (make-bit-vector 0 #t))
           ;; ...even if fill value differed, because it's N/A
           (equal? (make-bit-vector 0 #t)
                   (make-bit-vector 0 #f))
           ;; Check a range of bit lengths spanning a few 8-bit bytes:
           (for ([len (in-range 1 24)])
             (check-equal?
              (equal? (make-bit-vector len #t)
                      (make-bit-vector len #t))
              #t)
             (check-equal?
              (equal? (make-bit-vector len #t)
                      (make-bit-vector len #f))
              #f))
           ;; Attempt to flush out potential bugs wrt to unused bits
           ;; that might be set by a "fill" value (implementation
           ;; detail we don't know for sure here), but should
           ;; definitely be ignored by equal?.
           (let ([x (make-bit-vector 1 #t)]  ;#t fill value
                 [y (make-bit-vector 1 #f)]) ;#f fill value
             ;; Set the only bit to #t in both
             (bit-vector-set! x 0 #t)
             (bit-vector-set! y 0 #t)
             ;; Should be equal, regardless of different fill values
             ;; in make-bit-vector:
             (check-equal? (equal? x y) #t)))

(test-case "for/bit-vector"
           (check-equal? (for/bit-vector ([i 5]) (odd? i))
                         (bit-vector #f #t #f #t #f))
           (check-equal? (for/bit-vector #:length 4 ([i 2]) (odd? i))
                         (bit-vector #f #t #f #f))
           (check-equal? (for/bit-vector #:length 4 #:fill #t ([i 2]) (odd? i))
                         (bit-vector #f #t #t #t))
           (let ([bv (make-bit-vector 1000)])
             (bit-vector-set! bv 400 #t)
             (check-equal? bv (for/bit-vector ([i 1000]) (= i 400)))))

(test-case "bit-vector-popcount"
           (let ()
             (define (test len)
               (define fill (odd? (random 2)))
               (define bv (make-bit-vector len fill))
               (define ns (list->set (build-list 100 (λ (_) (random len)))))
               (for ([n (in-set ns)]) (bit-vector-set! bv n (not fill)))
               (define count 
                 (if fill (- len (set-count ns)) (set-count ns)))
               (check-equal? (bit-vector-popcount bv) count))
             (for ([i (in-range 100)])
               (test 1000))
             ;; test multiples of possible word sizes
             (for ([ws (in-list '(8 30 62))])
               (for ([i (in-range 10)])
                 (test (* ws 10))))))

(test-case "bit-vector string->list"
  (let ([bitstrings '("0" "1" "10" "11" "1010110011100011110000")])
    (for ([s (in-list bitstrings)])
      (check-equal? (bit-vector->string (string->bit-vector s)) s)
      (let ([bitlist (for/list ([c (in-string s)]) (eqv? c #\1))])
        (check-equal? (bit-vector->list (string->bit-vector s))
                      bitlist)
        (check-equal? (string->bit-vector s)
                      (list->bit-vector bitlist))))))

(test-case "bit-vector-set! error"
  (define bv (bit-vector #f #f #f))

  (check-exn #rx"index is out of range"
             (λ () (bit-vector-set! bv 4 #t)))

  (check-exn #rx"expected: natural\\?"
             (λ () (bit-vector-set! bv -1 #t)))

  (check-exn #rx"expected: bit-vector\\?"
             (λ () (bit-vector-set! 1 0 #t))))

(test-case "bit-vector-ref error"
  (define bv (bit-vector #f #f #f))

  (check-exn #rx"index is out of range"
             (λ () (bit-vector-ref bv 4)))

  (check-exn #rx"expected: natural\\?"
             (λ () (bit-vector-ref bv -1)))

  (check-exn #rx"expected: bit-vector\\?"
             (λ () (bit-vector-ref 1 0))))

;; Check equality for 2 vector with the same bits, one initiliazed with #f, the other with #t
(test-case "bit-vector #f #t"
           (for* ([n (in-range 17)]
                  [i (in-range n)])
             (define bv1 (make-bit-vector n #false))
             (define bv2 (make-bit-vector n #true))
             (bit-vector-set! bv1 i #true)
             (for ([j (in-range n)] #:unless (= i j))
               (bit-vector-set! bv2 j #false))
             (check-equal? bv1 bv2))
           )