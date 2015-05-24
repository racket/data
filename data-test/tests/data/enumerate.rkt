#lang racket/base
(require rackunit
         racket/function
         racket/set
         racket/contract
         racket/generator
         data/gvector
         data/enumerate
         data/enumerate/lib
         "enumerate/util.rkt"
         (prefix-in unsafe: data/enumerate/private/more)
         (prefix-in unsafe: data/enumerate/private/core))



(require (for-syntax racket/base))
(define last (current-process-milliseconds))
(define (show-here/proc l)
  (printf "got to line ~a ~s\n" l (- (current-process-milliseconds) last))
  (set! last (current-process-milliseconds)))
(define-syntax (show-here stx)
  #`(show-here/proc #,(syntax-line stx)))

;; fin/e tests
(let ([e (fin/e 17)])
  (test-begin
   (check-eq? (from-nat e 0) 17)
   (check-exn exn:fail? (λ () (from-nat e 1)))
   (check-eq? (to-nat e 17) 0)
   (check-exn exn:fail? (λ () (to-nat e 0)))
   (check-bijection? e)))

(let ([e (single/e 17)])
  (test-begin
   (check-eq? (from-nat e 0) 17)
   (check-exn exn:fail? (λ () (from-nat e 1)))
   (check-eq? (to-nat e 17) 0)
   (check-exn exn:fail? (λ () (to-nat e 0)))
   (check-bijection? e)))

;; fin/e tests
(let ([e (fin/e 5 4 1 8)])
  (test-begin
   (check-eq? (from-nat e 0) 5)
   (check-eq? (from-nat e 3) 8)
   (check-exn exn:fail?
              (λ () (from-nat e 4)))
   (check-eq? (to-nat e 5) 0)
   (check-eq? (to-nat e 8) 3)
   (check-exn exn:fail?
              (λ ()
                 (to-nat e 17)))
   (check-bijection? e)
   (check-true ((enum-contract e) (from-nat e 0)))))

(check-bijection? (fin/e "x" 11 "y" 12 #"x" 'w +nan.0 +nan.f +inf.0 '#:kwd))

(let ([e (fin/e (λ (x) x) '(1 2 3))])
  (check-equal? ((from-nat e 0) 1) 1)
  (check-equal? (from-nat e 1) '(1 2 3))
  (check-true (one-way-enum? e))
  (check-true (finite-enum? e)))

;; map test
(define nats+1 (nat+/e 1))

(test-begin
 (check-equal? (infinite-enum? nats+1) #t)
 (check-equal? (from-nat nats+1 0) 1)
 (check-equal? (from-nat nats+1 1) 2)
 (check-bijection? nats+1))
;; encode check
(test-begin
 (check-exn exn:fail?
            (λ ()
               (from-nat natural/e -1))))

;; ints checks
(test-begin
 (check-eq? (from-nat integer/e 0) 0)         ; 0 -> 0
 (check-eq? (from-nat integer/e 1) 1)         ; 1 -> 1
 (check-eq? (from-nat integer/e 2) -1)        ; 2 -> 1
 (check-eq? (to-nat integer/e 0) 0)
 (check-eq? (to-nat integer/e 1) 1)
 (check-eq? (to-nat integer/e -1) 2)
 (check-bijection? integer/e))                ; -1 -> 2, -3 -> 4

(check-equal? (from-nat string/e (+ (enum-count char/e) 1))
              (string (from-nat char/e 0) (from-nat char/e 0)))
(check-equal? (from-nat string/e (enum-count char/e))
              "")
(check-equal? (from-nat string/e 0)
              (string (from-nat char/e 0)))
(check-equal? (from-nat symbol/e (+ (enum-count char/e) 1))
              (string->symbol (from-nat string/e (+ (enum-count char/e) 1))))

(test-begin
 (define bool-or-num
   (or/e (cons bool/e boolean?)
         (cons (fin/e 0 1 2 3) number?)))

 (define bool-or-nat
   (or/e (cons bool/e boolean?)
         (cons natural/e number?)))

 (define nat-or-bool
   (or/e (cons natural/e number?)
         (cons bool/e boolean?)))

 (define odd-or-even
   (let ()
     ;; sum tests
     (define evens/e
       (map/e (λ (n)
                (* 2 n))
              (λ (n)
                (if (and (zero? (modulo n 2))
                         (>= n 0))
                    (/ n 2)
                    (error 'even)))
              natural/e
              #:contract (and/c exact-integer? even?)))
     
     (define odds/e
       (map/e (λ (n)
                (+ (* 2 n) 1))
              (λ (n)
                (if (and (not (zero? (modulo n 2)))
                         (>= n 0))
                    (/ (- n 1) 2)
                    (error 'odd)))
              natural/e
              #:contract (and/c exact-integer? odd?)))
     
     (or/e (cons evens/e even?)
           (cons odds/e odd?))))

 (check-equal? (enum-count bool-or-num) 6)
   
 (check-equal? (from-nat bool-or-num 0) #t)
 (check-equal? (from-nat bool-or-num 1) 0)
 (check-equal? (from-nat bool-or-num 2) #f)
 (check-equal? (from-nat bool-or-num 3) 1)
 (check-equal? (from-nat bool-or-num 4) 2)
 (check-equal? (from-nat bool-or-num 5) 3)
   
 (check-equal? (for/list ([i (in-range 5)])
                 (from-nat (take/e natural/e 5) i))
               '(0 1 2 3 4))
 
 (check-exn exn:fail?
            (λ ()
               (from-nat bool-or-num 6)))
 (check-bijection? bool-or-num)
   
 (check-equal? (infinite-enum? bool-or-nat) #t)
 (check-equal? (from-nat bool-or-nat 0) #t)
 (check-equal? (from-nat bool-or-nat 1) 0)
 (check-bijection? bool-or-nat)
 
 (check-equal? (infinite-enum? odd-or-even) #t)
 (check-equal? (from-nat odd-or-even 0) 0)
 (check-equal? (from-nat odd-or-even 1) 1)
 (check-equal? (from-nat odd-or-even 2) 2)
 (check-exn exn:fail?
            (λ ()
               (from-nat odd-or-even -1)))
 (check-equal? (to-nat odd-or-even 0) 0)   
 (check-equal? (to-nat odd-or-even 1) 1)
 (check-equal? (to-nat odd-or-even 2) 2)
 (check-equal? (to-nat odd-or-even 3) 3)
 (check-bijection? odd-or-even)

 (check-bijection? nat-or-bool)

 (define multi-layered
   (or/e (cons (take/e string/e 5) string?)
         (cons (fin/e 'a 'b 'c 'd) symbol?)
         (cons natural/e number?)
         (cons bool/e boolean?)
         (cons (listof/e bool/e) list?)))

 (define (test-multi-layered i x)
   (check-equal? (from-nat multi-layered i) x))

 (map test-multi-layered
      (for/list ([i (in-range 31)])
        i)
      ;; The #||# comments in the below are
      ;; to trick the automatic indentation
      ;; to keep everything lined up nicely
      '(#||#
        #||# "a"  a 0 #t ()
        #||# "b"  b 1 #f (#t)
        #||# "c"  c 2    (#f)
        #||# "d"  d 3    (#t #t)
        #||# "e"    4    (#f #t)
        #||#        5    (#t #f)
        #||#        6    (#f #f)
        #||#        7    (#t #t #t)
        #||#        8    (#f #t #t)
        #||#        9    (#t #f #t)))
 
 (check-bijection? multi-layered)
 
 (check-equal? (enum->list (or/e (cons/e natural/e natural/e) natural/e)
                           6)
              (list (from-nat (cons/e natural/e natural/e) 0)
                    0
                    (from-nat (cons/e natural/e natural/e) 1)
                    1
                    (from-nat (cons/e natural/e natural/e) 2)
                    2)))

;; make sure various combinators correctly propagate bijectionness.
(check-equal? 
 (two-way-enum? 
  (or/e (pam/e (λ (x) (floor (/ x 2))) natural/e #:contract exact-integer?)
        (pam/e (λ (x) (floor (/ x 3))) natural/e #:contract exact-integer?)))
 #f)
(check-equal? 
 (two-way-enum? 
  (or/e natural/e natural/e #:one-way-enum? #t))
 #f)
(check-equal? 
 (two-way-enum? 
  (unsafe:fin-cons/e
   (pam/e (λ (x) (floor (/ x 2))) (below/e 100) #:contract exact-integer?)
   (pam/e (λ (x) (floor (/ x 3))) (below/e 100) #:contract exact-integer?)))
 #f)

(test-begin
 (define bool-or-num
   (append/e (cons bool/e boolean?)
             (cons (fin/e 0 1 2 3) number?)))
 (define bool-or-nat
   (append/e (cons bool/e boolean?)
             (cons natural/e number?)))
 
 (check-equal? (enum-count bool-or-num) 6)
   
 (check-equal? (from-nat bool-or-num 0) #t)
 (check-equal? (from-nat bool-or-num 1) #f)
 (check-equal? (from-nat bool-or-num 2) 0)
 (check-equal? (from-nat bool-or-num 3) 1)
 (check-equal? (from-nat bool-or-num 4) 2)
 (check-equal? (from-nat bool-or-num 5) 3)
   
 (check-exn exn:fail?
            (λ ()
               (from-nat bool-or-num 6)))
 (check-bijection? bool-or-num)
   
 (check-equal? (infinite-enum? bool-or-nat) #t)
 (check-equal? (from-nat bool-or-nat 0) #t)
 (check-equal? (from-nat bool-or-nat 1) #f)
 (check-equal? (from-nat bool-or-nat 2) 0)
 (check-bijection? bool-or-nat)
 
 (check-bijection? (append/e (below/e 10) bool/e (cons/e natural/e natural/e))))

;; cons/e tests
(define bool*bool (cons/e bool/e bool/e))
(define 1*b (cons/e (fin/e 1) bool/e))
(define b*1 (cons/e bool/e (fin/e 1)))
(define bool*nats (cons/e bool/e natural/e))
(define nats*bool (cons/e natural/e bool/e))
(define nats*nats (cons/e natural/e natural/e))
(define ns-equal? (λ (ns ms)
                     (and (= (car ns)
                             (car ms))
                          (= (cdr ns)
                             (cdr ms)))))


;; prod tests
(test-begin

 (check-equal? (enum-count 1*b) 2)
 (check-equal? (from-nat 1*b 0) (cons 1 #t))
 (check-equal? (from-nat 1*b 1) (cons 1 #f))
 (check-bijection? 1*b)
 (check-bijection? b*1)
 (check-equal? (enum-count bool*bool) 4)
 (check-bijection? bool*bool)

 (check-equal? (infinite-enum? bool*nats) #t)
 (check-bijection? bool*nats)

 (check-equal? (infinite-enum? nats*bool) #t)
 (check-bijection? nats*bool)

 (check-bijection? nats*nats)
 (check-bijection? (list/e integer/e integer/e))
 (check-bijection? 
  (apply list/e
         (for/list ([i (in-range 24)])
           (map/e (curry cons i) cdr natural/e
                  #:contract (cons/c i exact-nonnegative-integer?))))))

(check-equal? (for/list ([i (in-range 10)])
                (from-nat (cons/e natural/e natural/e #:ordering 'diagonal) i))
              '((0 . 0) 
                (0 . 1) (1 . 0) 
                (0 . 2) (1 . 1) (2 . 0)
                (0 . 3) (1 . 2) (2 . 1) (3 . 0)))

(check-equal? (for/list ([i (in-range 9)])
                (from-nat (cons/e natural/e natural/e #:ordering 'square) i))
              '((0 . 0)
                (0 . 1) (1 . 0) (1 . 1)
                (0 . 2) (1 . 2) (2 . 0) (2 . 1) (2 . 2)))

(check-equal? (for/list ([i (in-range 10)])
                (from-nat (vector/e natural/e natural/e #:ordering 'diagonal) i))
              '(#(0 0) 
                #(0 1) #(1 0) 
                #(0 2) #(1 1) #(2 0)
                #(0 3) #(1 2) #(2 1) #(3 0)))

(check-equal? (for/list ([i (in-range 9)])
                (from-nat (vector/e natural/e natural/e #:ordering 'square) i))
              '(#(0 0)
                #(0 1) #(1 0) #(1 1)
                #(0 2) #(1 2) #(2 0) #(2 1) #(2 2)))

(check-true (flat-enum? (vector/e natural/e)))

;; check that box-tuples/e is the same ordering as list/e in 'square mode
(check-equal? (for/list ([x (in-range 100)])
                (from-nat (unsafe:box-tuples/e 3) x))
              (for/list ([x (in-range 100)])
                (from-nat (list/e #:ordering 'square natural/e natural/e natural/e) x)))

;; check to make sure that the #:ordering keyword argument is treated
;; properly when there is a mixture of finite and infintite enumerations.
(check-equal? (for/list ([x (in-range 9)])
                (from-nat (list/e natural/e natural/e (fin/e 'x)) x))
              '((0 0 x)
                (0 1 x) (1 0 x) (1 1 x)
                (0 2 x) (1 2 x) (2 0 x) (2 1 x) (2 2 x)))

(check-equal? (for/list ([x (in-range 9)])
                (from-nat (list/e natural/e natural/e (fin/e 'x) #:ordering 'square) x))
              '((0 0 x)
                (0 1 x) (1 0 x) (1 1 x)
                (0 2 x) (1 2 x) (2 0 x) (2 1 x) (2 2 x)))

(check-equal? (for/list ([x (in-range 10)])
                (from-nat (list/e natural/e natural/e (fin/e 'x) #:ordering 'diagonal) x))
              '((0 0 x)
                (0 1 x) (1 0 x)
                (0 2 x) (1 1 x) (2 0 x)
                (0 3 x) (1 2 x) (2 1 x) (3 0 x)))



;; fair product tests
(define-simple-check (check-range? e l u approx)
  (let ([actual (for/set ([i (in-range l u)])
                  (from-nat e i))]
        [expected (list->set approx)])
    (equal? actual expected)))
(test-begin
 (define n*n     (unsafe:cantor-list/e natural/e natural/e))
 (check-range? n*n  0  1 '((0 0)))
 (check-range? n*n  1  3 '((0 1) (1 0)))
 (check-range? n*n  3  6 '((0 2) (1 1) (2 0)))
 (check-range? n*n  6 10 '((0 3) (1 2) (2 1) (3 0)))
 (check-range? n*n 10 15 '((0 4) (1 3) (2 2) (3 1) (4 0))))
(test-begin
 (define n*n     (list/e #:ordering 'diagonal natural/e natural/e))
 (check-range? n*n  0  1 '((0 0)))
 (check-range? n*n  1  3 '((0 1) (1 0)))
 (check-range? n*n  3  6 '((0 2) (1 1) (2 0)))
 (check-range? n*n  6 10 '((0 3) (1 2) (2 1) (3 0)))
 (check-range? n*n 10 15 '((0 4) (1 3) (2 2) (3 1) (4 0))))
(test-begin
 (define n*n*n   (unsafe:cantor-list/e natural/e natural/e natural/e))
 (define n*n*n*n (unsafe:cantor-list/e natural/e natural/e natural/e natural/e))
 
 (check-equal? (one-way-enum?
                (unsafe:cantor-list/e 
                 (pam/e values natural/e #:contract (enum-contract natural/e))
                 natural/e))
               #t)
 
 (check-equal? (one-way-enum?
                (list/e natural/e
                        (pam/e values natural/e #:contract exact-nonnegative-integer?)
                        natural/e))
               #t)
 
 (check-equal? (from-nat
                (list/e natural/e
                        (pam/e values natural/e #:contract exact-nonnegative-integer?)
                        natural/e)
                0)
               '(0 0 0))
 
 (check-equal? (one-way-enum?
                (list/e natural/e
                        (pam/e values natural/e #:contract exact-nonnegative-integer?)
                        natural/e
                        natural/e
                        natural/e
                        natural/e))
               #t)
 
 (check-equal? (from-nat
                (list/e natural/e
                        (pam/e values natural/e #:contract exact-nonnegative-integer?)
                        natural/e
                        natural/e
                        natural/e
                        natural/e)
                0)
               '(0 0 0 0 0 0))
 
 (check-range? n*n*n  0  1 '((0 0 0)))
 (check-range? n*n*n  1  4 '((0 0 1) (0 1 0) (1 0 0)))
 (check-range? n*n*n  4 10 '((0 0 2) (1 1 0) (0 1 1) (1 0 1) (0 2 0) (2 0 0)))
 (check-range? n*n*n 10 20 '((0 0 3) (0 3 0) (3 0 0)
                             (0 1 2) (1 0 2) (0 2 1) (1 2 0) (2 0 1) (2 1 0)
                             (1 1 1))))

(test-begin
 (check-bijection? (vector/e string/e natural/e two-way-real/e))
 (check-bijection? (unsafe:cantor-list/e string/e natural/e two-way-real/e))
 (check-bijection? (unsafe:cantor-list/e)))

(test-begin
 (define n*n     (unsafe:box-list/e natural/e natural/e))
 (check-range? n*n  0  1 '((0 0)))
 (check-range? n*n  1  4 '((0 1) (1 0) (1 1)))
 (check-range? n*n  4  9 '((0 2) (1 2) (2 1) (2 0) (2 2))))
(test-begin
 (define n*n*n   (unsafe:box-list/e natural/e natural/e natural/e))

 (check-range? n*n*n  0  1 '((0 0 0)))
 (check-range? n*n*n  1  8 '((0 0 1) (0 1 1) (0 1 0)
                             
                             (1 0 0) (1 0 1) (1 1 0) (1 1 1)))
 (check-range? n*n*n  8 27 '((0 0 2) (0 1 2) (0 2 2)
                             (0 2 0) (0 2 1)

                             (1 0 2) (1 1 2) (1 2 2)
                             (1 2 0) (1 2 1)

                             (2 0 0) (2 0 1) (2 0 2)
                             (2 1 0) (2 1 1) (2 1 2)
                             (2 2 0) (2 2 1) (2 2 2))))

(test-begin
 (define n*n*n   (list/e #:ordering 'square natural/e natural/e natural/e))

 (check-range? n*n*n  0  1 '((0 0 0)))
 (check-range? n*n*n  1  8 '((0 0 1) (0 1 1) (0 1 0)
                             
                             (1 0 0) (1 0 1) (1 1 0) (1 1 1)))
 (check-range? n*n*n  8 27 '((0 0 2) (0 1 2) (0 2 2)
                             (0 2 0) (0 2 1)

                             (1 0 2) (1 1 2) (1 2 2)
                             (1 2 0) (1 2 1)

                             (2 0 0) (2 0 1) (2 0 2)
                             (2 1 0) (2 1 1) (2 1 2)
                             (2 2 0) (2 2 1) (2 2 2))))

(test-begin
 (check-bijection? (unsafe:box-list/e string/e natural/e two-way-real/e))
 (check-bijection? (unsafe:box-list/e)))

;; multi-arg map/e test
(define sums/e
  (map/e
   cons
   (λ (x-y)
      (values (car x-y) (cdr x-y)))
   (fin/e 1 2)
   (fin/e 3 4)
   #:contract any/c))


(check-not-exn
 (λ ()
   (map/e add1 sub1 empty/e #:contract none/c)))

(test-begin
 (check-bijection? sums/e))

(check-bijection? 
 (letrec ([m/e (delay/e
                (or/e (fin/e #f)
                      (cons/e m/e m/e)))])
   m/e))

(check-bijection? 
 (letrec ([m/e (thunk/e
                (λ ()
                  (or/e (fin/e #f)
                        (cons/e m/e m/e))))])
   m/e))

;; cons/de tests

(check-equal? (flat-enum? (cons/de [hd natural/e] [tl (hd) natural/e]))
              #t)
(check-equal? (flat-enum? (dep/e natural/e (λ (_) natural/e)))
              #t)
(check-equal? (flat-enum?
               (cons/de [len (nat+/e 1)]
                        [lst (len)
                             (listof-n/e natural/e (len . * . 2))]))
              #t)

(check-equal? (from-nat (or/e (single/e '())
                              (cons/de [len (nat+/e 1)]
                                       [lst (len)
                                            (listof-n/e natural/e (len . * . 2))]))
                        0)
              '())

(check-equal? (from-nat (or/e (single/e '())
                              (cons/de [len (nat+/e 1)]
                                       [lst (len)
                                            (listof-n/e natural/e (len . * . 2))]))
                        1)
              '(1 0 0))

(define (up-to n) (below/e (add1 n)))
(define 3-up
  (cons/de [hd (fin/e 0 1 2)]
           [tl (hd) (below/e (add1 hd))]
           #:dep-expression-finite? #t))

(define from-3
  (cons/de
   [hd (fin/e 0 1 2)]
   [tl (hd) (nat+/e hd)]))

(define nats-to
  (cons/de [hd natural/e]
           [tl (hd) (up-to hd)]
           #:dep-expression-finite? #t))

(define nats-up
  (cons/de [hd natural/e]
           [tl (hd) (nat+/e hd)]))

(test-begin
 (check-equal? (enum-count 3-up) 6)
 (check-equal? (from-nat 3-up 0) (cons 0 0))
 (check-equal? (from-nat 3-up 1) (cons 1 0))
 (check-equal? (from-nat 3-up 2) (cons 1 1))
 (check-equal? (from-nat 3-up 3) (cons 2 0))
 (check-equal? (from-nat 3-up 4) (cons 2 1))
 (check-equal? (from-nat 3-up 5) (cons 2 2))
 (check-bijection? 3-up)

 (check-equal? (infinite-enum? from-3) #t)
 (check-equal? (from-nat from-3 0) (cons 0 0))
 (check-equal? (from-nat from-3 1) (cons 1 1))
 (check-equal? (from-nat from-3 2) (cons 2 2))
 (check-equal? (from-nat from-3 3) (cons 0 1))
 (check-equal? (from-nat from-3 4) (cons 1 2))
 (check-equal? (from-nat from-3 5) (cons 2 3))
 (check-equal? (from-nat from-3 6) (cons 0 2))
 (check-bijection? from-3)

 (check-equal? (infinite-enum? nats-to) #t)
 (check-equal? (from-nat nats-to 0) (cons 0 0))
 (check-equal? (from-nat nats-to 1) (cons 1 0))
 (check-equal? (from-nat nats-to 2) (cons 1 1))
 (check-equal? (from-nat nats-to 3) (cons 2 0))
 (check-equal? (from-nat nats-to 4) (cons 2 1))
 (check-equal? (from-nat nats-to 5) (cons 2 2))
 (check-equal? (from-nat nats-to 6) (cons 3 0))
 (check-bijection? nats-to)

 (check-equal? (infinite-enum? nats-up) #t)
 (check-equal? (from-nat nats-up 0) (cons 0 0))
 (check-equal? (from-nat nats-up 1) (cons 0 1))
 (check-equal? (from-nat nats-up 2) (cons 1 1))
 (check-equal? (from-nat nats-up 3) (cons 1 2))
 (check-equal? (from-nat nats-up 4) (cons 0 2))
 (check-equal? (from-nat nats-up 5) (cons 1 3))
 (check-equal? (from-nat nats-up 6) (cons 2 2))
 (check-equal? (from-nat nats-up 7) (cons 2 3))

 (check-bijection? nats-up))

(check-equal? (enum->list (dep/e natural/e (λ (i) natural/e)) 20)
              (enum->list (cons/e natural/e natural/e #:ordering 'square) 20))
(check-bijection? (dep/e natural/e (λ (i) natural/e)))
(check-equal? (enum->list (flip-dep/e natural/e 
                                      (λ (tl) (below/e tl))
                                      #:f-range-finite? #t)
                          10)
              '((0 . 1)
                (0 . 2) (1 . 2)
                (0 . 3) (1 . 3) (2 . 3)
                (0 . 4) (1 . 4) (2 . 4) (3 . 4)))
(check-equal? (enum->list (dep/e natural/e 
                                 (λ (hd) (nat+/e (+ hd 1))))
                          10)
              '((0 . 1)
                (0 . 2) (1 . 2) (1 . 3) (0 . 3)
                (1 . 4) (2 . 3) (2 . 4) (2 . 5)
                (0 . 4)))
(check-equal? (enum->list (dep/e natural/e
                                 (λ (hd)
                                   (pam/e (λ (_) (+ hd 1))
                                          (below/e 1)
                                          #:contract
                                          (λ (x) (equal? x (+ hd 1)))))
                                 #:f-range-finite? #t
                                 #:one-way? #t)
                          3)
              '((0 . 1) (1 . 2) (2 . 3)))
(check-equal? (enum->list (flip-dep/e natural/e
                                      (λ (hd)
                                        (pam/e (λ (_) (+ hd 1))
                                               (below/e 1)
                                               #:contract
                                               (λ (x) (equal? x (+ hd 1)))))
                                      #:f-range-finite? #t
                                      #:one-way? #t)
                          3)
              '((1 . 0) (2 . 1) (3 . 2)))
(check-true (one-way-enum? (dep/e natural/e
                                  (λ (hd)
                                    (pam/e (λ (_) (+ hd 1))
                                           (below/e 1)
                                           #:contract
                                           (λ (x) (equal? x (+ hd 1)))))
                                  #:f-range-finite? #t
                                  #:one-way? #t)))
(check-true (one-way-enum? (cons/de [hd natural/e] [tl (hd) natural/e]
                                    #:one-way? #t)))

(define 3-up-2
  (cons/de
   [hd (fin/e 0 1 2)]
   [tl (hd) (up-to hd)]
   #:dep-expression-finite? #t))

(define nats-to-2
  (cons/de [hd natural/e]
           [tl (hd) (up-to hd)]
           #:dep-expression-finite? #t))

(check-equal? (one-way-enum?
               (cons/de
                [i (pam/e values natural/e #:contract (enum-contract natural/e))]
                [tl (i) (pam/e values natural/e #:contract (enum-contract natural/e))]))
              #t)
(check-equal? (one-way-enum?
               (cons/de
                [i (pam/e values (below/e 10) #:contract (enum-contract natural/e))]
                [tl (i) (pam/e values natural/e #:contract (enum-contract natural/e))]))
              #t)
(check-equal? (one-way-enum?
               (cons/de
                [i (pam/e values (below/e 10) #:contract (enum-contract natural/e))]
                [tl (i) (pam/e values (below/e i) #:contract (enum-contract (below/e i)))]
                #:dep-expression-finite? #t))
              #t)

(test-begin
 (check-equal? (enum-count 3-up-2) 6)
 (check-equal? (from-nat 3-up-2 0) (cons 0 0))
 (check-equal? (from-nat 3-up-2 1) (cons 1 0))
 (check-equal? (from-nat 3-up-2 2) (cons 1 1))
 (check-equal? (from-nat 3-up-2 3) (cons 2 0))
 (check-equal? (from-nat 3-up-2 4) (cons 2 1))
 (check-equal? (from-nat 3-up-2 5) (cons 2 2))
 
 (check-equal? (to-nat 3-up-2 (cons 0 0)) 0)
 (check-equal? (to-nat 3-up-2 (cons 1 0)) 1)
 (check-equal? (to-nat 3-up-2 (cons 1 1)) 2)
 (check-equal? (to-nat 3-up-2 (cons 2 0)) 3)

 (check-equal? (infinite-enum? nats-to-2) #t)
 (check-equal? (to-nat nats-to-2 (cons 0 0)) 0)
 (check-equal? (to-nat nats-to-2 (cons 1 0)) 1)
 (check-equal? (to-nat nats-to-2 (cons 1 1)) 2)
 (check-equal? (to-nat nats-to-2 (cons 2 0)) 3)
 (check-equal? (to-nat nats-to-2 (cons 2 1)) 4)
 (check-equal? (to-nat nats-to-2 (cons 2 2)) 5)
 (check-equal? (to-nat nats-to-2 (cons 3 0)) 6)

 (check-equal? (from-nat nats-to-2 0) (cons 0 0))
 (check-equal? (from-nat nats-to-2 1) (cons 1 0))
 (check-equal? (from-nat nats-to-2 2) (cons 1 1))
 (check-equal? (from-nat nats-to-2 3) (cons 2 0))
 (check-equal? (from-nat nats-to-2 4) (cons 2 1))
 (check-equal? (from-nat nats-to-2 5) (cons 2 2))
 (check-equal? (from-nat nats-to-2 6) (cons 3 0)))

;; take/e test
(define to-2 (up-to 2))
(test-begin
 (check-equal? (enum-count to-2) 3)
 (check-equal? (from-nat to-2 0) 0)
 (check-equal? (from-nat to-2 1) 1)
 (check-equal? (from-nat to-2 2) 2)
 (check-bijection? to-2))

;; slic/e test
(test-begin
 (check-equal? (enum->list (slice/e natural/e 3 5)) '(3 4))
 (check-bijection? (slice/e natural/e 3 5)))

;; enum->list test
(test-begin
 (check-equal? (enum->list (up-to 3))
               '(0 1 2 3)))

;; except/e test

(define not-3 (except/e natural/e 3))
(test-begin
 (check-equal? (from-nat not-3 0) 0)
 (check-equal? (from-nat not-3 3) 4)
 (check-bijection? not-3))

;; fold-enum tests
(define complicated
  (fold-enum
   #:f-range-finite? #t
   (λ (excepts n)
      (apply except/e (up-to n) excepts))
   '(2 4 6)))
(test-begin
 (check-bijection? complicated))

(test-begin
 (check-bijection? (listof/e natural/e))
 (check-equal? (from-nat (listof/e empty/e) 0) '())
 (check-bijection? (listof/e empty/e))
 (check-bijection/just-a-few? (listof/e natural/e #:simple-recursive? #f))
 (check-bijection/just-a-few? (non-empty-listof/e natural/e #:simple-recursive? #f))
 (check-bijection? (non-empty-listof/e empty/e))
 (check-bijection? (non-empty-listof/e natural/e)))

(check-bijection? (listof-n/e natural/e 4))

(check-equal? (from-nat (range/e -inf.0 10) 0) 10)
(check-equal? (to-nat (range/e -inf.0 10) 10) 0)
(check-equal? (from-nat (range/e -inf.0 10) 1) 9)
(check-equal? (to-nat (range/e -inf.0 10) 9) 1)
(check-equal? (from-nat (range/e 10 +inf.0) 0) 10)
(check-equal? (to-nat (range/e 10 +inf.0) 10) 0)
(check-equal? (from-nat (range/e 10 +inf.0) 1) 11)
(check-equal? (to-nat (range/e 10 +inf.0) 11) 1)
(check-equal? (from-nat (range/e -inf.0 +inf.0) 0) 0)
(check-equal? (to-nat (range/e -inf.0 +inf.0) 0) 0)
(check-equal? (from-nat (range/e -10 10) 0) -10)
(check-equal? (to-nat (range/e -10 10) -10) 0)
(check-equal? (from-nat (range/e -10 10) 1) -9)
(check-equal? (to-nat (range/e -10 10) -9) 1)

(check-equal? (ormap negative? 
                     (for/list ([i (in-range 20)])
                       (from-nat exact-rational/e i)))
              #t)
(check-equal? (ormap positive? 
                     (for/list ([i (in-range 20)])
                       (from-nat exact-rational/e i)))
              #t)
(check-equal? (ormap integer? 
                     (for/list ([i (in-range 20)])
                       (from-nat exact-rational/e i)))
              #t)
(check-equal? (ormap (not/c integer?)
                     (for/list ([i (in-range 20)])
                       (from-nat exact-rational/e i)))
              #t)

(let ()
  (define sevens/e (infinite-sequence/e (below/e 7)))
  (check-not-false
   (andmap (integer-in 0 6)
           (for/list ([e (from-nat sevens/e 42)]
                      [i (in-range 10)])
             e))))

(check-equal? (enum->list (set/e empty/e))
              (list (set)))
(check-equal? (enum->list (set/e (fin/e 4)))
              (list (set) (set 4)))
(check-equal? (list->set (enum->list (set/e (fin/e 'a 'b))))
              (set (set) (set 'a) (set 'b) (set 'a 'b)))
(let ()
  (define nat-set/e (set/e natural/e))

  (for ([i  (in-range 10000)])
    (check-equal? (to-nat nat-set/e (from-nat nat-set/e i))
                  i))
  (for ([i  (in-range 10000)])
    (define s (list->set (build-list (random 100) (λ (_) (random 100)))))
    (check-equal? (from-nat nat-set/e (to-nat nat-set/e s))
                  s)))

(let ()
  (define e (permutations-of-n/e 3))
  (check-equal? (for/list ([x (in-range (enum-count e))])
                  (from-nat e x))
                '((0 1 2)
                  (0 2 1)
                  (1 0 2)
                  (1 2 0)
                  (2 0 1)
                  (2 1 0))))

(let ()
  (define abcs/e (permutations/e '(a b c)))
  (check-equal? (for/list ([i (in-range (enum-count abcs/e))])
                  (from-nat abcs/e i))
                '((a b c)
                  (a c b)
                  (b a c)
                  (b c a)
                  (c a b)
                  (c b a))))

(check-equal? (let ([h (hash "Brian" 5 "Jenny" 15 "Ted" 25 "Ki" 30)])
                (enum->list
                 (hash-traverse/e (λ (n) (below/e n))
                                  h
                                  #:get-contract
                                  (λ (v) (and/c exact-integer? (<=/c (hash-ref h v)))))
                 5))
              '(#hash(("Ki" . 0) ("Ted" . 0) ("Brian" . 0) ("Jenny" . 0))
                #hash(("Ki" . 0) ("Ted" . 0) ("Brian" . 1) ("Jenny" . 0))
                #hash(("Ki" . 0) ("Ted" . 0) ("Brian" . 2) ("Jenny" . 0))
                #hash(("Ki" . 0) ("Ted" . 0) ("Brian" . 3) ("Jenny" . 0))
                #hash(("Ki" . 0) ("Ted" . 0) ("Brian" . 4) ("Jenny" . 0))))

(check-equal? (for/list ([i (below/e 10)]) i) (build-list 10 values))
(check-equal? (for/list ([i natural/e][j (in-range 10)]) i) (build-list 10 values))
(check-equal? (for/list ([i (in-enum (below/e 10))]) i) (build-list 10 values))
(check-equal? (for/list ([i (in-enum natural/e)][j (in-range 10)]) i) (build-list 10 values))
(check-equal? (let ([es (in-enum (below/e 10))]) (for/list ([i es]) i)) (build-list 10 values))

(define (to-str e print?)
  (define sp (open-output-string))
  (if print?
      (print e sp)
      (write e sp))
  (get-output-string sp))
;; printer tests
(check-equal? (to-str natural/e #t) "#<infinite-enum: 0 1 2 3 4 5 6 7 8 9 10...>")
(check-equal? (to-str (cons/e natural/e natural/e) #t) "#<infinite-enum: '(0 . 0) '(0 . 1) '(1 . 0)...>")
(check-equal? (to-str (cons/e natural/e natural/e) #f) "#<infinite-enum: (0 . 0) (0 . 1) (1 . 0)...>")
(check-equal? (to-str (fin/e 0) #t) "#<1-count-enum: 0>")
(check-equal? (to-str (pam/e values natural/e #:contract exact-nonnegative-integer?) #t)
              "#<infinite-one-way-enum: 0 1 2 3 4 5 6 7 8 9 10...>")
(check-equal? (to-str (pam/e values (below/e 3) #:contract (integer-in 0 2)) #t)
              "#<3-count-one-way-enum: 0 1 2>")
(check-equal? (to-str (below/e 1000000000) #t)
              "#<finite-enum: 0 1 2 3 4 5 6 7 8 9 10...>")
;; just check that it doesn't crash when we get deep nesting
;; (checks that we end up in the case that just uses the string
;; in the implementation of the enumerator printer)
(check-equal? (string? (to-str
                        (map/e (λ (i)
                                 (map/e (λ (j)
                                          (map/e (λ (k) (+ i j k))
                                                 (λ (k) (- k (+ i j)))
                                                 natural/e
                                                 #:contract exact-nonnegative-integer?))
                                        (λ (e) (- (from-nat e 0) i))
                                        natural/e
                                        #:contract enum?))
                               (λ (e) (from-nat (from-nat e 0) 0))
                               natural/e
                               #:contract enum?)
                        #t))
              #t)

(check-contract natural/e)
(check-contract (cons/e natural/e natural/e))
(check-contract (cons/e natural/e natural/e #:ordering 'diagonal))
(check-contract (except/e natural/e 0))
(check-contract (below/e 50))
(check-contract (fin/e 1 2 #f 'c +inf.0 +nan.0 '#:x))
(check-contract (or/e (cons (cons/e natural/e natural/e) pair?)
                      (cons natural/e real?)))
(check-contract (map/e add1 sub1 natural/e #:contract (and/c exact-integer? positive?)))

;; use pam/e to skip the to-nat check (it gets slow)
(check-contract (let ([e (listof/e natural/e)])
                  (pam/e values e #:contract (enum-contract e))))

(check-contract 
 (cons/de [i natural/e]
          [tl (i)
              (map/e (λ (x) (+ x i)) (λ (x) (- x i)) natural/e 
                     #:contract 
                     (and/c (>=/c i) exact-integer?))]))
(check-contract integer/e)
(check-contract flonum/e)
(check-contract exact-rational/e)
(check-contract two-way-real/e)
(check-contract real/e)
(check-contract two-way-number/e)
(check-contract number/e)
(check-contract (slice/e natural/e 10 20))
(check-contract (permutations-of-n/e 4))
(check-contract (permutations/e '(a b c)))
(check-contract (range/e -inf.0 10))
(check-contract (range/e 10 +inf.0))
(check-contract (range/e -inf.0 +inf.0))
(check-contract (range/e -10 10))
(check-contract (delay/e natural/e))

(check-not-exn
 (λ ()
   (define HOW-MANY 5000)
   
   (define (test-seq K seq)
     (define d->i (make-hasheq))
     (for ([i (in-range HOW-MANY)]
           [d seq])
       (hash-update! d->i d add1 0))
     
     (define total
       (for/fold ([cnt 0]) ([i (in-range K)])
         (define i-cnt (hash-ref d->i i 0))
         (+ cnt i-cnt)))
     
     (unless (= HOW-MANY total)
       (error 'digits "Missed some: ~a" total)))
   
   (define (test-digits N)
     (test-seq 10 (in-generator (unsafe:BPP-digits N))))
   
   (test-digits 1)
   (test-digits 9)
   
   (define (test-tetris K N)
     (test-seq K (unsafe:10-sequence->K-sequence K (in-generator (unsafe:BPP-digits N)))))
   
   (test-tetris 7 1)
   (test-tetris 7 2)
   (test-tetris 15 1)
   (test-tetris 15 2)
   
   (test-tetris 100 2)))

(require rackunit/docs-complete)
(check-docs 'data/enumerate)
(check-docs 'data/enumerate/lib)

(check-pred exact-nonnegative-integer? (random-index natural/e))
(check-pred (and/c exact-nonnegative-integer?
                   (<=/c 5))
            (random-index (below/e 5)))

;; test to be sure that predicates are coerced
;; to contracts properly by or/e's contract ...
(check-not-exn
 (λ ()
   (or/e
    (map/e (λ (x) 'x) (λ (x) 0) (below/e 1) #:contract 'x)
    (map/e (λ (x) 'y) (λ (x) 0) (below/e 1) #:contract 'y))))

;; ... and by or/e itself
(check-not-exn
 (λ ()
   (define type/e
     (delay/e
      (or/e (single/e 'nat)
            (list/e (single/e '->) type/e type/e))))
   
   (to-nat
    (cons/de
     [type type/e]
     [e (type)
        natural/e])
    '(nat . 0))))
