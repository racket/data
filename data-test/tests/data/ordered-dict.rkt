#lang racket/base
(require rackunit
         rackunit/text-ui
         racket/contract
         racket/dict
         data/skip-list
         ;; (prefix-in nc: (submod data/skip-list no-contracts))
         data/splay-tree
         data/order)

;; Tests for ordered dictionaries
;;   - skip-list
;;   - splay-tree (both kinds)

(define KEY-CT    5000)
(define REM-CT     500)
(define SEARCH-CT  5000)

(define VAL-LB -100000)
(define VAL-UB  100000)
(define (rand) (+ (random (- VAL-UB VAL-LB)) VAL-LB))

(define TEST? #t)
(define LOUD? #f)
(define IDK? #f)

(define-syntax-rule (time* label body ...)
  (let ([f (lambda () body ...)]) (if LOUD? (timef label f) (f))))

(define (timef label f)
  (let-values ([(vs cpu real gc) (time-apply f null)])
    (printf "  ~a: cpu ~s, real ~s, gc ~s\n" label cpu real gc)
    (apply values vs)))

(define-syntax-rule (rand-test dicts ordered? idk?
                               (-ref
                                -set!
                                -remove!
                                -count
                                -has-key?
                                -iterate-key
                                -iterate-least/>?
                                -iterate-least/>=?
                                -iterate-greatest/<?
                                -iterate-greatest/<=?))
  (let ([hash (make-hash)])

    (define (check-equal? x y [msg #f]) ;; rackunit check-equal? is apparently slow
      (unless (equal? x y)
        (error 'check-equal? "not equal:\n~e\n~e" x y)))

    (time* "set!"
    (for ([c (in-range KEY-CT)])
      (let* ([k (rand)]
             [v (rand)])
        (hash-set! hash k v)
        (for ([d dicts])
          (-set! d k v)))))

    (for ([d dicts])
      (check-equal? (hash-count hash)
                    (-count d)))

    (when #f
      (time* "seq ref"
      ;; Sequential access
      (for ([i (in-range VAL-LB VAL-UB)])
        (for ([d dicts])
          (let* ([vh (hash-ref hash i 'not-there)]
                 [vd (-ref d i 'not-there)])
            (check-equal? vh vd))))))

    ;; Random removal
    (time* "remove"
    (for ([i (in-range REM-CT)])
      (let ([k (rand)])
        (for ([d dicts])
          (hash-remove! hash k)
          (-remove! d k)
          (check-equal? (hash-count hash) (-count d))))))

    ;; Lookup
    (time* "rnd ref"
    (for ([c (in-range SEARCH-CT)])
      (let ([i (rand)])
        (for ([d dicts])
          (let* ([vh (hash-ref hash i 'not-there)]
                 [vd (-ref d i 'not-there)])
            (check-equal? vh vd))))))

    (when ordered?
      (time* "ordered"
      (for ([c (in-range SEARCH-CT)])
        (let* ([k0 (rand)])
          (for ([d dicts])
            (let* ([has? (-has-key? d k0)]
                   [l>i (-iterate-least/>? d k0)]
                   [l>=i (-iterate-least/>=? d k0)]
                   [g<i (-iterate-greatest/<? d k0)]
                   [g<=i (-iterate-greatest/<=? d k0)]
                   [l> (and l>i (-iterate-key d l>i))]
                   [l>= (and l>=i (-iterate-key d l>=i))]
                   [g< (and g<i (-iterate-key d g<i))]
                   [g<= (and g<=i (-iterate-key d g<=i))])
              (when has?
                (check-equal? l>= g<= "has, should be same"))
              (unless has?
                (check-equal? l> l>= "not has, should be same")
                (check-equal? g< g<= "not has, should be same"))
              (when l> (check > l> k0))
              (when l>= (check >= l>= k0))
              (when g< (check < g< k0))
              (when g<= (check <= g<= k0))
              (when (and IDK? idk? (zero? (modulo c 15)))
                (for ([k (in-dict-keys d)])
                  (when (and l> (and (> k k0) (< k l>))) (error "l>"))
                  (when (and l>= (and (>= k k0) (< k l>=))) (error "l>="))
                  (when (and g< (and (< k k0) (> k g<))) (error "g<"))
                  (when (and g<= (and (<= k k0) (> k g<=))) (error "g<="))))))))))
    ))

;; Test dict interface

(define (dict-test dicts ordered? [idk? #f])
  (rand-test dicts ordered? idk?
             (dict-ref
              dict-set!
              dict-remove!
              dict-count
              dict-has-key?
              dict-iterate-key
              dict-iterate-least/>?
              dict-iterate-least/>=?
              dict-iterate-greatest/<?
              dict-iterate-greatest/<=?)))

(define-syntax-rule (tc name body ...)
  (test-case name (printf "Test ~s\n" name) (timef "total" (lambda () body ...))))

(when TEST?
  (when #t (printf "== dict interface\n"))
  (tc "skip-list, datum-order, dict interface"
      (dict-test (list (make-skip-list)) #t #t))
  (tc "skip-list, < = order, dict interface"
      (dict-test (list (make-skip-list (order 'my-order any/c = <))) #t #t))
  (tc "adjustable-skip-list, dict interface"
      (dict-test (list (make-adjustable-skip-list)) #t #t))
  (tc "splay-tree, datum-order, dict interface"
      (dict-test (list (make-splay-tree)) #t #t))
  (tc "splay-tree, < = order, dict interface"
      (dict-test (list (make-splay-tree (order 'mine any/c = <))) #t #t))
  (tc "adjustable-splay-tree, dict interface"
      (dict-test (list (make-adjustable-splay-tree)) #t #t))
  (when #t (printf "\n")))

(provide dict-test)

;; Test splay-tree interface

(define (splay-test dicts ordered? [idk? #f])
  (rand-test dicts ordered? idk?
             (splay-tree-ref
              splay-tree-set!
              splay-tree-remove!
              splay-tree-count
              dict-has-key?
              splay-tree-iterate-key
              splay-tree-iterate-least/>?
              splay-tree-iterate-least/>=?
              splay-tree-iterate-greatest/<?
              splay-tree-iterate-greatest/<=?)))

(when TEST?
  (when #t (printf "== splay-tree interface\n"))
  (tc "splay-tree, datum-order, custom interface"
      (splay-test (list (make-splay-tree)) #t #t))
  (tc "splay-tree, < = order, custom interface"
      (splay-test (list (make-splay-tree (order 'mine any/c = <))) #t #t))
  (tc "adjustable-splay-tree, custom interface"
      (splay-test (list (make-adjustable-splay-tree)) #t #t))
  (when #t (printf "\n")))

(provide splay-test)

;; Test skip-list interface

(define (skip-test dicts ordered? [idk? #f])
  (rand-test dicts ordered? idk?
             (skip-list-ref
              skip-list-set!
              skip-list-remove!
              skip-list-count
              dict-has-key?
              skip-list-iterate-key
              skip-list-iterate-least/>?
              skip-list-iterate-least/>=?
              skip-list-iterate-greatest/<?
              skip-list-iterate-greatest/<=?)))

(when TEST?
  (when #t (printf "== skip-list interface\n"))
  (tc "skip-list, datum-order, custom interface"
      (skip-test (list (make-skip-list)) #t #t))
  (tc "skip-list, < = order, custom interface"
      (skip-test (list (make-skip-list (order 'mine any/c = <))) #t #t))
  (tc "adjustable-skip-list, custom interface"
      (skip-test (list (make-adjustable-skip-list)) #t #t))
  (when #t (printf "\n")))

(provide skip-test)

#|
(define (nc:skip-test dicts ordered? [idk? #f])
  (rand-test dicts ordered? idk?
             (nc:skip-list-ref
              nc:skip-list-set!
              nc:skip-list-remove!
              nc:skip-list-count
              dict-has-key?
              nc:skip-list-iterate-key
              nc:skip-list-iterate-least/>?
              nc:skip-list-iterate-least/>=?
              nc:skip-list-iterate-greatest/<?
              nc:skip-list-iterate-greatest/<=?)))

(when TEST?
  (when #t (printf "== skip-list interface w/o contracts\n"))
  (tc "skip-list, datum-order, custom interface"
      (nc:skip-test (list (nc:make-skip-list)) #t #t))
  (tc "skip-list, < = order, custom interface"
      (nc:skip-test (list (nc:make-skip-list (order 'mine any/c = <))) #t #t))
  (tc "adjustable-skip-list, custom interface"
      (nc:skip-test (list (nc:make-adjustable-skip-list)) #t #t))
  (when #t (printf "\n")))
|#

;; Test hash interface
;; for speed comparison only

(define (hash-test dicts ordered? _idk?)
  (when ordered?
    (error 'hash-tests "ordered not supported"))
  (rand-test dicts #f #f
             (hash-ref
              hash-set!
              hash-remove!
              hash-count
              hash-has-key?
              '-iterate-key
              '-iterate-least/>?
              '-iterate-least/>=?
              '-iterate-greatest/<?
              '-iterate-greatest/<=?)))

(provide hash-test)

;; ============================================================
;; Performance tests
;; ============================================================

(define (p name testf mkd ordered?)
  (collect-garbage)
  (collect-garbage)
  (let-values ([(_result cpu real gc)
                (time-apply
                 (lambda ()
                   (for ([i (in-range 5)])
                     (testf (list (mkd)) ordered? ordered?)))
                 null)])
    (printf "~a : ~s\n" name real)))

(define (mksplay) (make-splay-tree))
(define (mkasplay) (make-adjustable-splay-tree))
(define (mkcsplay) (make-splay-tree real-order))
(define (mkskip) (make-skip-list))
(define (mkcskip) (make-skip-list real-order))
(define (mkaskip) (make-adjustable-skip-list))

(define (performance)
  (when #t
  (display "Using ordered-dict interface, w/ search\n")
  (p "skip-list " dict-test mkskip #t)
  (p "adj skip  " dict-test mkaskip #t)
  (p "skip w/ c " dict-test mkcskip #t)
  (p "splay-tree" dict-test mksplay #t)
  (p "adj splay " dict-test mkasplay #t)
  (p "splay w/ c" dict-test mkcsplay #t)
  (newline)
  (display "Using custom interfaces, w/ search\n")
  (p "skip-list " skip-test mkskip #t)
  (p "adj skip  " skip-test mkaskip #t)
  (p "skip w/ c " skip-test mkcskip #t)
  (p "splay-tree" splay-test mksplay #t)
  (p "adj splay " splay-test mkasplay #t)
  (p "splay w/ c" splay-test mkcsplay #t)
  ;; (p "nc skip   " nc:skip-test mkskip #t)
  ;; (p "nc adjskip" nc:skip-test mkaskip #t)
  (newline)
  )
  (display "Using custom interfaces, w/o search\n")
  (p "skip-list " skip-test mkskip #f)
  (p "adj skip  " skip-test mkaskip #f)
  (p "skip w/ c " skip-test mkcskip #f)
  (p "splay-tree" splay-test mksplay #f)
  (p "adj splay " splay-test mkasplay #f)
  (p "splay w/ c" splay-test mkcsplay #f)
  ;; (p "nc skip   " nc:skip-test mkskip #f)
  ;; (p "nc adjskip" nc:skip-test mkaskip #f)
  (p "hash      " hash-test make-hash #f)
  (newline))

(provide performance)

(define (deep-test [test 'splay] [count 100])
  (let ([mk (case test
              ((splay) mksplay)
              ((asplay) mkasplay)
              ((skip) mkskip)
              ((askip) mkaskip))])
    (for ([seed (in-range count)])
      (random-seed seed)
      (printf "seed = ~s\n" seed)
      (p "test" dict-test mk #t))))

(provide deep-test)

#|
Run (8/22/2013):

Using ordered-dict interface, w/ search
splay-tree : 3104
adj splay  : 3098
skip-list  : 2975
adj skip   : 2863
splay w/ c : 3984
skip w/ c  : 3831

Using custom interfaces, w/ search
splay-tree : 2490
adj splay  : 2560
skip-list  : 2441
adj skip   : 2329
splay w/ c : 2559
skip w/ c  : 2444

Using custom interfaces, w/o search
splay-tree : 224
adj splay  : 249
skip-list  : 190
adj skip   : 156
splay w/ c : 216
skip w/ c  : 175
hash       : 26

Conclusions:

 - generic interface is somewhat costly
 - even more costly combined with instance contracts
 - in-dict-keys is slow for splay trees

|#

;; regression test

(printf "== regression tests\n")
(run-tests
 (test-suite "splay-tree"
             (test-case "splay-tree->list"
               (define t (make-splay-tree))
               (splay-tree-set! t 1 'a)
               (splay-tree-set! t 2 'b)
               (splay-tree-set! t 3 'c)
               (check-equal? (splay-tree->list t)
                             '((1 . a) (2 . b) (3 . c))))))
