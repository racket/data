#lang racket/base
(require racket/match
         racket/contract/base
         racket/dict
         racket/generic
         "private/skip-list.rkt"
         "order.rkt")
;; owned by ryanc

#|
reference
  Skip Lists: A Probabilistic Alternative to Balanced Trees
  by William Pugh
|#

(define none (gensym 'none))

(define (skip-list-ref s key [default none])
  (define head (skip-list-head s))
  (define result
    (search head (item-level head) key (skip-list-=? s) (skip-list-<? s)))
  (cond [result (item-data result)]
        [(eq? default none)
         (error 'skip-list-ref "no mapping found for key\n  key: ~e" key)]
        [(procedure? default) (default)]
        [else default]))

(define (skip-list-set! s key data)
  (define head (skip-list-head s))
  (define =? (skip-list-=? s))
  (define <? (skip-list-<? s))
  (define max-level (max MAX-LEVEL (add1 (item-level head))))
  (define result ;; new Item or #f
    (update/insert head (item-level head) key data =? <? max-level))
  (when result
    (when (skip-list-num-entries s)
      (set-skip-list-num-entries! s (add1 (skip-list-count s))))
    (when (> (item-level result) (item-level head))
      (let ([new-head (resize-item head (item-level result))])
        (set-item-next! new-head (item-level result) result)
        (set-skip-list-head! s new-head)))))

(define (skip-list-remove! s key)
  (define head (skip-list-head s))
  (define =? (skip-list-=? s))
  (define <? (skip-list-<? s))
  (define deleted
    (delete head (item-level head) key =? <?))
  (when (and deleted (skip-list-num-entries s))
    (set-skip-list-num-entries! s (sub1 (skip-list-count s))))
  (unless (or (item? (item-next head (item-level head)))
              (= 1 (item-level head)))
    ;; Trim head
    (let ([new-head (resize-item head (sub1 (item-level head)))])
      (set-skip-list-head! s new-head))))

(define (skip-list-remove-range! s from to)
  (match s
    [(skip-list head count =? <?)
     (delete-range head head (item-level head) from to <? #f)
     (set-skip-list-num-entries! s #f)]))

(define (skip-list-contract! s from to)
  (match s
    [(adjustable-skip-list head count =? <?)
     (delete-range head head (item-level head) from to <? #t)
     (set-skip-list-num-entries! s #f)]))

(define (skip-list-expand! s from to #:gravity [gravity 'right])
  (match s
    [(adjustable-skip-list head count =? <?)
     (let ([adj-from
            ;; Note: left-gravity relies on adjustable skip-list restriction to ints!
            (case gravity
              ((left) (add1 from))
              ((right) from)
              (else (error 'skip-list-expand! "bad gravity: ~e" gravity)))])
       (expand/right-gravity! head (item-level head) adj-from (- to from)))]))

;; Dict methods

(define (skip-list-count s)
  (let ([n (skip-list-num-entries s)])
    (or n
        (let loop ([n 0] [item (item-next (skip-list-head s) 1)])
          (cond [item (loop (add1 n) (item-next item 1))]
                [else
                 (set-skip-list-num-entries! s n)
                 n])))))

(struct skip-list-iter (s item))

(define (check-iter who s iter)
  (unless (skip-list-iter? iter)
    (raise-argument-error who "skip-list-iter?" iter))
  (unless (eq? (skip-list-iter-s iter) s)
    (error who "skip-list-iter does not match skip-list")))

(define (skip-list-iterate-first s)
  (let ([next (item-next (skip-list-head s) 1)])
    (and next (skip-list-iter s next))))

(define (skip-list-iterate-next s iter)
  (check-iter 'skip-list-iterate-next s iter)
  (let ([next (item-next (skip-list-iter-item iter) 1)])
    (and next (skip-list-iter s next))))

(define (skip-list-iterate-key s iter)
  (check-iter 'skip-list-iterate-key s iter)
  (item-key (skip-list-iter-item iter)))

(define (skip-list-iterate-value s iter)
  (check-iter 'skip-list-iterate-key s iter)
  (item-data (skip-list-iter-item iter)))

;; Extensions

;; Returns greatest/rightmost item s.t. key(item) < key
(define (skip-list-iterate-greatest/<? s key)
  (let* ([head (skip-list-head s)]
         [<? (skip-list-<? s)]
         [item (closest head (item-level head) key <?)])
    (and (not (eq? item head)) (skip-list-iter s item))))

;; Returns greatest/rightmost item s.t. key(item) <= key
(define (skip-list-iterate-greatest/<=? s key)
  (let* ([head (skip-list-head s)]
         [<? (skip-list-<? s)]
         [=? (skip-list-=? s)]
         [item< (closest head (item-level head) key <?)]
         [item1 (item-next item< 1)])
    (cond [(and item1 (=? (item-key item1) key))
           (skip-list-iter s item1)]
          [(eq? item< head)
           #f]
          [else
           (skip-list-iter s item<)])))

;; Returns least/leftmost item s.t. key(item) > key
(define (skip-list-iterate-least/>? s key)
  (let* ([head (skip-list-head s)]
         [<? (skip-list-<? s)]
         [item< (closest head (item-level head) key <?)]
         ;; If head, nudge forward one so comparisons are valid.
         [item< (if (eq? item< head) (item-next item< 1) item<)])
    (let loop ([item item<])
      (and item
           (if (<? key (item-key item))
               (skip-list-iter s item)
               (loop (item-next item 1)))))))

;; Returns least/leftmost item s.t. key(item) >= key
(define (skip-list-iterate-least/>=? s key)
  (let* ([head (skip-list-head s)]
         [<? (skip-list-<? s)]
         [item (closest head (item-level head) key <?)]
         [item (item-next item 1)])
    (and item (skip-list-iter s item))))

(define (skip-list-iterate-least s)
  (let* ([head (skip-list-head s)]
         [item (item-next head 1)])
    (and item (skip-list-iter s item))))

(define (skip-list-iterate-greatest s)
  (let* ([head (skip-list-head s)]
         [item (closest head (item-level head)
                        ;; replace standard comparison with "always <",
                        ;; so closest yields max item
                        'unused
                        (lambda (x y) #t))])
    (and item (skip-list-iter s item))))

(define (skip-list->list s)
  (let loop ([item (item-next (skip-list-head s) 1)])
    (if item
        (cons (cons (item-key item) (item-data item))
              (loop (item-next item 1)))
        null)))

;; ============================================================

(define dict-methods
  (vector-immutable skip-list-ref
                    skip-list-set!
                    #f ;; set
                    skip-list-remove!
                    #f ;; remove
                    skip-list-count
                    skip-list-iterate-first
                    skip-list-iterate-next
                    skip-list-iterate-key
                    skip-list-iterate-value))

(struct skip-list ([head #:mutable] [num-entries #:mutable] =? <?)
        #:property prop:dict/contract
        (list dict-methods
              (vector-immutable any/c any/c skip-list-iter?
                                #f #f #f))
        #:methods gen:ordered-dict
        [(define dict-iterate-least skip-list-iterate-least)
         (define dict-iterate-greatest skip-list-iterate-greatest)
         (define dict-iterate-least/>? skip-list-iterate-least/>?)
         (define dict-iterate-least/>=? skip-list-iterate-least/>=?)
         (define dict-iterate-greatest/<? skip-list-iterate-greatest/<?)
         (define dict-iterate-greatest/<=? skip-list-iterate-greatest/<=?)])

(struct skip-list* skip-list (key-c value-c)
        #:property prop:dict/contract
        (list dict-methods
              (vector-immutable any/c any/c skip-list-iter?
                                (lambda (s) (skip-list*-key-c s))
                                (lambda (s) (skip-list*-value-c s))
                                #f))
        #:methods gen:ordered-dict
        [(define dict-iterate-least skip-list-iterate-least)
         (define dict-iterate-greatest skip-list-iterate-greatest)
         (define dict-iterate-least/>? skip-list-iterate-least/>?)
         (define dict-iterate-least/>=? skip-list-iterate-least/>=?)
         (define dict-iterate-greatest/<? skip-list-iterate-greatest/<?)
         (define dict-iterate-greatest/<=? skip-list-iterate-greatest/<=?)])

(struct adjustable-skip-list skip-list ()
        #:property prop:dict/contract
        (list dict-methods
              (vector-immutable exact-integer? any/c skip-list-iter?
                                #f #f #f)))

(struct adjustable-skip-list* adjustable-skip-list (key-c value-c)
        #:property prop:dict/contract
        (list dict-methods
              (vector-immutable exact-integer? any/c skip-list-iter?
                                (lambda (s) (adjustable-skip-list*-key-c s))
                                (lambda (s) (adjustable-skip-list*-value-c s))
                                #f))
        #:methods gen:ordered-dict
        [(define dict-iterate-least skip-list-iterate-least)
         (define dict-iterate-greatest skip-list-iterate-greatest)
         (define dict-iterate-least/>? skip-list-iterate-least/>?)
         (define dict-iterate-least/>=? skip-list-iterate-least/>=?)
         (define dict-iterate-greatest/<? skip-list-iterate-greatest/<?)
         (define dict-iterate-greatest/<=? skip-list-iterate-greatest/<=?)])

(define (make-skip-list [ord datum-order]
                        #:key-contract [key-contract any/c]
                        #:value-contract [value-contract any/c])
  (let ([key-contract (and/c* (order-domain-contract ord) key-contract)]
        [=? (order-=? ord)]
        [<? (order-<? ord)])
    (cond [(and (eq? key-contract any/c) (eq? value-contract any/c))
           (skip-list (vector 'head 'head #f) 0 =? <?)]
          [else
           (skip-list* (vector 'head 'head #f) 0 =? <?
                       key-contract value-contract)])))

(define (make-adjustable-skip-list #:key-contract [key-contract any/c]
                                   #:value-contract [value-contract any/c])
  (cond [(and (eq? key-contract any/c) (eq? value-contract any/c))
         (adjustable-skip-list (vector 'head 'head #f) 0 = <)]
        [else
         (adjustable-skip-list* (vector 'head 'head #f) 0 = <
                                key-contract value-contract)]))


(define (key-c s)
  (cond [(skip-list*? s) (skip-list*-key-c s)]
        [(adjustable-skip-list*? s)
         (and/c* exact-integer? (adjustable-skip-list*-key-c s))]
        [else any/c]))
(define (val-c s)
  (cond [(skip-list*? s) (skip-list*-value-c s)]
        [(adjustable-skip-list*? s) (adjustable-skip-list*-value-c s)]
        [else any/c]))

(define (and/c* x y)
  (cond [(eq? x any/c) y]
        [(eq? y any/c) x]
        [else (and/c x y)]))

;; ============================================================

(provide/contract
 [make-skip-list
  (->* ()
       (order? #:key-contract contract? #:value-contract contract?)
       skip-list?)]
 [make-adjustable-skip-list
  (->* ()
       (#:key-contract contract? #:value-contract contract?)
       adjustable-skip-list?)]
 [skip-list?
  (-> any/c boolean?)]
 [adjustable-skip-list?
  (-> any/c boolean?)]

 [skip-list-ref
  (->i ([s skip-list?] [k (s) (key-c s)])
       ([d any/c])
       any)]
 [skip-list-set!
  (->i ([s skip-list?] [k (s) (key-c s)] [v (s) (val-c s)]) [_r void?])]
 [skip-list-remove!
  (->i ([s skip-list?] [k (s) (key-c s)]) [_r void?])]
 [skip-list-count
  (-> skip-list? exact-nonnegative-integer?)]

 [skip-list-remove-range!
  (->i ([s skip-list?] [from (s) (key-c s)] [to (s) (key-c s)])
       [_r void?])]
 [skip-list-contract! 
  (->i ([s adjustable-skip-list?] [from (s) (key-c s)] [to (s) (key-c s)])
       [_r void?])]
 [skip-list-expand!
  (->i ([s adjustable-skip-list?] [from (s) (key-c s)] [to (s) (key-c s)])
       (#:gravity [g (or/c 'left 'right)])
       [_r void?])]

 [skip-list-iterate-first
  (-> skip-list? (or/c skip-list-iter? #f))]
 [skip-list-iterate-next
  (-> skip-list? skip-list-iter? (or/c skip-list-iter? #f))]
 [skip-list-iterate-key
  (->i ([s skip-list?] [i skip-list-iter?]) [_r (s) (key-c s)])]
 [skip-list-iterate-value
  (->i ([s skip-list?] [i skip-list-iter?]) [_r (s) (val-c s)])]

 [skip-list-iterate-greatest/<=?
  (->i ([s skip-list?] [k (s) (key-c s)]) [_r (or/c skip-list-iter? #f)])]
 [skip-list-iterate-greatest/<?
  (->i ([s skip-list?] [k (s) (key-c s)]) [_r (or/c skip-list-iter? #f)])]
 [skip-list-iterate-least/>=?
  (->i ([s skip-list?] [k (s) (key-c s)]) [_r (or/c skip-list-iter? #f)])]
 [skip-list-iterate-least/>?
  (->i ([s skip-list?] [k (s) (key-c s)]) [_r (or/c skip-list-iter? #f)])]

 [skip-list-iterate-least
  (-> skip-list? (or/c skip-list-iter? #f))]
 [skip-list-iterate-greatest
  (-> skip-list? (or/c skip-list-iter? #f))]

 [skip-list-iter?
  (-> any/c any)]

 [skip-list->list
  (-> skip-list? list?)])
