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
  (define cmp (skip-list-cmp s))
  (define result (search head (item-level head) key cmp))
  (cond [result (item-data result)]
        [(eq? default none)
         (error 'skip-list-ref "no mapping found for key\n  key: ~e" key)]
        [(procedure? default) (default)]
        [else default]))

(define (skip-list-set! s key data)
  (define head (skip-list-head s))
  (define cmp (skip-list-cmp s))
  (define max-level (min MAX-LEVEL (add1 (item-level head))))
  (define result ;; new Item or #f
    (update/insert head (item-level head) key data cmp max-level))
  (when result
    (when (skip-list-num-entries s)
      (set-skip-list-num-entries! s (add1 (skip-list-count s))))
    (when (> (item-level result) (item-level head))
      (let ([new-head (resize-item head (item-level result))])
        (set-item-next! new-head (item-level result) result)
        (set-skip-list-head! s new-head)))))

(define (skip-list-remove! s key)
  (define head (skip-list-head s))
  (define cmp (skip-list-cmp s))
  (define deleted (delete! head (item-level head) key cmp))
  (when deleted
    (set-skip-list-timestamp! s (add1 (skip-list-timestamp s)))
    (when (skip-list-num-entries s)
      (set-skip-list-num-entries! s (sub1 (skip-list-num-entries s)))))
  (unless (or (item? (item-next head (item-level head)))
              (= 1 (item-level head)))
    ;; Trim head
    ;; FIXME: trim head less often?
    (let ([new-head (resize-item head (sub1 (item-level head)))])
      (set-skip-list-head! s new-head))))

(define (skip-list-remove-range! s from to)
  (match s
    [(skip-list head count timestamp cmp)
     (define deleted
       (delete-range! head head (item-level head) from to cmp #f))
     (when deleted
       (set-skip-list-timestamp! s (add1 timestamp))
       (set-skip-list-num-entries! s #f))]))

(define (skip-list-contract! s from to)
  (match s
    [(adjustable-skip-list head count timestamp cmp)
     (define deleted
       (delete-range! head head (item-level head) from to cmp #t))
     (when deleted
       (set-skip-list-timestamp! s (add1 timestamp))
       (set-skip-list-num-entries! s #f))]))

(define (skip-list-expand! s from to)
  (match s
    [(adjustable-skip-list head count timestamp cmp)
     (expand/right-gravity! head (item-level head) from (- to from))
     (set-skip-list-timestamp! s (add1 timestamp))]))

;; Dict methods

(define (skip-list-count s)
  (or (skip-list-num-entries s)
      (let loop ([n 0] [item (item-next (skip-list-head s) 1)])
        (cond [item (loop (add1 n) (item-next item 1))]
              [else
               (set-skip-list-num-entries! s n)
               n]))))

(struct skip-list-iter (s item [timestamp #:mutable]))

;; check-iter : symbol skip-list iter boolean -> boolean
;; If ok returns #t; if deleted returns #f if allow-deleted?, else raises error.
(define (check-iter who s iter allow-deleted?)
  (unless (skip-list-iter? iter)
    (raise-argument-error who "skip-list-iter?" iter))
  (unless (eq? s (skip-list-iter-s iter))
    (error who "iterator does not belong to given skip-list"))
  (or (= (skip-list-timestamp s) (skip-list-iter-timestamp iter))
      (let ([head (skip-list-head s)]
            [item (skip-list-iter-item iter)])
        (let-values ([(item status) (repair head (item-level head) item)])
          (cond [(eq? status 'valid)
                 (set-skip-list-iter-timestamp! iter (skip-list-timestamp s))
                 #t]
                [allow-deleted?
                 #f]
                [else
                 (error who "iterator invalidated by deletion")])))))

(define (skip-list-iterate-first s)
  (let ([next (item-next (skip-list-head s) 1)])
    (and next (skip-list-iter s next (skip-list-timestamp s)))))

(define (skip-list-iterate-next s iter)
  (check-iter 'skip-list-iterate-next s iter #t)
  (cond [(= (skip-list-timestamp s) (skip-list-iter-timestamp iter))
         (let ([next (item-next (skip-list-iter-item iter) 1)])
           (and next (skip-list-iter s next (skip-list-timestamp s))))]
        [else
         (let ([head (skip-list-head s)]
               [item (skip-list-iter-item iter)])
           (let-values ([(item status) (repair head (item-level head) item)])
             (case status
               ((valid)
                (let ([next (item-next item 1)])
                  (and next (skip-list-iter s next (skip-list-timestamp s)))))
               ((deleted)
                (and item (skip-list-iter s item (skip-list-timestamp s))))
               ((failed)
                (error 'skip-list-iterate-next
                       "internal error: iterator invalidated by deletion")))))]))

(define (skip-list-iterate-key s iter)
  (check-iter 'skip-list-iterate-key s iter #f)
  (item-key (skip-list-iter-item iter)))

(define (skip-list-iterate-value s iter)
  (check-iter 'skip-list-iterate-value s iter #f)
  (item-data (skip-list-iter-item iter)))

(define (skip-list-iter-valid? iter)
  (check-iter 'skip-list-iter-valid? (skip-list-iter-s iter) iter #t))

;; Extensions

;; Returns greatest/rightmost item s.t. key(item) < key
(define (skip-list-iterate-greatest/<? s key)
  (let* ([head (skip-list-head s)]
         [cmp (skip-list-cmp s)]
         [item (closest head (item-level head) key cmp)])
    (and (not (eq? item head))
         (skip-list-iter s item (skip-list-timestamp s)))))

;; Returns greatest/rightmost item s.t. key(item) <= key
(define (skip-list-iterate-greatest/<=? s key)
  (let* ([head (skip-list-head s)]
         [cmp (skip-list-cmp s)]
         [item< (closest head (item-level head) key cmp)]
         [item1 (item-next item< 1)])
    (cond [(and item1 (=? cmp (item-key item1) key))
           (skip-list-iter s item1 (skip-list-timestamp s))]
          [(eq? item< head)
           #f]
          [else
           (skip-list-iter s item< (skip-list-timestamp s))])))

;; Returns least/leftmost item s.t. key(item) > key
(define (skip-list-iterate-least/>? s key)
  (let* ([head (skip-list-head s)]
         [cmp (skip-list-cmp s)]
         [item< (closest head (item-level head) key cmp)]
         ;; If head, nudge forward one so comparisons are valid.
         [item< (if (eq? item< head) (item-next item< 1) item<)])
    (let loop ([item item<])
      (and item
           (if (<? cmp key (item-key item))
               (skip-list-iter s item (skip-list-timestamp s))
               (loop (item-next item 1)))))))

;; Returns least/leftmost item s.t. key(item) >= key
(define (skip-list-iterate-least/>=? s key)
  (let* ([head (skip-list-head s)]
         [cmp (skip-list-cmp s)]
         [item (closest head (item-level head) key cmp)]
         [item (item-next item 1)])
    (and item (skip-list-iter s item (skip-list-timestamp s)))))

(define (skip-list-iterate-least s)
  (let* ([head (skip-list-head s)]
         [item (item-next head 1)])
    (and item (skip-list-iter s item (skip-list-timestamp s)))))

(define (skip-list-iterate-greatest s)
  (let* ([head (skip-list-head s)]
         [item (closest head (item-level head)
                        ;; replace standard comparison with "always <",
                        ;; so closest yields max item
                        'unused
                        (lambda (x y) '<))])
    (and item (skip-list-iter s item (skip-list-timestamp s)))))

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

(struct skip-list ([head #:mutable] [num-entries #:mutable] [timestamp #:mutable] cmp)
        ;; cmp is either procedure or #f (numeric order); see private/skip-list
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
        [cmp (order-comparator ord)])
    (cond [(and (eq? key-contract any/c) (eq? value-contract any/c))
           (skip-list (vector 'head 'head #f) 0 0 cmp)]
          [else
           (skip-list* (vector 'head 'head #f) 0 0 cmp
                       key-contract value-contract)])))

(define (make-adjustable-skip-list #:key-contract [key-contract any/c]
                                   #:value-contract [value-contract any/c])
  (cond [(and (eq? key-contract any/c) (eq? value-contract any/c))
         (adjustable-skip-list (vector 'head 'head #f) 0 0 #f)]
        [else
         (adjustable-skip-list* (vector 'head 'head #f) 0 0 #f
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

#|
(module+ no-contracts
  (provide make-skip-list
           make-adjustable-skip-list
           skip-list?
           adjustable-skip-list?
           skip-list-ref
           skip-list-set!
           skip-list-remove!
           skip-list-count
           skip-list-remove-range!
           skip-list-contract!
           skip-list-expand!
           skip-list-iterate-first
           skip-list-iterate-next
           skip-list-iterate-key
           skip-list-iterate-value
           skip-list-iterate-greatest/<=?
           skip-list-iterate-greatest/<?
           skip-list-iterate-least/>=?
           skip-list-iterate-least/>?
           skip-list-iterate-least
           skip-list-iterate-greatest
           skip-list-iter?
           skip-list-iter-valid?
           skip-list->list))
|#

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
 [skip-list-iter-valid?
  (-> skip-list-iter? boolean?)]

 [skip-list->list
  (-> skip-list? list?)])
