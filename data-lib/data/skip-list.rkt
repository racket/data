#lang racket/base
(require racket/match
         racket/contract/base
         racket/dict
         racket/generic
         "order.rkt")
;; owned by ryanc

#|
reference
  Skip Lists: A Probabilistic Alternative to Balanced Trees
  by William Pugh

I take the "fix the dice" approach to avoiding level jumps.
Levels are indexed starting at 1, as in the paper.
|#

#|
(require (rename-in racket/unsafe/ops
                    [unsafe-vector-length vector-length]
                    [unsafe-vector-ref vector-ref]
                    [unsafe-vector-set! vector-set!]))
|#

(define PROBABILITY-FACTOR 4)
(define MAX-LEVEL 16)

(define DATA-SLOTS 2)

;; An Item is (vector Key/Adj data Item/#f Item/#f ...)

;; The Level of an Item is the number of next links it has (at least 1).
;; The head is an Item with key and data #f (never examined)
;; The end of the list is represented by #f

;; A Key/Adj is one of
;;  - Key
;;  - (adjust-key Key Delta)
;; If item I has key (adjust-key Key Delta), it indicates a lazily-propagated
;; key adjustment.  The key value is (+ Key Delta), and the adjustment should be
;; propagated to the successors of I with level less than or equal to level(I),
;; but not to any item with greater level.

(define (item? x) (vector? x))
(define (item-level item)
  (- (vector-length item) DATA-SLOTS))

(define (item-raw-key item)
  (vector-ref item 0))
(define (item-data item)
  (vector-ref item 1))
(define (item-next item level)
  (vector-ref item (+ level DATA-SLOTS -1)))

(define (set-item-key! item key)
  (vector-set! item 0 key))
(define (set-item-data! item data)
  (vector-set! item 1 data))
(define (set-item-next! item level next)
  (vector-set! item (+ level DATA-SLOTS -1) next))

(define (resize-item item level)
  (define new-size (+ DATA-SLOTS level))
  (define new-item (make-vector new-size #f))
  (vector-copy! new-item 0 item 0 (min (vector-length item) new-size))
  new-item)

;; ----

(struct adjust-key (base delta) #:mutable #:transparent)

;; item-key : Item -> Key
(define (item-key item)
  (let ([raw-key (item-raw-key item)])
    (cond [(adjust-key? raw-key)
           (let* ([base-key (adjust-key-base raw-key)]
                  [delta (adjust-key-delta raw-key)]
                  [key (+ base-key delta)])
             (unless (zero? delta)
               ;; Leave adjust-key struct in place
               (set-adjust-key-base! raw-key key)
               (set-adjust-key-delta! raw-key 0)
               ;; Propagate to nexts of lesser or equal level
               (let ([level (item-level item)])
                 (for ([k (in-range 1 level)])
                   (let ([next (item-next item k)])
                     ;; Don't adjust same item again if next at multiple levels
                     (when (and next (= (item-level next) level))
                       (adjust-item-key! item delta))))))
             key)]
          [else raw-key])))

;; adjust-item-key! : Item Delta -> void
(define (adjust-item-key! item delta)
  (let ([raw-key (item-raw-key item)])
    (cond [(adjust-key? raw-key)
           (set-adjust-key-delta! raw-key
                                  (+ (adjust-key-delta raw-key)
                                     delta))]
          [else
           (set-item-key! item (adjust-key raw-key delta))])))

;; ----

;; search : Item Level Key Cmp Cmp -> Item/#f
;; Returns item(R) s.t. key(R) =? key
(define (search head level key =? <?)
  (let* ([closest (closest head level key <?)]
         [item (item-next closest 1)])
    (and (item? item)
         (=? key (item-key item))
         item)))

;; closest : Item Level Key Cmp Cmp -> Item
;; Returns greatest item R s.t. key(R) <? key.
;; Pre: level(item) >= level, key(item) <? key OR item = head
(define (closest item level key <?)
  (if (zero? level)
      item
      (closest (advance item level key <?) (sub1 level) key <?)))

;; advance : Item Level Key Cmp -> Item
;; Returns greatest item R s.t. key(R) <? key and level(R) >= level.
;; Pre: level(item) >= level, key(item) <? key OR item = head
(define (advance item level key <?)
  (let ([next (item-next item level)])
    (if (and next (<? (item-key next) key))
        (advance next level key <?)
        item)))

;; pick-random-level : Nat -> Nat
;; Returns number in [1, max] (with exp. prob. dist.)
(define (pick-random-level max)
  (let loop ([level 1])
    (if (and (< level max) (zero? (random PROBABILITY-FACTOR)))
        (loop (add1 level))
        level)))

;; insert-link! : Item Level Item -> void
(define (insert-link! item level target)
  (let ([old (item-next item level)])
    (set-item-next! item level target)
    (set-item-next! target level old)))

;; delete-link! : Item Level boolean -> void
;; Does not delete next link of deleted item.
(define (delete-link! item level)
  (let* ([old (item-next item level)]
         [after-old (and old (item-next item level))])
    (set-item-next! item level after-old)))

;; update/insert : ... -> Item/#f
;; Updates skip-list so that key |-> data
;; Returns #f to indicate update (existing item changed);
;; returns item to indicate insertion (context's links need updating)
;; Pre: level(item) >= level, key(item) <? key OR item = head
(define (update/insert item level key data =? <? max-level)
  (cond [(positive? level)
         (let* ([item (advance item level key <?)]
                [result (update/insert item (sub1 level)
                                       key data =? <? max-level)])
           (when (and result (>= (item-level result) level))
             (insert-link! item level result))
           result)]
        [else
         (let ([next (item-next item 1)])
           (cond [(and next (=? (item-key next) key))
                  ;; Update!
                  (set-item-data! next data)
                  #f]
                 [else
                  ;; Insert!
                  (let ([new-item
                         (make-vector (+ DATA-SLOTS (pick-random-level max-level)) #f)])
                    (set-item-key! new-item key)
                    (set-item-data! new-item data)
                    ;; next fields will be set by pending recursive calls
                    new-item)]))]))

;; delete : ... -> Item/#f
;; Returns item to indicate deletion (context's links need updating);
;; returns #f if not found.
;; Pre: level(item) >= level; key(item) <? key OR item = head
(define (delete item level key =? <?)
  (cond [(positive? level)
         (let* ([item (advance item level key <?)]
                [result (delete item (sub1 level) key =? <?)])
           (when (and result (eq? (item-next item level) result))
             (delete-link! item level))
           result)]
        [else
         (let ([next (item-next item 1)])
           (cond [(and next (=? (item-key next) key))
                  ;; Delete!
                  next]
                 [else
                  ;; Not found!
                  #f]))]))

;; delete-range : ... -> Item/#f
;; Returns first deleted item, or #f if none.
;; Pre: level(*-item) >= level; key(*-item) <? *-key OR *-item = head
(define (delete-range from-item to-item level from-key to-key <? contract!?)
  (let loop ([from-item from-item] [to-item to-item] [level level])
    (cond [(positive? level)
           (let* ([from-item (advance from-item level from-key <?)]
                  [to-item (advance to-item level to-key <?)]
                  ;; to-item greatest s.t. key(to-item) <? to-key (at level)
                  [to-item* (item-next to-item level)]) ;; key(to-item*) >=? to-key
             (set-item-next! from-item level to-item*)
             (unless (eq? to-item from-item)
               ;; to-item is actually within range
               ;; test like (<? (item-key to-item) from-key), but (item-key head) is undef
               (set-item-next! to-item level #f))
             (when (and contract!? to-item*)
               ;; Don't adjust same item again if next at multiple levels
               (when (= (item-level to-item*) level)
                 (adjust-item-key! to-item* (- from-key to-key))))
             (loop from-item to-item (sub1 level)))]
          [else
           ;; from-item is greatest item s.t. key(item) <? from-key
           ;; so from-item is greatest item s.t. key(item) <? to-key,
           ;; because deleted [from-key, to-key)
           (let ([next (item-next from-item 1)])
             (and next
                  (<? (item-key next) to-key)
                  next))])))

;; expand/right-gravity! : Item Level Key Delta -> void
;; An item with key = from-key will be adjusted up.
(define (expand/right-gravity! item level from-key delta)
  (let loop ([item item] [level level])
    (cond [(positive? level)
           (let* ([item (advance item level from-key <)]
                  [next (item-next item level)])
             (when next
               ;; Don't adjust same item again if next at multiple levels
               (when (= (item-level next) level)
                 (adjust-item-key! next delta)))
             (loop item (sub1 level)))]
          [else
           (void)])))

;; expand/left-gravity! : Item Level Key Delta -> void
;; An item with key = from-key will not be adjusted.
(define (expand/left-gravity! item level from-key delta)
  (expand/right-gravity! item level (add1 from-key) delta))


;; Skip list

(define (skip-list-ref s key [default (skip-list-error key)])
  (define head (skip-list-head s))
  (define result
    (search head (item-level head) key (skip-list-=? s) (skip-list-<? s)))
  (cond [result (item-data result)]
        [(procedure? default) (default)]
        [else default]))

(define ((skip-list-error x))
  (error 'skip-list-ref "no mapping found for: ~e" x))

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
    (raise-type-error who "skip-list-iter" iter))
  (unless (eq? (skip-list-iter-s iter) s)
    (raise-mismatch-error who "skip-list-iter does not match skip-list" iter)))

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
