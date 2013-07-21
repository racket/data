#lang racket/base
(provide (all-defined-out))
;; owned by ryanc

;; Internal representation for data/skip-list.

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
