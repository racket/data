#lang racket/base
(provide (all-defined-out))
;; owned by ryanc

;; Internal representation for data/skip-list.

#|
reference
  Skip Lists: A Probabilistic Alternative to Balanced Trees
  by William Pugh
|#

;; A skip-list's internal state is represented as an Item called head
;; with key and data set to 'head (and never examined).

(define PROBABILITY-FACTOR 4)
(define MAX-LEVEL 20)

(define DATA-SLOTS 2)

;; An Item is (vector Key/Adj/Del data Item/#f Item/#f ...)

;; The Level of an Item is the number of next links it has (at least 1).
;; Note: levels are counted from 1.
;; The end of the list is represented by #f.

;; A Key/Adj/Del is one of
;;  - Key
;;  - (adjust-key Key Delta)
;;  - deleted-marker
;; If item I has key (adjust-key Key Delta), it indicates a lazily-propagated
;; key adjustment.  The key value is (+ Key Delta), and the adjustment should be
;; propagated to the successors of I with level less than or equal to level(I),
;; but not to any item with greater level.
;; If the key is deleted-marker, then the item has been deleted (see
;; below).  A deleted item is never reachable from the head of a
;; skip-list, but may be reachable from an iterator.

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
                 (for ([k (in-range level 0 -1)])
                   (let ([next (item-next item k)])
                     ;; Don't adjust same item again if next at multiple levels
                     (when (and next (= (item-level next) k))
                       (adjust-item-key! next delta))))))
             key)]
          [(eq? raw-key deleted-marker)
           (error 'item-key "internal-error: item is deleted: ~e" item)]
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

;; Comparator is either #f or (any any -> (U '< '= '>))
;; where #f represents standard numeric order (<, =)

(define (compare cmp a b)
  (cond [cmp     (cmp a b)]
        [(< a b) '<]
        [(= a b) '=]
        [else    '>]))

(define (=? cmp a b)
  (cond [cmp  (eq? (cmp a b) '=)]
        [else (= a b)]))

(define (<? cmp a b)
  (cond [cmp  (eq? (cmp a b) '<)]
        [else (< a b)]))

;; ----

;; search : Item Level Key Cmp -> Item/#f
;; Returns item(R) s.t. key(R) =? key
(define (search head level key cmp)
  (let* ([closest (closest head level key cmp)]
         [item (item-next closest 1)])
    (and (item? item)
         (=? cmp key (item-key item))
         item)))

;; closest : Item Level Key Cmp Cmp -> Item
;; Returns greatest item R s.t. key(R) <? key.
;; Pre: level(item) >= level, key(item) <? key OR item = head
(define (closest item level key cmp)
  (if (zero? level)
      item
      (closest (advance item level key cmp) (sub1 level) key cmp)))

;; advance : Item Level Key Cmp -> Item
;; Returns greatest item R s.t. key(R) <? key and level(R) >= level.
;; Pre: level(item) >= level, key(item) <? key OR item = head
(define (advance item level key cmp)
  (let ([next (item-next item level)])
    (if (and next (<? cmp (item-key next) key))
        (advance next level key cmp)
        item)))

;; pick-random-level : Nat -> Nat
;; Returns number in [1, max] (with exp. prob. dist.)
;; Note: I take the "fix the dice" approach to avoiding level jumps.
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
(define (delete-link! item level)
  (let* ([old (item-next item level)]
         [after-old (and old (item-next old level))])
    (set-item-next! item level after-old)
    (set-item-next! old level #f)))

;; update/insert : ... -> Item/#f
;; Updates skip-list so that key |-> data
;; Returns #f to indicate update (existing item changed);
;; returns item to indicate insertion (context's links need updating)
;; Pre: level(item) >= level, key(item) <? key OR item = head
(define (update/insert item level key data cmp max-level)
  (cond [(positive? level)
         (let* ([item (advance item level key cmp)]
                [result (update/insert item (sub1 level)
                                       key data cmp max-level)])
           (when (and result (>= (item-level result) level))
             (insert-link! item level result))
           result)]
        [else
         (let ([next (item-next item 1)])
           (cond [(and next (=? cmp (item-key next) key))
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

;; delete! : ... -> Item/#f
;; Returns deleted item or #f if none deleted. Deleted item is shredded.
;; Pre: level(item) >= level; key(item) <? key OR item = head.
(define (delete! item level key cmp)
  (let-values ([(deleted follower) (delete*! item level key cmp)])
    (shred! deleted follower MAX-LEVEL)
    deleted))

;; delete*! : ... -> (values Item/#f Item/#f)
;; Returns deleted item and (old) successor.
;; Pre: level(item) >= level; key(item) <? key OR item = head
(define (delete*! item level key cmp)
  ;; Returns item to indicate deletion (context's links need updating);
  ;; returns #f if not found.
  (let loop ([item item] [level level])
    (cond [(positive? level)
           (let ([item (advance item level key cmp)])
             (let-values ([(deleted follower) (loop item (sub1 level))])
               (when (and deleted (eq? (item-next item level) deleted))
                 (delete-link! item level))
               (values deleted follower)))]
          [else
           (let ([next (item-next item 1)])
             (cond [(and next (=? cmp (item-key next) key))
                    ;; Delete!
                    (values next (item-next next 1))]
                   [else
                    ;; Not found!
                    (values #f #f)]))])))

;; FIXME/NOTE: Two ways to implement delete-range!, with performance tradeoff:
;;  - fast (log N), but iter to deleted item may pin up to entire deleted range
;;    of items (including keys & values), preventing GC
;;  - slow (N), but iter to deleted item only pins that item
;; Easy to offer both or hybrid (eg, slow is shred! using max-link-level=1; see
;; shred! comments), but harder to pick automatically.  With short-lived
;; iterators, or iterators not used after deletion, fast is better.  For marker
;; (ala Emacs) impl, markers are long-lived iters, but still hard to pick
;; between fast delete and low memory usage.

;; delete-range! : ... -> Item/#f
;; Returns first deleted item, or #f if none deleted. Deleted chain is shredded.
(define (delete-range! from-item to-item level from-key to-key cmp contract!?)
  (define-values (deleted follower)
    (delete-range*! from-item to-item level from-key to-key cmp contract!?))
  (shred! deleted follower MAX-LEVEL)
  deleted)

;; delete-range*! : ... -> (values Item/#f Item/#f)
;; Returns first deleted item, or #f if none.
;; Deleted item chain is internally connected, but disconnected from old surroundings.
;; Pre: level > 0; level(*-item) >= level; key(*-item) <? *-key OR *-item = head
(define (delete-range*! from-item to-item level from-key to-key cmp contract!?)
  (let loop ([from-item from-item] [to-item to-item] [level level])
    (let* ([from-item (advance from-item level from-key cmp)]
           [old-from-next (item-next from-item level)]
           [to-item (advance to-item level to-key cmp)]
           ;; to-item greatest s.t. key(to-item) < to-key (at level)
           [to-item* (item-next to-item level)]) ;; key(to-item*) >= to-key
      (set-item-next! from-item level to-item*)
      (unless (eq? to-item from-item)
        ;; to-item is actually within range
        ;; test like (< (item-key to-item) from-key), but (item-key head) is undef
        (set-item-next! to-item level #f))
      (begin0 (cond [(= level 1)
                     (if (and old-from-next
                              (<? cmp (item-key old-from-next) to-key))
                         (values old-from-next to-item*)
                         (values #f #f))]
                    [else (loop from-item to-item (sub1 level))])
        ;; Adjust keys after recursion
        (when (and contract!? to-item*)
          ;; Don't adjust same item again if next at multiple levels
          (when (= (item-level to-item*) level)
            (adjust-item-key! to-item* (- from-key to-key))))))))

;; ----

;; expand/right-gravity! : Item Level Key Delta -> void
;; An item with key = from-key will be adjusted up.
(define (expand/right-gravity! item level from-key delta)
  (let loop ([item item] [level level])
    (cond [(positive? level)
           (let* ([item (advance item level from-key #f)]
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

;;----------------------------------------

;; Deleted items and repairing iterators

;; A deleted item belongs to a chain whose final item's key is deleted-marker.
(define deleted-marker (gensym 'deleted))

;; shred! : Item/#f Item/#f Level -> void
;; Partly disconnect the chain starting at start into smaller chains and mark
;; the final item in each subchain as deleted, and connect to follower via data
;; field.
(define (shred! start follower max-link-level)
  ;; Since there might be references to deleted items (eg, by iterators), want
  ;; to reduce chain length to minimize amount of memory kept from GC. But
  ;; chopping up into length-1 chains would require time proportional to length
  ;; of deleted chain. So instead, traverse along max-link-level links; goes up
  ;; and then down again, so if max-link-level is MAX-LEVEL should take time ~
  ;; PROB-FACTOR * log(N), so O(log N). (??)  But only cuts longest chain by
  ;; about factor of PROB-FACTOR.  Can use lower max-link-level to take longer,
  ;; get smaller subchains; max-link-leve=1 is O(N), subchain of size 1.

  ;; visit : Item -> void
  (define (visit start)
    (when start
      (let ([next (for/or ([k (in-range (min max-link-level (item-level start)) 0 -1)])
                    (item-next start k))])
        (shred-item! start)
        (visit next))))

  ;; shred-item : Item -> void
  ;; Set key to deleted-marker, set data to follower, next_k to #f.
  (define (shred-item! item)
    (unless (eq? (item-raw-key item) deleted-marker)
      (set-item-key! item deleted-marker)
      (set-item-data! item follower)
      (for ([k (in-range (item-level item) 0 -1)])
        (set-item-next! item k #f))))

  (visit start))

;; repair : Item Level Item -> (values Item/#f (or/c 'valid 'deleted 'failed))
;; Finds sought item *without* using key, forcing keys on the path.
;; The point of this function is to update sought's key when there might be
;; lazily-propagated adjustments in the context that haven't reached it yet, or
;; to discover if sought was deleted.
;; Pre: level(start) >= level
(define (repair start level sought)
  ;; We chase two sequences: approx_k and follower_k.
  ;;
  ;; Assuming sought is reachable from start:
  ;;
  ;;  - follower_k is the leftmost item with level >= k that is to the right of
  ;;    or the same as sought. (Ideally, key(follower_k) >= key(sought), but we
  ;;    want to compute this without trusting keys; see earlier comment.)
  ;;    Must not follow link from item with deleted-marker as key.
  ;;
  ;;  - approx_k is the rightmost item with level >= k that is strictly to the
  ;;    left of sought---because it is the k-predecessor of follower_k, and
  ;;    follower_k is the leftmost item that is right-of-or-same-as sought.  As
  ;;    a side effect, all key adjustments that affect approx_k are forced in
  ;;    the process of computing it.
  ;;
  ;; The goal is approx_1; if approx_1.next_1 = sought, then sought was in the
  ;; same skip-list as start, and any adjustments have been applied to sought's
  ;; key (it still needs to be forced, though). Otherwise, sought is not
  ;; reachable from start; probably because it was removed from the skip-list.
  ;;
  ;; If sought is not reachable from start, then find terminal item w/
  ;; deleted-marker as key, get successor, call repair on that but adjust return
  ;; value to 'deleted.
  ;;
  ;; We compute the two sequences without additional (explicit) storage using a
  ;; "There and Back Again" traversal: we compute follower_k on the way there
  ;; (as k increases), and approx_k on the way back (as k decreases).
  (define (next-follower/approx follower flevel)
    ;; Pre: (item-level follower) >= flevel
    ;; Treat #f as infinitely tall item; ie, level(#f) = inf
    (cond [(= flevel level)
           ;; Return predecessor of follower at level flevel
           (advance-to-predecessor start flevel follower)]
          [else
           (let* ([next-flevel (add1 flevel)]
                  [next-follower
                   (let loop ([next follower])
                     (if (or (eq? next #f)
                             (>= (item-level next) next-flevel))
                         next
                         (loop (item-next next flevel))))])
             (let ([approx (next-follower/approx next-follower next-flevel)])
               (advance-to-predecessor approx flevel follower)))]))

  ;; (check-head start "repair")

  (let ([predecessor (next-follower/approx sought 1)])
    (cond [(and predecessor (eq? (item-next predecessor 1) sought))
           (values sought 'valid)]
          [(get-deleted-marker-item sought)
           => (lambda (deleted)
                ;; FIXME: shred! again if found?
                (cond [(item-data deleted)
                       => (lambda (old-next)
                            (define-values (item status)
                              (repair start level old-next))
                            (case status
                              ((failed)
                               (error 'repair
                                      "internal error: successor of deleted item not found"))
                              ((valid deleted) (values item 'deleted))))]
                      [else
                       (values #f 'deleted)]))]
          [else (values #f 'failed)])))

;; advance-to-predecessor : Item/#f Level Item/#f -> Item/#f
;; Compute S, level-successor to item, st S.next_level = limit.  If no such S,
;; then return #f.  As a side effect: force all keys on path from start to S
;; (see comment on find-item above).
(define (advance-to-predecessor start level limit)
  (let loop ([item start])
    (and item
         (begin
           (item-key item)
           (let ([next (item-next item level)])
             (if (eq? next limit)
                 item
                 (loop next)))))))

;; get-deleted-marker-item : Item -> Item/#f
;; Get item reachable from start whose key is deleted-marker.
(define (get-deleted-marker-item start)
  (let loop ([start start])
    (cond [(eq? start #f) #f]
          [(eq? (item-raw-key start) deleted-marker)
           start]
          [else
           (let ([next (for/or ([k (in-range (item-level start) 0 -1)])
                         (item-next start k))])
             (loop next))])))

;; ----------------------------------------

(module* debug #f
  (require racket/format
           racket/string)
  (provide (all-defined-out))

  (define (check-head head msg [ht #f] [before #f])
    (with-handlers ([exn:fail?
                     (lambda (e)
                       (eprintf "\nerror, printing visualization\n")
                       (eprintf "msg = ~s\n" msg)
                       (when before
                         (eprintf "before:\n~a" before)
                         (eprintf "\nafter:\n"))
                       (visualize-items head ht)
                       (raise e))])
      (void (check-item head (item-level head)))))

  ;; check and return leftmost successor of level > given level
  (define (check-item start level)
    (cond [(zero? level)
           (let ([next (item-next start 1)])
             next)]
          [else
           (let* ([next (item-next start level)]
                  [next* (check-item start (sub1 level))])
             (unless (eq? next next*)
               (error "discrepancy at level ~s" level))
             (cond [(and next (= (item-level next) level))
                    (check-item next level)]
                   [else ;; (item-level next) > level
                    next]))]))

  ;; ----------------------------------------

  ;; build-items : (listof (list key value level)) -> Item
  (define (build-items spec)
    (define head (vector 'head 'head #f))
    (for ([entry (in-list (reverse spec))])
      (let* ([key (car entry)]
             [value (cadr entry)]
             [level (caddr entry)]
             [item (make-vector (+ 2 level) #f)])
        (when (> level (item-level head))
          (set! head (resize-item head level)))
        (vector-set! item 0 key)
        (vector-set! item 1 value)
        (for ([k (in-range level 0 -1)])
          (insert-link! head k item))))
    head)

  (define (visualize-items head [ht (make-hasheq)])
    (define init-length (hash-count ht))

    (let loop ([item head])
      (when (and item (not (hash-ref ht item #f)))
        (hash-set! ht item (hash-count ht))
        (loop (item-next item 1))))

    (let ([visited (make-hasheq)])
      (let loop ([item head])
        (when (and item (not (hash-ref visited item #f)))
          (hash-set! visited item #t)
          (unless (hash-ref ht item #f)
            (hash-set! ht item (hash-count ht)))
          (for ([k (in-range (item-level item) 0 -1)])
            (loop (item-next item k))))))

    (define raw-keys (make-hasheq))

    #|
    (for ([i (in-range (hash-count ht))])
      (let ([raw-key (item-raw-key item)])
        (hash-set! raw-keys item
                   (if (adjust-key? raw-key)
                       (list (adjust-key-base raw-key) (adjust-key-delta raw-key))
                       raw-key))))
    |#

    (define (print-item item)
      (printf (~a (~a #:width 3 #:align 'right "#" (hash-ref ht item))
                  " = ["
                  (if #f
                      (~.v #:width 15 #:align 'right (hash-ref raw-keys item '???))
                      "")
                  " "
                  (~.v #:width 5 #:align 'right
                       (with-handlers ([exn:fail? (lambda (e) 'DEL)])
                         (item-key item)))
                  " "
                  (~.v #:width 10 #:align 'right (item-data item))
                  " "
                  (string-join
                   (for/list ([level (in-range 1 (add1 (item-level item)))])
                     (let* ([next (item-next item level)]
                            [next-label (hash-ref ht next #f)])
                       (cond [next-label
                              (~a #:width 3 #:align 'right "#" next-label)]
                             [next
                              (~a #:width 3 #:align 'right "k="
                                  (with-handlers ([exn:fail? (lambda (e) 'DEL)])
                                    (item-key next)))]
                             [else (~a #:width 3 #:align 'right '--)])))
                   " ")
                  "]\n")))

    (let ([index+item-list
           (sort (for/list ([(k v) (in-hash ht)]) (cons v k))
                 < #:key car)])
      (for ([index+item index+item-list])
        (when (= (car index+item) init-length) (newline))
        (print-item (cdr index+item))))

    ht)

  (define head1
    (build-items
     '((1 one 1)
       (2 two 3)
       (3 three 1)
       (4 four 1)
       (5 five 2)
       (6 six 1)
       (7 seven 2)
       (8 eight 1))))

  (define item2 (search head1 (item-level head1) 2 #f))
  (define item4 (search head1 (item-level head1) 4 #f))

  ;; (delete-range head1 head1 3 3 6 < #t)
  ;; (visualize head1)
  )
