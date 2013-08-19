#lang racket/base
(require (for-syntax racket/base
                     racket/syntax)
         racket/match
         racket/dict
         racket/contract/base
	 racket/generic
         "order.rkt")

(define not-given (gensym 'not-given))

(struct splay-tree-iter (key))

(define (intcmp x y)
  (cond [(= x y) '=] [(< x y) '<] [else '>]))

;; ============================================================
;; Node splay tree
;; ============================================================

(struct node (key value left right) #:mutable #:transparent)

#|
Bottom-up, zero-allocation splay

The following notes sketch the derivation from the naive bottom-up
splay algorithm.

====

SplayPath = null | (cons (Side,Node) SplayPath)
In a SplayPath [...,(s1,n1),(s2,n2),...], then n1 = n2.s2.

find : ... -> (Node, SplayPath)
If find returns (s,x,[(s1,n1),...]), then x = n1.s1.

splay : (Node, SplayPath) -> Node
splayloop : (Node, SplayPath) -> (Node, SplayPath)

====

We always splay after find, so let's have find immediately call
isplay (incremental splay) with just the new part of the splay
path. But we can only splay when we have *two* splay path segments to
work with.

SplayPathBuf = Maybe (Side, Node)

find' : ... -> (Node, SplayPathBuf)
find' ... = ... isplay (find' ..., localSide, localNode) ...

isplay : ((Node, SplayPathBuf), Side, Node) -> (Node, SplayPathBuf)

And at the top there needs to be a finish function to handle
zigs (odd-length SplayPaths => non-None final SplayPathBufs).

finish : (Node, SplayPathBuf) -> Node

====

Actually, find returns Maybe Node. But we still want to splay the path
and produce a new root, even if find failed. So if find'' initially
returns None, isplay' takes the last node seen, sets that as the new
root, and continues splaying. We introduce a status result that
indicates whether the new root was actually the node sought (we also
distinguish found vs added.)

Status = Found | Added | Failed

find'' : ... -> (Status, Maybe Node, SplayPathBuf)
isplay : ((Status, Maybe Node, SplayPathBuf), Side, Node) -> (Status, Node, SplayPathBuf)

finish' : (Status, Maybe Node, SplayPathBuf) -> (Status, Maybe Node)

Note that isplay always returns a Node, never None (I'm taking some
type liberties here). Of course, if the initial tree is empty, isplay
is not called.

====

To avoid allocation, we flatten the types above and use multiple value
return.

<SPB> = Node/#f Node/#f
SP = (values Status Node/#f <SPB>)
   = (values Status Node/#f Side/#f Node/#f)
Status = 'found | 'added | #f
Side = 'left | 'right

In (values status nroot pside pnode):
  nroot is the new root (or #f)
  if pside and pnode are both non-#f,
    pnode is next node in splay path, overrides nroot as new root IF nroot = #f
  if pside and pnode are both #f,
    no pending rotation; add it and keep going...

|#

(define-syntax-rule (SPfinish expr adjust?)
  (let-values ([(ok? x p-side p) expr])
    (finish ok? x p-side p adjust?)))

(define-syntax-rule (SPisplay x-expr gp-side gp adjust?)
  (let-values ([(ok? x p-side p) x-expr])
    (isplay! ok? x p-side p gp-side gp adjust?)))

(define (SPunit x) (values 'found x #f #f))
(define (SPunit/add x) (values 'added x #f #f))
(define (SPfail) (values #f #f #f #f))

;; --------

;; find : ... -> (values status node/#f)
;; If ok?, then node returned is one sought.
(define (n:find k x add-v cmp adjust?)
  (SPfinish (findb k x #f #f add-v cmp adjust?) adjust?))

;; findb : ... -> SP
(define (findb k x p-side p add-v cmp adjust?)
  (cond [x
         (case (cmp k (node-key x))
           [(=)
            (SPunit x)]
           [(<)
            (let ([k* (if adjust? (- k (node-key x)) k)])
              (SPisplay (findb k* (node-left x)  'left  x add-v cmp adjust?) 'left x adjust?))]
           [(>)
            (let ([k* (if adjust? (- k (node-key x)) k)])
              (SPisplay (findb k* (node-right x) 'right x add-v cmp adjust?) 'right x adjust?))])]
        [add-v
         (let ([new-node (node k (car add-v) #f #f)])
           ;; FIXME: link unnecessary? will be done in isplay/finish?
           (when p (set-node-side! p p-side new-node))
           (SPunit/add new-node))]
        [else (SPfail)]))

(define (n:find-min x adjust?)
  (define (find-min-loop x)
    (cond [(and x (node-left x))
           (SPisplay (find-min-loop (node-left x)) 'left x adjust?)]
          [x (SPunit x)]
          [else (SPfail)]))
  (SPfinish (find-min-loop x) adjust?))

(define (n:find-max x adjust?)
  (define (find-max-loop x)
    (cond [(and x (node-right x))
           (SPisplay (find-max-loop (node-right x)) 'right x adjust?)]
          [x (SPunit x)]
          [else (SPfail)]))
  (SPfinish (find-max-loop x) adjust?))

;; isplay! : ... -> SP
;; incremental splay
(define (isplay! ok? x p-side p gp-side gp adjust?)
  (cond [(eq? x #f)
         ;; Then p-side = #f, p = #f
         ;; Overwrite new root with gp
         (values ok? gp #f #f)]
        [p-side ;; we have two splay path segments; splay
         (set-node-side! p p-side x)
         (cond [(eq? p-side gp-side)
                ;; zig-zig
                (rotate! p p-side adjust?)
                (set-node-side! gp gp-side x)
                (rotate! gp gp-side adjust?)
                (values ok? x #f #f)]
               [else
                ;; zig-zag
                (rotate! p p-side adjust?)
                (set-node-side! gp gp-side x)
                (rotate! gp gp-side adjust?)
                (values ok? x #f #f)])]
        [else
         (values ok? x gp-side gp)]))

(define (finish ok? x p-side p adjust?)
  (cond [(eq? x #f)
         ;; Then p-side = #f, p = #f
         (values ok? #f)]
        [p-side ;; one splay path segment left; perform zig
         (set-node-side! p p-side x)
         (rotate! p p-side adjust?)
         (values ok? x)]
        [else ;; no splay path segments left
         (values ok? x)]))

(define (set-node-side! n side v)
  (case side
    ((left) (set-node-left! n v))
    ((right) (set-node-right! n v))))

(define (rotate! x side adjust?)
  (case side
    ((left) (right! x adjust?))
    ((right) (left! x adjust?))
    ((#f) (void))))

(define (right! p adjust?)
  (match p
    [(node Kp _ (and x (node Kx _ A B)) C)
     (set-node-left! p B)
     (set-node-right! x p)
     (when adjust?
       (set-node-key! p (- 0 Kx))
       (set-node-key! x (+ Kp Kx))
       (when B
         (set-node-key! B (+ (node-key B) Kx))))]))

(define (left! p adjust?)
  (match p
    [(node Kp _ A (and x (node Kx _ B C)))
     (set-node-right! p B)
     (set-node-left! x p)
     (when adjust?
       (set-node-key! p (- 0 Kx))
       (set-node-key! x (+ Kp Kx))
       (when B
         (set-node-key! B (+ (node-key B) Kx))))]))

;; --------

;; if left is node, new root is max(left)
(define (n:join-left left right adjust?)
  (cond [(and left right)
         (let-values ([(_ok? left*) (n:find-max left adjust?)])
           ;; left* is node, left*.right = #f
           (set-node-right! left* right)
           (when adjust?
             (set-node-key! right (- (node-key right) (node-key left*))))
           left*)]
        [left left]
        [else right]))

;; if right is node, new root is min(right)
(define (n:join-right left right adjust?)
  (cond [(and left right)
         (let-values ([(_ok? right*) (n:find-min right adjust?)])
           ;; right* is node, right*.left = #f
           (set-node-left! right* left)
           (when adjust?
             (set-node-key! left (- (node-key left) (node-key right*))))
           right*)]
        [right right]
        [else left]))

(define (n:split/drop-root root adjust?)
  (let ([left (node-left root)]
        [right (node-right root)])
    (when adjust?
      (when left
        (set-node-key! left (+ (node-key left) (node-key root))))
      (when right
        (set-node-key! right (+ (node-key right) (node-key root)))))
    (values left right)))

(define (n:split/root-to-left root adjust?)
  (let ([right (node-right root)])
    (when adjust?
      (when right
        (set-node-key! right (+ (node-key right) (node-key root)))))
    (set-node-right! root #f)
    (values root right)))

(define (n:split/root-to-right root adjust?)
  (let ([left (node-left root)])
    (when adjust?
      (when left
        (set-node-key! left (+ (node-key left) (node-key root)))))
    (set-node-left! root #f)
    (values left root)))

(define (n:delete-root root adjust?)
  (let-values ([(left right) (n:split/drop-root root adjust?)])
    (n:join-left left right adjust?)))

(define (n:remove-range! root from to contract!? cmp adjust?)
  (let*-values ([(ok? from-node) (n:find from root (list #f) cmp adjust?)]
                [(left-tree right-tree)
                 (if (eq? ok? 'added)
                     (n:split/drop-root from-node adjust?)
                     (n:split/root-to-right from-node adjust?))]
                [(ok? to-node) (n:find to right-tree (list #f) cmp adjust?)]
                [(mid-tree right-tree)
                 (if (eq? ok? 'added)
                     (n:split/drop-root to-node adjust?)
                     (n:split/root-to-right to-node adjust?))])
    (when (and adjust? contract!?)
      (when right-tree
        (set-node-key! right-tree (+ (node-key right-tree) (- from to)))))
    (n:join-left left-tree right-tree adjust?)))

(define (n:expand! root from to cmp)
  (let*-values ([(ok? from-node) (n:find from root (list #f) cmp #t)]
                [(left-tree right-tree)
                 (if (eq? ok? 'added)
                     (n:split/drop-root from-node #t)
                     (n:split/root-to-right from-node #t))])
    (when right-tree
      (set-node-key! right-tree (+ (node-key right-tree) (- to from))))
    (n:join-left left-tree right-tree #t)))

(define (n:find-prev root adjust?)
  ;; PRE: root is node and root.left is node; ie, has-prev?
  (let-values ([(left right) (n:split/root-to-right root adjust?)])
    ;; join-left does max(left)
    (n:join-left left right adjust?)))

(define (n:find-next root adjust?)
  ;; PRE: root is node and root.right is node; ie, has-next?
  (let-values ([(left right) (n:split/root-to-left root adjust?)])
    ;; join-right does min(right)
    (n:join-right left right adjust?)))

(define (n:has-prev? x) (and x (node-left x) #t))
(define (n:has-next? x) (and x (node-right x) #t))

;; ------------------------------------------------------------
;; Splay tree operations
;; ------------------------------------------------------------

(define (splay-tree-ref s x [default not-given])
  (match s
    [(splay-tree root size cmp adjust?)
     (let-values ([(ok? root) (n:find x root #f cmp adjust?)])
       (set-splay-tree-root! s root)
       (if ok?
           (node-value root)
           (cond [(eq? default not-given)
                  (error 'splay-tree-ref "no value found for key: ~e" x)]
                 [(procedure? default)
                  (default)]
                 [else default])))]))

(define (splay-tree-set! s x v)
  (match s
    [(splay-tree root size cmp adjust?)
     (let-values ([(ok? root) (n:find x root (list v) cmp adjust?)])
       (set-splay-tree-root! s root)
       (when (and (eq? ok? 'added) size)
         (set-splay-tree-size! s (add1 size)))
       (unless (eq? (node-value root) v)
         (set-node-value! root v)))]))

(define (splay-tree-remove! s x)
  (match s
    [(splay-tree root size cmp adjust?)
     (let-values ([(ok? root) (n:find x root #f cmp adjust?)])
       (cond [ok? ;; => root is node to remove
              (set-splay-tree-root! s (n:delete-root root adjust?))
              (when size (set-splay-tree-size! s (sub1 size)))]
             [else
              (set-splay-tree-root! s root)]))]))

(define (splay-tree-count s)
  (let ([size (splay-tree-size s)])
    (if size
        size
        (let ([size (let loop ([x (splay-tree-root s)] [n 0])
                      (if x
                          (loop (node-left x) (loop (node-right x) (add1 n)))
                          n))])
          (set-splay-tree-size! s size)
          size))))

(define (splay-tree-remove-range! s from to)
  (match s
    [(splay-tree root size cmp adjust?)
     (when (eq? (cmp from to) '<)
       (set-splay-tree-root! s (n:remove-range! root from to #f cmp adjust?))
       (set-splay-tree-size! s #f))]))

(define (splay-tree-contract! s from to)
  (match s
    [(splay-tree root size cmp adjust?)
     (unless adjust?
       (error 'splay-tree-contract!
              "non-adjustable splay tree"))
     (unless (< from to)
       (error 'splay-tree-contract!
              "bad range: ~s to ~s" from to))
     (set-splay-tree-root! s (n:remove-range! root from to #t cmp adjust?))
     (set-splay-tree-size! s #f)]))

(define (splay-tree-expand! s from to)
  (match s
    [(splay-tree root size cmp adjust?)
     (unless adjust?
       (error 'splay-tree-expand! "non-adjustable splay tree"))
     (unless (< from to)
       (error 'splay-tree-expand!
              "bad range: ~s to ~s" from to))
     (set-splay-tree-root! s (n:expand! root from to cmp))]))

;; ========

#|
Iteration in splay-trees is problematic.
 - any access to the splay-tree disturbs most notions of "position"
   (other dictionaries, eg hashes, are only disturbed by *updates*)
 - parent-relative keys need parent chain to be interpreted

Options
 1) position = parent chain (very likely to get out of sync)
 2) position = key (re-lookup each time)
 3) snapshot as alist (more allocation than necessary, sometimes much more)
 4) position = node (doesn't work with position-relative keys)

(1,4) are no good. (3) is not very iterator-like.

(2) seems to be the best compromise.
|#

(define (splay-tree-iterate-first s)
  (match s
    [(splay-tree root size cmp adjust?)
     (let-values ([(ok? root) (n:find-min root adjust?)])
       (set-splay-tree-root! s root)
       (if ok? (splay-tree-iter (node-key root)) #f))]))

(define (splay-tree-iterate-next s pos)
  (match pos
    [(splay-tree-iter key)
     (splay-tree-iterate-least/>? s key)]))

(define (splay-tree-iterate-key s pos)
  (match pos
    [(splay-tree-iter key) key]))

(define (splay-tree-iterate-value s pos)
  (match pos
    [(splay-tree-iter key) (splay-tree-ref s key #f)]))

;; Order-based search

(define (n:extreme s key cmp-result has-X? find-X)
  (match s
    [(splay-tree root size cmp adjust?)
     (let-values ([(ok? root)
                   (n:extreme* root key cmp-result has-X? find-X cmp adjust?)])
       (set-splay-tree-root! s root)
       (and ok? (splay-tree-iter (node-key root))))]))

(define (n:extreme* root key cmp-result has-X? find-X cmp adjust?)
  (let-values ([(_ok? root) (n:find key root #f cmp adjust?)])
    ;; ok? is true if returned root satisfies search criteria
    (cond [(and root (memq (cmp (node-key root) key) cmp-result))
           (values #t root)]
          [(has-X? root)
           (values #t (find-X root adjust?))]
          [else
           (values #f root)])))

(define (splay-tree-iterate-greatest/<=? s key)
  (n:extreme s key '(< =) n:has-prev? n:find-prev))
(define (splay-tree-iterate-greatest/<? s key)
  (n:extreme s key '(<) n:has-prev? n:find-prev))
(define (splay-tree-iterate-least/>=? s key)
  (n:extreme s key '(> =) n:has-next? n:find-next))
(define (splay-tree-iterate-least/>? s key)
  (n:extreme s key '(>) n:has-next? n:find-next))

(define (splay-tree-iterate-least s)
  (splay-tree-iterate-first s))
(define (splay-tree-iterate-greatest s)
  (match s
    [(splay-tree root size cmp adjust?)
     (let-values ([(ok? root) (n:find-max root adjust?)])
       (set-splay-tree-root! s root)
       (if ok? (splay-tree-iter (node-key root)) #f))]))

;; ========

;; snapshot
(define (splay-tree->list s)
  (match s
    [(splay-tree root size cmp adjust?)
     (let loop ([x root] [onto null] [k* 0])
       (match x
         [(node key value left right)
          (let ([key (+ key k*)])
            (loop left
                  (cons (cons key value)
                        (loop right onto key))
                  key))]
         [#f onto]))]))

;; ------------------------------------------------------------
;; Struct
;; ------------------------------------------------------------

(define n:dict-methods
  (vector-immutable splay-tree-ref
                    splay-tree-set!
                    #f ;; set
                    splay-tree-remove!
                    #f ;; remove
                    splay-tree-count
                    splay-tree-iterate-first
                    splay-tree-iterate-next
                    splay-tree-iterate-key
                    splay-tree-iterate-value))

(struct splay-tree ([root #:mutable] [size #:mutable] cmp adjust?)
        #:property prop:dict/contract
        (list n:dict-methods
              (vector-immutable any/c
                                any/c
                                splay-tree-iter?
                                #f #f #f))
        #:methods gen:ordered-dict
	[(define dict-iterate-least splay-tree-iterate-least)
	 (define dict-iterate-greatest splay-tree-iterate-greatest)
	 (define dict-iterate-least/>? splay-tree-iterate-least/>?)
	 (define dict-iterate-least/>=? splay-tree-iterate-least/>=?)
	 (define dict-iterate-greatest/<? splay-tree-iterate-greatest/<?)
	 (define dict-iterate-greatest/<=? splay-tree-iterate-greatest/<=?)])

(struct adjustable-splay-tree splay-tree ()
        ;; Note: adjust? field must be true
        #:property prop:dict/contract
        (list n:dict-methods
              (vector-immutable exact-integer?
                                any/c
                                splay-tree-iter?
                                #f #f #f))
        #:methods gen:ordered-dict
	[(define dict-iterate-least splay-tree-iterate-least)
	 (define dict-iterate-greatest splay-tree-iterate-greatest)
	 (define dict-iterate-least/>? splay-tree-iterate-least/>?)
	 (define dict-iterate-least/>=? splay-tree-iterate-least/>=?)
	 (define dict-iterate-greatest/<? splay-tree-iterate-greatest/<?)
	 (define dict-iterate-greatest/<=? splay-tree-iterate-greatest/<=?)])

(struct splay-tree* splay-tree (key-c value-c)
        #:property prop:dict/contract
        (list n:dict-methods
              (vector-immutable any/c
                                any/c
                                splay-tree-iter?
                                (lambda (s) (splay-tree*-key-c s))
                                (lambda (s) (splay-tree*-value-c s))
                                #f))
        #:methods gen:ordered-dict
        [(define dict-iterate-least splay-tree-iterate-least)
	 (define dict-iterate-greatest splay-tree-iterate-greatest)
	 (define dict-iterate-least/>? splay-tree-iterate-least/>?)
	 (define dict-iterate-least/>=? splay-tree-iterate-least/>=?)
	 (define dict-iterate-greatest/<? splay-tree-iterate-greatest/<?)
	 (define dict-iterate-greatest/<=? splay-tree-iterate-greatest/<=?)])


;; ============================================================
;; Constructors, predicates
;; ============================================================

(define (make-splay-tree [ord datum-order]
                         #:key-contract [key-contract any/c]
                         #:value-contract [value-contract any/c])
  (let ([cmp (order-comparator ord)]
        [key-contract (and/c* (order-domain-contract ord) key-contract)])
    (cond [(and (eq? key-contract any/c) (eq? value-contract any/c))
           (splay-tree #f 0 cmp #f)]
          [else
           (splay-tree* #f 0 cmp #f key-contract value-contract)])))

(define (make-adjustable-splay-tree #:key-contract [key-contract any/c]
                                    #:value-contract [value-contract any/c])
  (cond [(and (eq? key-contract any/c) (eq? value-contract any/c))
         (adjustable-splay-tree #f 0 intcmp #t)]
        [else
         (splay-tree* #f 0 intcmp #t key-contract value-contract)]))

(define (and/c* x y)
  (cond [(eq? x any/c) y]
        [(eq? y any/c) x]
        [else (and/c x y)]))


;; ============================================================
;; provide/contract
;; ============================================================

(define (key-c s)
  (cond [(splay-tree*? s) (splay-tree*-key-c s)]
        [(splay-tree-adjust? s) exact-integer?]
        [else any/c]))
(define (val-c s)
  (cond [(splay-tree*? s) (splay-tree*-value-c s)]
        [else any/c]))

(provide/contract
 [make-splay-tree
  (->* ()
       (order? #:key-contract contract? #:value-contract contract?)
       splay-tree?)]
 [make-adjustable-splay-tree
  (->* ()
       (#:key-contract contract? #:value-contract contract?)
       splay-tree?)]

 [splay-tree? (-> any/c boolean?)]
 [adjustable-splay-tree? (-> any/c boolean?)]

 [splay-tree-ref
  (->i ([s splay-tree?] [key (s) (key-c s)])
       ([default any/c])
       any)]
 [splay-tree-set!
  (->i ([s splay-tree?] [key (s) (key-c s)] [v (s) (val-c s)]) [_r void?])]
 [splay-tree-remove!
  (->i ([s splay-tree?] [key (s) (key-c s)]) [_r void?])]
 [splay-tree-remove-range!
  (->i ([s splay-tree?] [from (s) (key-c s)] [to (s) (key-c s)]) [_r void?])]
 [splay-tree-count
  (-> splay-tree? exact-nonnegative-integer?)]
 [splay-tree->list
  (->i ([s splay-tree?]) [_r (s) (listof (cons/c (key-c s) (val-c s)))])]

 [splay-tree-contract!
  (->i ([s adjustable-splay-tree?]
        [from (s) (key-c s)] [to (s) (key-c s)])
       [_r void?])]
 [splay-tree-expand!
  (->i ([s adjustable-splay-tree?]
        [from (s) (key-c s)] [to (s) (key-c s)])
       [_r void?])]

 [splay-tree-iterate-first
  (-> splay-tree? (or/c splay-tree-iter? #f))]
 [splay-tree-iterate-next
  (-> splay-tree? splay-tree-iter? (or/c splay-tree-iter? #f))]
 [splay-tree-iterate-key
  (->i ([s splay-tree?] [i splay-tree-iter?]) [_r (s) (key-c s)])]
 [splay-tree-iterate-value
  (->i ([s splay-tree?] [i splay-tree-iter?]) [_r (s) (val-c s)])]

 [splay-tree-iterate-greatest/<=?
  (->i ([s splay-tree?] [k (s) (key-c s)]) [_r (or/c splay-tree-iter? #f)])]
 [splay-tree-iterate-greatest/<?
  (->i ([s splay-tree?] [k (s) (key-c s)]) [_r (or/c splay-tree-iter? #f)])]
 [splay-tree-iterate-least/>=?
  (->i ([s splay-tree?] [k (s) (key-c s)]) [_r (or/c splay-tree-iter? #f)])]
 [splay-tree-iterate-least/>?
  (->i ([s splay-tree?] [k (s) (key-c s)]) [_r (or/c splay-tree-iter? #f)])]

 [splay-tree-iterate-least
  (-> splay-tree? (or/c splay-tree-iter? #f))]
 [splay-tree-iterate-greatest
  (-> splay-tree? (or/c splay-tree-iter? #f))]

 [splay-tree-iter? (-> any/c boolean?)])
