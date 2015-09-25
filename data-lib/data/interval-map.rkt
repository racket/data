#lang racket/base
;; owned by ryanc
(require racket/contract/base
         racket/promise
         racket/dict
         racket/struct
         data/skip-list)

(define not-given (gensym 'not-given))

;; Interval-maps support only half-open exact-integer intervals.

;; An interval-map is (interval-map skip-list)
;; dict maps Start => (cons End-Start Value)
;; Invariant: intervals are disjoint (but the end of one interval
;; can be the same as the start of the next, since half-open).

(define (interval-map-ref im key [default not-given])
  (define (not-found)
    (cond [(eq? default not-given)
           (error 'interval-map-ref "no mapping found\n  key: ~e" key)]
          [(procedure? default) (default)]
          [else default]))
  (let* ([s (interval-map-s im)]
         [istart (skip-list-iterate-greatest/<=? s key)])
    (cond [istart
           (let ([istartkey (skip-list-iterate-key s istart)]
                 [istartvalue (skip-list-iterate-value s istart)])
             (if (< (- key istartkey) (car istartvalue))
                 (cdr istartvalue)
                 (not-found)))]
          [else (not-found)])))

;; (POST x) =
;;   (if (start <= x < end)
;;       (updater (PRE x default))
;;       (PRE x))
(define (interval-map-update*! im start end updater [default not-given])
  (define updated-defaultp
    (delay (updater
            (cond [(eq? default not-given)
                   (error 'interval-map-update*! "no mapping found")]
                  [(procedure? default) (default)]
                  [else default]))))
  (let ([s (interval-map-s im)])
    (check-interval start end 'interval-map-update*!
                    "im" im "start" start "end" end "updater" updater)
    (split! s start)
    (split! s end)
    ;; Interval ix needs updating iff start <= key(ix) < end
    ;; (Also need to insert missing intervals)
    ;; Main loop:
    (let loop ([start start] [ix (skip-list-iterate-least/>=? s start)])
      (let ([ixstart (and ix (skip-list-iterate-key s ix))])
        (cond [(and ix (< ixstart end))
               ;; First do leading gap, [ start, key(ix) )
               (when (< start ixstart)
                 (skip-list-set! s start
                                 (cons (- ixstart start)
                                       (force updated-defaultp))))
               ;; Then interval, [ ixstart, end(ix) )
               (let ([ixvalue (skip-list-iterate-value s ix)])
                 (skip-list-set! s ixstart
                                 (cons (car ixvalue)
                                       (updater (cdr ixvalue))))
                 (loop (+ ixstart (car ixvalue)) (skip-list-iterate-next s ix)))]
              [else
               ;; Do gap, [ start, end )
               (when (< start end)
                 (skip-list-set! s start
                                 (cons (- end start)
                                       (force updated-defaultp))))])))))

(define (interval-map-cons*! im start end obj [default null])
  (check-interval start end 'interval-map-cons*!
                  "im" im "start" start "end" end "obj" obj)
  (interval-map-update*! im start end (lambda (old) (cons obj old)) default))

;; (POST x) = (if (start <= x < end) value (PRE x))
(define (interval-map-set! im start end value)
  (check-interval start end 'interval-map-set!
                  "im" im "start" start "end" end "value" value)
  (interval-map-remove! im start end)
  (interval-map-update*! im start end (lambda (old) value) #f))

(define (interval-map-remove! im start end)
  (let ([s (interval-map-s im)])
    (check-interval start end 'interval-map-remove!
                    "im" im "start" start "end" end)
    (let ([start (norm s start)]
          [end (norm s end)])
      (when (and start end) ;; ie, s not empty
        (split! s start)
        (split! s end)
        (skip-list-remove-range! s start end)))))

(define (interval-map-contract! im from to)
  (check-interval from to 'interval-map-contract!
                  "im" im "from" from "to" to)
  (interval-map-remove! im from to)
  (let* ([s (interval-map-s im)])
    (skip-list-contract! s from to)
    (when #t
      (coalesce! s from))))

(define (interval-map-expand! im from to)
  (check-interval from to 'interval-map-expand!
                  "im" im "from" from "to" to)
  (let* ([s (interval-map-s im)])
    (split! s from)
    (skip-list-expand! s from to)))

(define (norm s pos)
  (cond [(= pos -inf.0)
         (let ([iter (skip-list-iterate-least s)])
           (and iter (skip-list-iterate-key s iter)))]
        [(= pos +inf.0)
         (let ([iter (skip-list-iterate-greatest s)])
           ;; add 1 to *include* max (recall, half-open intervals)
           (and iter (+ 1 (skip-list-iterate-key s iter))))]
        [else pos]))

(define (coalesce! s x)
  ;; Coalesce [a, x) -> v; [x, c) -> v into [a, c) -> v
  (define ia (skip-list-iterate-greatest/<? s x))
  (define ib (and ia (skip-list-iterate-next s ia)))
  (when (and ia ib)
    (define a (skip-list-iterate-key s ia))
    (define b (skip-list-iterate-key s ib))
    (define va (skip-list-iterate-value s ia))
    (define vb (skip-list-iterate-value s ib))
    (when (and (= x (+ a (car va)))
               (= x b)
               (eq? (cdr va) (cdr vb)))
      (skip-list-remove! s x)
      (skip-list-set! s a (cons (+ (car va) (car vb)) (cdr va))))))

;; split! 
;; Ensures that if an interval contains x, it starts at x
(define (split! s x)
  (let* ([ix (skip-list-iterate-greatest/<? s x)]
         [ixstart (and ix (skip-list-iterate-key s ix))])
    ;; (ix = #f) or (key(ix) < x)
    (cond [(eq? ix #f)
           ;; x <= all existing intervals; that is, either
           ;;   1) x starts its own interval (=), or
           ;;   2) x < all existing intervals (<)
           ;; Either way, nothing to split.
           (void)]
          [else
           (let* ([ixvalue (skip-list-iterate-value s ix)]
                  [ixrun (car ixvalue)])
             (cond [(< x (+ ixstart ixrun))
                    ;; Split; adjust ix to end at x, insert [x, ixend)
                    (skip-list-set! s ixstart (cons (- x ixstart) (cdr ixvalue)))
                    (skip-list-set! s x (cons (- (+ ixstart ixrun) x) (cdr ixvalue)))]
                   [else
                    ;; x not in ix
                    (void)]))])))

(define (check-interval start end who . args)
  (unless (< start end)
    (apply
     raise-arguments-error
     who
     (if (member "from" args)
         "from is not strictly less than to"
         "start is not strictly less than end")
     args)))

;; Iteration

(struct interval-map-iter (si))

(define (interval-map-iterate-first im)
  (cond [(skip-list-iterate-first (interval-map-s im))
         => interval-map-iter]
        [else #f]))

(define (interval-map-iterate-next im iter)
  (cond [(skip-list-iterate-next (interval-map-s im)
                                 (interval-map-iter-si iter))
         => interval-map-iter]
        [else #f]))

(define (interval-map-iterate-key im iter)
  (let ([s (interval-map-s im)]
        [is (interval-map-iter-si iter)])
    (let ([key (skip-list-iterate-key s is)])
      (cons key (+ key (car (skip-list-iterate-value s is)))))))

(define (interval-map-iterate-value im iter)
  (let ([s (interval-map-s im)]
        [is (interval-map-iter-si iter)])
    (cdr (skip-list-iterate-value s is))))

;; ============================================================

;; Interval map

(define dict-methods
  (vector-immutable interval-map-ref
                    #f ;; set!
                    #f ;; set
                    #f ;; remove!
                    #f ;; remove
                    (lambda (im) (error 'interval-map-count "not supported"))
                    interval-map-iterate-first
                    interval-map-iterate-next
                    interval-map-iterate-key
                    interval-map-iterate-value))

;; Can't use prop:dict/contract, because we don't really
;; follow the dict interface!

(struct interval-map (s)
        #:property prop:dict dict-methods
        #:property prop:custom-write
        (make-constructor-style-printer
         (lambda (im) 'make-interval-map)
         (lambda (im) (list (dict-map im cons)))))

(struct interval-map* interval-map (key-c value-c)
        #:property prop:dict dict-methods)

(define (make-interval-map #:key-contract [key-contract any/c]
                           #:value-contract [value-contract any/c]
                           [contents null])
  (define im
    (cond [(and (eq? key-contract any/c) (eq? value-contract any/c))
           (interval-map (make-adjustable-skip-list))]
          [else
           (interval-map* (make-adjustable-skip-list) key-contract value-contract)]))
  (for ([entry (in-list contents)])
    (interval-map-set! im (car (car entry)) (cdr (car entry)) (cdr entry)))
  im)

;; ============================================================

(define (key-c im)
  (cond [(interval-map*? im)
         (let ([c (interval-map*-key-c im)])
           (if (eq? c any/c) exact-integer? (and/c exact-integer? c)))]
        [else exact-integer?]))
(define (val-c im)
  (cond [(interval-map*? im)
         (interval-map*-value-c im)]
        [else any/c]))

(provide/contract
 [make-interval-map
  (->* ()
       ((listof (cons/c (cons/c exact-integer? exact-integer?) any/c))
        #:key-contract contract? #:value-contract contract?)
       interval-map?)]
 [interval-map?
  (-> any/c boolean?)]
 [interval-map-ref
  (->i ([im interval-map?] [k (im) (key-c im)]) ([d any/c]) any)]
 [interval-map-set!
  (->i ([im interval-map?]
        [start (im) (key-c im)]
        [end (im) (key-c im)]
        [v (im) (val-c im)])
       [_r void?])]
 [interval-map-update*!
  (->i ([im interval-map?]
        [start (im) (key-c im)]
        [end (im) (key-c im)]
        [f (im) (-> (val-c im) (val-c im))])
       ([default any/c]) ;; imprecise
       [_r void?])]
 [interval-map-cons*!
  (->i ([im interval-map?]
        [start (im) (key-c im)]
        [end (im) (key-c im)]
        [v any/c]) ;; imprecise
       ([d any/c]) ;; imprecise
       [_r void?])]
 [interval-map-remove!
  (->i ([im interval-map?]
        [start (im) (or/c -inf.0 (key-c im))]
        [end (im) (or/c +inf.0 (key-c im))])
       [_r void?])]
 [interval-map-contract!
  (->i ([im interval-map?]
        [start (im) (key-c im)]
        [end (im) (key-c im)])
       [_r void?])]
 [interval-map-expand!
  (->i ([im interval-map?]
        [start (im) (key-c im)]
        [end (im) (key-c im)])
       [_r void?])]

 [interval-map-iterate-first
  (-> interval-map?
      (or/c interval-map-iter? #f))]
 [interval-map-iterate-next
  (-> interval-map? interval-map-iter?
      (or/c interval-map-iter? #f))]
 [interval-map-iterate-key
  (->i ([im interval-map?] [i interval-map-iter?])
       [_r (im) (let ([k (key-c im)]) (cons/c k k))])]
 [interval-map-iterate-value
  (->i ([im interval-map?] [i interval-map-iter?])
       [_r (im) (val-c im)])]

 [interval-map-iter?
  (-> any/c boolean?)])

#|
;; Testing
(define (dump im)
  (dict-map (interval-map-s im) list))

(define im (make-interval-map* = <))
(interval-map-set! im 1 3 '(a))
(interval-map-set! im 4 7 '(b))
(dump im)
;;(interval-map-remove! im 2 5)
(interval-map-cons*! im 2 5 'c null)
(dump im)
|#

#|
(define sim (make-interval-map* string=? string<?))
(interval-map-set! sim "apple" "orange" 'fruit)
(interval-map-set! sim "banana" "guava" 'tropical-fruit)
(dump sim)
|#
