#lang scribble/manual
@(require scribble/eval
          (for-label data/interval-map
                     data/order
                     racket/contract
                     racket/dict
                     racket/base))

@title[#:tag "interval-map"]{Interval Maps}

@(define the-eval (make-base-eval))
@(the-eval '(require data/interval-map))
@(the-eval '(require racket/dict))

@defmodule[data/interval-map]

@author[@author+email["Ryan Culpepper" "ryanc@racket-lang.org"]]

An interval-map is a mutable data structure that maps @emph{half-open}
intervals of exact integers to values. An interval-map is queried at a
discrete point, and the result of the query is the value mapped to the
interval containing the point.

Internally, interval-maps use a skip-list
(@racketmodname[data/skip-list]) of intervals for efficient query and
update, including efficient contraction and expansion of intervals.

Interval-maps implement the dictionary (@racketmodname[racket/dict])
interface to a limited extent. Only @racket[dict-ref] and the
iteration-based methods (@racket[dict-iterate-first],
@racket[dict-map], etc) are supported. For the iteration-based
methods, the mapping's keys are considered the pairs of the start and
end positions of the mapping's (half-open) intervals.

@examples[#:eval the-eval
(define r (make-interval-map))
(interval-map-set! r 1 5 'apple)
(interval-map-set! r 6 10 'pear)
(interval-map-set! r 3 7 'banana)
r
(interval-map-ref r 1 #f)
(interval-map-ref r 3 #f)
(interval-map-ref r 10 #f)
]

Operations on interval-maps are not thread-safe.

@defproc[(make-interval-map [contents
                             (listof (cons/c (cons/c exact-integer? exact-integer?) any/c))
                             null]
                            [#:key-contract key-contract contract? any/c]
                            [#:value-contract value-contract contract? any/c])
         interval-map?]{

Makes a new interval-map initialized with @racket[_contents], which has the form
@racketblock[(list (cons (cons _start _end) _value) ...)]

@examples[#:eval the-eval
(define r (make-interval-map '(((0 . 5) . apple) ((5 . 10) . banana))))
(interval-map-ref r 2)
(interval-map-ref r 5)
]
}

@defproc[(interval-map? [v any/c])
         boolean?]{

Returns @racket[#t] if @racket[v] is an interval-map, @racket[#f]
otherwise.
}

@defproc[(interval-map-ref [interval-map interval-map?]
                           [position exact-integer?]
                           [default any/c (lambda () (error ....))])
         any/c]{

Return the value associated with @racket[position] in
@racket[interval-map]. If no mapping is found, @racket[default] is
applied if it is a procedure, or returned otherwise.
}

@history[#:added "1.1"]
@defproc[(interval-map-ref/bounds [interval-map interval-map?]
                                  [position exact-integer?]
                                  [default any/c (lambda () (error ....))])
         (values (or/c #f exact-integer?)
                 (or/c #f exact-integer?)
                 any/c)]{
Like @racket[interval-map-ref], but also returns the bounds of the interval
associated with @racket[position]. If no mapping is found and @racket[default]
is a procedure, it is applied. If no mapping is found and @racket[default]
is not a procedure,  @racket[#f] is returned for the start and end positions
and @racket[default] is returned as the value.
}

@defproc[(interval-map-set! [interval-map interval-map?]
                            [start exact-integer?]
                            [end exact-integer?]
                            [value any/c])
         void?]{

Updates @racket[interval-map], associating every position in
[@racket[start], @racket[end]) with @racket[value].

Existing interval mappings contained in [@racket[start], @racket[end])
are destroyed, and partly overlapping intervals are truncated. See
@racket[interval-map-update*!] for an updating procedure that
preserves distinctions within [@racket[start], @racket[end]).
}

@defproc[(interval-map-update*! [interval-map interval-map?]
                                [start exact-integer?]
                                [end exact-integer?]
                                [updater (-> any/c any/c)]
                                [default any/c (lambda () (error ....))])
         void?]{

Updates @racket[interval-map], associating every position in
[@racket[start], @racket[end]) with the result of applying
@racket[updater] to the position's previously associated value, or to
the default value produced by @racket[default] if no mapping exists.

Unlike @racket[interval-map-set!], @racket[interval-map-update*!]
preserves existing distinctions within [@racket[start], @racket[end]).
}

@defproc[(interval-map-remove! [interval-map interval-map?]
                               [start (or/c exact-integer? -inf.0)]
                               [end (or/c exact-integer? +inf.0)])
         void?]{

Removes the value associated with every position in [@racket[start],
@racket[end]).
}

@defproc[(interval-map-contract! [interval-map interval-map?]
                                 [start exact-integer?]
                                 [end exact-integer?])
         void?]{

Contracts @racket[interval-map]'s domain by removing all mappings on
the interval [@racket[start], @racket[end]) and decreasing intervals
initally after @racket[end] by @racket[(- end start)].

If @racket[start] is not less than @racket[end], an exception is raised.
}

@defproc[(interval-map-expand! [interval-map interval-map?]
                               [start exact-integer?]
                               [end exact-integer?])
         void?]{

Expands @racket[interval-map]'s domain by introducing a gap
[@racket[start], @racket[end]) and increasing intervals starting at or after
@racket[start] by @racket[(- end start)].

If @racket[start] is not less than @racket[end], an exception is raised.
}

@defproc[(interval-map-cons*! [interval-map interval-map?]
                              [start any/c]
                              [end any/c]
                              [v any/c]
                              [default any/c null])
         void?]{

Same as the following:
@racketblock[
(interval-map-update*! interval-map start end
                       (lambda (old) (cons v old))
                       default)
]
}


@deftogether[[
@defproc[(interval-map-iterate-first [interval-map interval-map?])
         (or/c interval-map-iter? #f)]
@defproc[(interval-map-iterate-next [interval-map interval-map?]
                                    [iter interval-map-iter?])
         (or/c interval-map-iter? #f)]
@defproc[(interval-map-iterate-key [interval-map interval-map?]
                                   [iter interval-map-iter?])
         pair?]
@defproc[(interval-map-iterate-value [interval-map interval-map?]
                                     [iter interval-map-iter?])
         any]]]{

Implementations of @racket[dict-iterate-first],
@racket[dict-iterate-next], @racket[dict-iterate-key], and
@racket[dict-iterate-value], respectively.
}

@deftogether[[
 @defproc[(interval-map-iterate-least [interval-map interval-map?])
          (or/c interval-map-iter? #f)]
 @defproc[(interval-map-iterate-greatest [interval-map interval-map?])
          (or/c interval-map-iter? #f)]]]{

Like @racket[dict-iterate-least] and @racket[dict-iterate-greatest],
respectively, though interval maps do not implement the
@racket[gen:ordered-dict] interface.

@history[#:added "1.2"]}

@deftogether[[
 @defproc[(interval-map-iterate-least/start>? [interval-map interval-map?]
                                              [start exact-integer?])
          (or/c interval-map-iter? #f)]
 @defproc[(interval-map-iterate-least/start>=? [interval-map interval-map?]
                                               [start exact-integer?])
          (or/c interval-map-iter? #f)]
 @defproc[(interval-map-iterate-greatest/start<? [interval-map interval-map?]
                                                 [start exact-integer?])
          (or/c interval-map-iter? #f)]
 @defproc[(interval-map-iterate-greatest/start<=? [interval-map interval-map?]
                                                  [start exact-integer?])
          (or/c interval-map-iter? #f)]
 @defproc[(interval-map-iterate-least/end>? [interval-map interval-map?]
                                            [end exact-integer?])
          (or/c interval-map-iter? #f)]
 @defproc[(interval-map-iterate-least/end>=? [interval-map interval-map?]
                                             [end exact-integer?])
          (or/c interval-map-iter? #f)]
 @defproc[(interval-map-iterate-greatest/end<? [interval-map interval-map?]
                                               [end exact-integer?])
          (or/c interval-map-iter? #f)]
 @defproc[(interval-map-iterate-greatest/end<=? [interval-map interval-map?]
                                                [end exact-integer?])
          (or/c interval-map-iter? #f)]]]{

Like @racket[dict-iterate-least/>?], @racket[dict-iterate-least/>=?],
@racket[dict-iterate-greatest/<?], and @racket[dict-iterate-greatest/<=?],
but each function comes in a @tt{start} and an @tt{end} variant
corresponding to the start or end of each interval, respectively.

Note that interval maps do not implement the @racket[gen:ordered-dict]
interface, as these operations accept individual bounds rather than the
pairs returned by @racket[interval-map-iterate-key]. Therefore, these
operations must be used directly.

@history[#:added "1.2"]}

@defproc[(interval-map-iter? [v any/c])
         boolean?]{

Returns @racket[#t] if @racket[v] represents a position in an
interval-map, @racket[#f] otherwise.
}


@close-eval[the-eval]
