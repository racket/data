#lang scribble/manual
@(require scribble/eval
          data/enumerate/lib
          plot/pict
          (for-label data/enumerate
                     data/enumerate/lib
                     pict
                     pict/tree-layout
                     racket/math
                     racket/set
                     racket/contract
                     racket/match
                     racket/base
                     math/base))

@title{Enumerations}
@defmodule[data/enumerate #:no-declare]
@declare-exporting[data/enumerate data/enumerate/lib]

@(define the-eval (make-base-eval))
@(the-eval '(require data/enumerate data/enumerate/lib
                     racket/set racket/string
                     racket/contract racket/match
                     pict pict/tree-layout))
@(define-syntax-rule (ex e ...) (examples #:eval the-eval e ...))


@author[@author+email["Max S. New" "maxnew@ccs.neu.edu"]]

This library defines @deftech{enumerations}. Enumerations
are represented as bijections between the natural numbers (or a prefix of
them) and the values of some contract. Most of the
enumerations defined in this library guarantee that the
constructed bijection is efficient, in the sense that
decoding a number is roughly linear in the number of bits
taken to represent the number.

The two main options on an enumeration convert natural numbers
back (@racket[from-nat]) and forth (@racket[to-nat]) between
the elements of the contract. The simplest enumeration, 
@racket[natural/e] is just a pair of identity functions:
@interaction[#:eval
             the-eval
             (from-nat natural/e 0)
             (to-nat natural/e 1)]
but the library builds up more complex enumerations from
simple ones. For example, you can enumerate lists of the
elements of other enumerations using @racket[list/e]:
@interaction[#:eval
             the-eval
             (from-nat (list/e natural/e natural/e natural/e) 0)
             (from-nat (list/e natural/e natural/e natural/e) 1)
             (from-nat (list/e natural/e natural/e natural/e) (expt 2 100))
             (to-nat (list/e natural/e natural/e natural/e)
                     (list 123456789 123456789 123456789))]
To interleave two enumerations, use @racket[or/e]:
@interaction[#:eval
             the-eval
             (from-nat (or/e natural/e (list/e natural/e natural/e)) 0)
             (from-nat (or/e natural/e (list/e natural/e natural/e)) 1)
             (from-nat (or/e natural/e (list/e natural/e natural/e)) 2)
             (from-nat (or/e natural/e (list/e natural/e natural/e)) 3)
             (from-nat (or/e natural/e (list/e natural/e natural/e)) 4)]
and to construct recursive data structures, use 
@racket[delay/e] (with a little help from @racket[single/e] to
build a singleton enumeration for the base-case):
@def+int[#:eval 
         the-eval
         (define bt/e
           (delay/e
            (or/e (single/e #f)
                  (list/e bt/e bt/e))))
         (from-nat bt/e 0)
         (from-nat bt/e 1)
         (from-nat bt/e 2)
         (from-nat bt/e 3)
         (from-nat bt/e (expt 2 100))]

The library also supports dependent enumerations. For example, 
to build ordered pairs, we can allow any natural number
in the first component, but we want to have only natural
numbers that are larger than that in the second component. 
The @racket[cons/de] lets us express the dependency (using a notation
similar to the contract @racket[cons/dc]) and then we can
use @racket[nat+/e], which builds a enumerators of natural numbers
that are larger than or equal to its argument:
@def+int[#:eval 
         the-eval
         (define ordered-pair/e
           (cons/de [hd natural/e]
                    [tl (hd) (nat+/e (+ hd 1))]))
         (for/list ([i (in-range 10)])
           (from-nat ordered-pair/e i))]

Sometimes the best way to get a new enumeration is to adjust
the output of a previous one. For example, if we wanted
ordered pairs that were ordered in the other direction, we
just need to swap the components of the pair from the 
@racket[ordered-pair/e] enumeration. The function 
@racket[map/e] adjusts existing enumerations. It accepts a
contract describing the new kinds of values and functions
that convert back and forth between the new and old kinds of
values. 
@defs+int[#:eval 
          the-eval
          ((define (swap-components x) (cons (cdr x) (car x)))
           (define other-ordered-pair/e
             (map/e swap-components
                    swap-components
                    ordered-pair/e
                    #:contract (cons/c exact-nonnegative-integer?
                                       exact-nonnegative-integer?))))
          (for/list ([i (in-range 10)])
            (from-nat other-ordered-pair/e i))]

Some of the combinators in the library are guaranteed to build
enumeration functions that are bijections. But since @racket[map/e]
accepts arbitrary functions and @racket[or/e] accepts enumerations with
arbitrary contracts, they may project enumerations that are not be bijections.
To help avoid errors, the contracts on @racket[map/e] and @racket[or/e] does some
random checking to see if the result would be a bijection. 
Here's an example that, with high probability, signals a contract violation.
@interaction[#:eval
             the-eval
             (map/e (λ (x) (floor (/ x 100)))
                    (λ (x) (* x 100))
                    natural/e
                    #:contract exact-nonnegative-integer?)]
The contract on @racket[or/e] has a similar kind of checking that attempts to
find overlaps between the elements of the enumerations in its arguments.

Sometimes, there is no easy way to make two functions that form a bijection. In 
that case you can use @racket[pam/e] and supply only one function 
to make a @tech{one way enumeration}. For example,
we can make an enumeration of picts of binary trees like this:

@def+int[#:eval
         the-eval
         (define pict-bt/e
           (pam/e
            (λ (bt)
              (binary-tidier
               (let loop ([bt bt])
                 (cond
                   [(list? bt) (apply tree-layout (map loop bt))]
                   [else #f]))))
            bt/e
            #:contract pict?))

         (from-nat pict-bt/e 10)
         (from-nat pict-bt/e 11)
         (from-nat pict-bt/e 12)]


Putting all these pieces together, here is a definition of
an enumeration of closed expressions of the untyped
lambda calculus.

@defs+int[#:eval
          the-eval
          ((define/contract (lc-var/e bvs memo)
             (-> (set/c symbol?) (hash/c (set/c symbol?) enum?) enum?)
             (code:comment "memoization is a significant performance improvement")
             (hash-ref!
              memo
              bvs
              (delay/e
               (or/e
                (code:comment "the variables currently in scope")
                (apply fin/e (set->list bvs))
                
                (code:comment "the λ case; first we build a dependent")
                (code:comment "pair of a bound variable and a body expression")
                (code:comment "and then use map/e to build the usual syntax")
                (map/e
                 (λ (pr) `(λ (,(car pr)) ,(cdr pr)))
                 (λ (λ-exp) (cons (caadr λ-exp) (caddr λ-exp)))
                 (cons/de
                  [hd symbol/e]
                  [tl (hd) (lc-var/e (set-add bvs hd) memo)])
                 #:contract (list/c 'λ (list/c symbol?) lc-exp?))
                
                (code:comment "application expressions")
                (list/e (lc-var/e bvs memo) (lc-var/e bvs memo))))))
           
           (define (lc-exp? x)
             (match x
               [(? symbol?) #t]
               [`(λ (,x) ,e) (and (symbol? x) (lc-exp? e))]
               [`(,a ,b) (and (lc-exp? a) (lc-exp? b))]))
           
           (define lc/e (lc-var/e (set) (make-hash))))
          (from-nat lc/e 0)
          (from-nat lc/e 1)
          (from-nat lc/e 2)
          (to-nat lc/e
                  '(λ (f) 
                     ((λ (x) (f (x x)))
                      (λ (x) (f (x x))))))]


@section{Enumeration Properties}

In addition to the functions that form the bijection, an
enumeration also has a contract, a count, and three boolean
properties associated with it: if it is finite
or not, if it is a bijection to the natural numbers or
merely maps from the natural numbers without going back, and
if the contract it has is a @racket[flat-contract?].

The functions in this section are predicates for the boolean
properties and selection functions for other properties.

When an enumeration prints out, it shows the first few elements
of the enumeration and, if it is either a @tech{finite enumeration}
or a @tech{one way enumeration}, it prints @litchar{finite} 
and @litchar{one-way}, as appropriate. If those prefixes are not
printed, then the enumeration is not finite and is not one-way.


@defproc[(enum? [x any/c]) boolean?]{
  Identifies a value as an @tech{enumeration}.
}

@defproc[(finite-enum? [v any/c]) boolean?]{
  Identifies @deftech{finite enumerations}.
}
@defproc[(infinite-enum? [v any/c]) boolean?]{
  Identifies @deftech{infinite enumerations}, i. e., 
  @tech{enumerations} that map all natural numbers.
}
@defproc[(two-way-enum? [v any/c]) boolean?]{
  Identifies @deftech{two way enumerations}, i. e., @tech{enumerations}
  that can map back and forth from
  values that satisfy the enumeration's contract to the natural
  numbers.
}
@defproc[(one-way-enum? [v any/c]) boolean?]{
   Identifies @deftech{one way enumerations}, i. e., @tech{enumerations}
   that can map only from the natural numbers to values that satisfy the 
   enumeration's contract, but not back.
}
@defproc[(flat-enum? [v any/c]) boolean?]{
  Identifies @deftech{flat enumerations}, i. e., @tech{enumerations}
  whose contracts are @racket[flat-contract?]s.
}

@defproc[(enum-count [e finite-enum?]) exact-nonnegative-integer?]{
  Returns the number of elements of an @tech{enumeration}.
}

@defproc[(enum-contract [e finite-enum?]) exact-nonnegative-integer?]{
  Returns the @racket[contract?] that @racket[e] enumerates.
}

@section{Querying Enumerations}

The functions in this section exercise the enumeration,
turning natural numbers back and forth to the values
that an enumeration enumerates.

@defproc[(from-nat [e enum?] [n (if (finite-enum? e)
                                    (integer-in 0 (enum-count e))
                                    exact-nonnegative-integer?)])
         (enum-contract e)]{
  Decodes @racket[n] from @racket[e].
}

@defproc[(to-nat [e two-way-enum?] [x (enum-contract e)])
         (if (finite-enum? e)
             (integer-in 0 (enum-count e))
             exact-nonnegative-integer?)]{
  Encodes @racket[x] from @racket[e].
}

@defproc[(enum->list [e enum?] 
                     [n (if (finite-enum? e)
                            (integer-in 0 (enum-count e))
                            exact-nonnegative-integer?)
                        (enum-count e)]) 
         (listof (enum-contract e))]{
  Returns a list of the first @racket[n] values in @racket[e].

  If @racket[n] is not supplied, then @racket[e] must be
  a finite-enum.
                              
  @examples[#:eval 
            the-eval
            (enum->list (list/e natural/e natural/e) 8)
            (enum->list (below/e 8))]
}

@defproc[(in-enum [e enum?]) sequence?]{
  Constructs a sequence suitable for use with
  @racket[for] loops.
  
  Note that enumerations are also sequences directly, too.
  
  @examples[#:eval 
            the-eval
            (for/list ([i (in-enum (below/e 5))])
              i)]
}

@section{Constructing Enumerations}

This section contains the fundamental operations for building
enumerations.

@defthing[natural/e (and/c infinite-enum? two-way-enum? flat-enum?)]{

An @tech{enumeration} of the natural numbers.
   
@examples[#:eval the-eval
(from-nat natural/e 5)
(to-nat natural/e 5)
]}

@defproc[(below/e [max (or/c exact-nonnegative-integer? +inf.0)])
         (and/c (if (= max +inf.0)
                    finite-enum?
                    infinite-enum?)
                two-way-enum?
                flat-enum?)]{

An @tech{enumeration} of the first @racket[max] naturals or, if
@racket[max] is @racket[+inf.0], all of the naturals.

@examples[#:eval the-eval
(enum->list (below/e 10))
]}

@defthing[empty/e (and/c finite-enum? two-way-enum? flat-enum?)]{

The empty @tech{enumeration}.

@examples[#:eval the-eval
(enum->list empty/e)
]}


@defproc*[([(map/e [f (-> (enum-contract e) c)]
                   [f-inv (-> c (enum-contract e))]
                   [#:contract c contract?]
                   [e enum?])
            enum?]
           [(map/e [f (dynamic->* #:mandatory-domain-contracts (map enum-contract e)
                                  #:range-contracts (list c))]
                   [f-inv (dynamic->* #:mandatory-domain-contracts (list c)
                                      #:range-contracts (map enum-contract e))]
                   [#:contract c contract?]
                   [e enum?] ...+)
            enum?])]{
 Builds an @tech{enumeration} of @racket[c] from @racket[e] by
 calling @racket[f] on each element of the enumeration
 and @racket[f-inv] of each value of @racket[c]. 
 
 If multiple enumerations are supplied, @racket[f] is expected
 to accept any combination of elements of the given enumerations,
 i. e., the enumerations are not processed in parallel like the
 lists in @racket[map], but instead any element from the first enumeration
 may appear as the first argument to @racket[f] and any element from
 the second may appear as the second argument to @racket[f], etc.
 
 If @racket[e] is a @tech{one way enumeration}, then the result is
 a one way enumeration and @racket[f-inv] is ignored. Otherwise,
 the result is a @tech{two way enumeration}.
 
 @examples[#:eval 
           the-eval
           (define evens/e
             (map/e (λ (x) (* x 2))
                    (λ (x) (/ x 2))
                    natural/e
                    #:contract (and/c exact-nonnegative-integer?
                                      even?)))
           (enum->list evens/e 10)
           (define odds/e
             (map/e add1
                    sub1
                    evens/e
                    #:contract (and/c exact-nonnegative-integer?
                                      odd?)))
           (enum->list odds/e 10)
           (define ordered-pair/e
             (map/e (λ (x y) (cons x (+ x y)))
                    (λ (p)
                      (define x (car p))
                      (define y (cdr p))
                      (values x (- y x)))
                    natural/e
                    natural/e
                    #:contract (and/c (cons/c exact-nonnegative-integer?
                                              exact-nonnegative-integer?)
                                      (λ (xy) (<= (car xy) (cdr xy))))))
           (enum->list ordered-pair/e 10)
           ]
}


@defproc[(pam/e [f (dynamic->* #:mandatory-domain-contracts (map enum-contract e)
                               #:range-contracts (list c))]
                [#:contract c contract?]
                [e enum?] ...+)
         one-way-enum?]{
  Builds a @tech{one way enumeration} from the given enumerations,
  combining their elements with @racket[f], in a manner similar
  to @racket[map/e].

   @examples[#:eval 
             the-eval
             (define rationals/e
               (pam/e /
                      (nat+/e 1)
                      (nat+/e 2)
                      #:contract (and/c exact? rational? positive?)))
           (enum->list rationals/e 10)]
}

@defproc[(except/e [e two-way-enum?]
                   [#:contract c (or/c #f contract?) #f]
                   [x (enum-contract e)] ...) 
         two-way-enum?]{

Returns a @tech{two way enumeration} identical to @racket[e] except that all
@racket[x] are removed from the enumeration.

If @racket[c] is @racket[#f], then it is not treated as a contract, instead
the resulting contract is synthesized from contract on @racket[e]
and the @racket[x]s.

@examples[#:eval the-eval
                 (define except-1/e
                   (except/e natural/e 3))
                 (from-nat except-1/e 2)
                 (from-nat except-1/e 4)
                 (to-nat except-1/e 2)
                 (to-nat except-1/e 4)]}

@defproc[(or/e [#:one-way-enum? one-way-enum? boolean? #f]
               [e-p (or/c enum? (cons/c enum? (-> any/c boolean?)))] ...) 
         enum?]{

An @tech{enumeration} of all of the elements of the enumerations in
the @racket[e-p] arguments. 

If the enumerations have overlapping elements, then pass @racket[#f] as
@racket[one-way-enum?] so the result is a @tech{one way enumeration}.

In more detail, if all of the arguments have or are @tech{two way enumerations} 
and @racket[one-way-enum?] is @racket[#f], then 
the result is also a @tech{two way enumeration} and
each argument must come with a predicate to distinguish its elements 
from the elements of the other enumerations. If the argument is
a pair, then the predicate in the second position of the pair is used.
If the argument is an enumeration, then it must be a @tech{flat enumeration}
and the contract is used as its predicate. 

If any of the arguments are @tech{one way enumerations} (or @racket[one-way-enum?] is
not @racket[#f]), then the result is a @tech{one way enumeration} and any predicates
in the arguments are ignored.

@examples[#:eval the-eval
                 (enum->list (or/e natural/e (list/e natural/e natural/e))
                             10)]
}

@defproc[(append/e [#:one-way-enum? one-way-enum? boolean? #f]
                   [e-p (or/c enum? (cons/c enum? (-> any/c boolean?)))] ...+) 
         enum?]{

An @tech{enumeration} of the elements of the enumerations given in
@racket[e-p] that enumerates the elements in order that the enumerations
are supplied. All but the last enumeration must be finite.

Like @racket[or/e] the resulting enumeration is either a @tech{one way enumeration} or 
a @tech{two way enumeration} depending on the status of the arguments, and 
@racket[append/e] has the same constraints on overlapping elements in the
arguments.

@examples[#:eval the-eval
                 (enum->list 
                  (append/e (take/e natural/e 4)
                            (list/e natural/e natural/e))
                  10)]
}

@defproc[(thunk/e [eth (-> (and/c (if (= count +inf.0)
                                      infinite-enum?
                                      (and/c finite-enum?
                                             (let ([matching-count? (λ (e) (= (enum-count e) count))])
                                               matching-count?)))
                                  (if is-two-way-enum?
                                      two-way-enum?
                                      one-way-enum?)
                                  (if is-flat-enum?
                                      flat-enum?
                                      (not/c flat-enum?))))]
                  [#:count count (or/c +inf.0 exact-nonnegative-integer?) +inf.0]
                  [#:two-way-enum? is-two-way-enum? any/c #t]
                  [#:flat-enum? is-flat-enum? any/c #t])
         enum?]{

A delayed @tech{enumeration} identical to the result of @racket[eth].
          
The @racket[count], @racket[is-two-way-enum?], and @racket[is-flat-enum?]
arguments must be accurate predications of the properties of the result of 
@racket[eth].

The argument @racket[eth] is invoked when the result enumeration's contract
or bijection is used, either directly or indirectly via a call to
@racket[enum-contract], @racket[from-nat], or @racket[to-nat].

@examples[#:eval the-eval
                 (letrec ([bt/e (thunk/e 
                                 (λ ()
                                   (or/e (single/e #f)
                                         (list/e bt/e bt/e))))])
                   (enum->list bt/e 5))]
}

@defproc[(list/e [#:ordering ordering (or/c 'diagonal 'square) 'square] [e enum?] ...) enum?]{

An @tech{enumeration} of lists of values enumerated by the
@racket[e].

If @racket[ordering] is @racket['square], it uses a generalized form
of Szudzik's ``elegant'' ordering and if @racket[ordering] is @racket['diagonal],
it uses a generalized form of Cantor's mapping from pairs of naturals
to naturals.

@examples[#:eval the-eval
                 (enum->list (list/e
                              (fin/e "Brian" "Jenny" "Ki" "Ted") 
                              natural/e
                              (fin/e "Terra" "Locke" "Edgar" "Mash"))
                             5)
                 (enum->list (list/e natural/e natural/e)
                             10)
                 (enum->list (list/e #:ordering  'diagonal natural/e natural/e)
                             10)]
}

@defproc[(dep/e [e enum?] 
                [f (-> (enum-contract e)
                       (and/c (if f-range-finite?
                                  finite-enum?
                                  infinite-enum?)
                              (if one-way?
                                  one-way-enum?
                                  two-way-enum?)
                              (if flat?
                                  flat-enum?
                                  (not/c flat-enum?))))]
                [#:f-range-finite? f-range-finite? boolean? #f]
                [#:flat? flat? boolean? #t]
                [#:one-way? one-way? boolean? (one-way-enum? e)])
         enum?]{
  Constructs an @tech{enumeration} of pairs like the first case of @racket[cons/de].
        
  @examples[#:eval
            the-eval
            (define dep/e-ordered-pair/e
              (dep/e natural/e 
                     (λ (hd) (nat+/e (+ hd 1)))))
            (enum->list dep/e-ordered-pair/e 10)]
}

@defproc[(bounded-list/e [k exact-nonnegative-integer?] [n exact-nonnegative-integer?]) (and/c finite-enum? two-way-enum? flat-enum?)]{

An @tech{enumeration} of tuples of naturals with @racket[max] @racket[n] of length @racket[k].

@examples[#:eval the-eval
(enum->list (bounded-list/e 3 2)
            5)
]}


@section{More Enumeration Operations}
@defmodule[data/enumerate/lib]

The @racket[data/enumerate/lib] extends @racket[data/enumerate] with a bunch of
additional ways to build enumerations, some utility functions, and a bunch of pre-built
enumerations.

@subsection{More Enumeration Constructors}


@defform*[[(cons/de [car-id car-enumeration-expr] 
                    [cdr-id (car-id) cdr-enumeration-expr] 
                    cons/de-option)
           (cons/de [car-id (cdr-id) car-enumeration-expr]
                    [cdr-id cdr-enumeration-expr]
                    cons/de-option)]
          #:grammar ([cons/de-option (code:line)
                                     (code:line #:dep-expression-finite? expr cons/de-option)
                                     (code:line #:flat? expr cons/de-option)
                                     (code:line #:one-way? expr cons/de-option)])]{
  Constructs an @tech{enumeration} of pairs where the first component
                of the pair is drawn from the @racket[car-enumeration-expr]'s
                value and the second is drawn from the @racket[cdr-enumeration-expr]'s
                value.
                
  In the first form, the @racket[cdr-enumeration-expr] can use @racket[car-id], which
  is bound to the value of the car position of the pair, mutatis mutandis in the second case.
  
  If @racket[#:dep-expression-finite?] keyword and expression are present, then the
  value of the dependent expression is expected to be an @tech{infinite enumeration}
  if the expression evaluates to @racket[#f] and a finite enumeration otherwise. If
  the keyword is not present, then the dependent expressions are expected to always
  produce infinite enumerations.
  
  If @racket[#:flat?] is present and evaluates to a true value, then the
  value of both sub-expressions are expected to be @tech{flat enumerations}
  and if it evaluates to @racket[#f], then the enumerations must not be @tech{flat enumerations}.
  If the keyword is not present, then the dependent expressions are expected to always
  produce @tech{flat enumerations}.

  If @racket[#:one-way?] is present and evaluates to a true value, then the
  result enumeration is a @tech{one way enumeration}
  
  The dependent expressions are expected to always produce @tech{two way enumerations}
  if the non-dependent expression is a @tech{two way enumeration} and the dependent
  the dependent expressions are expected to always produce @tech{one way enumerations}
  if the non-dependent expression is a @tech{one way enumeration}.
  
  @examples[#:eval
            the-eval
            (define ordered-pair/e
              (cons/de [hd natural/e]
                       [tl (hd) (nat+/e (+ hd 1))]))
            (enum->list ordered-pair/e 10)]
}

@defproc[(flip-dep/e [e enum?] 
                     [f (-> (enum-contract e)
                            (and/c (if f-range-finite?
                                       finite-enum?
                                       infinite-enum?)
                                   (if one-way?
                                       one-way-enum?
                                       two-way-enum?)
                                   (if flat?
                                       flat-enum?
                                       (not/c flat-enum?))))]
                     [#:f-range-finite? f-range-finite? boolean? #f]
                     [#:flat? flat? #t]
                     [#:one-way? one-way? boolean? (one-way-enum? e)])
         enum?]{
  Constructs an @tech{enumeration} of pairs like the second case of @racket[cons/de].
        
  @examples[#:eval
            the-eval
            (define flip-dep/e-ordered-pair/e
              (flip-dep/e natural/e 
                          (λ (tl) (below/e tl))
                          #:f-range-finite? #t))
            (enum->list flip-dep/e-ordered-pair/e 10)]
}

@defproc[(cons/e [e1 enum?] [e2 enum?]
                 [#:ordering ordering (or/c 'diagonal 'square) 'square])
         enum?]{

An @tech{enumeration} of pairs of the values from @racket[e1] and
@racket[e2]. Like @racket[list/e], the @racket[ordering] argument
controls how the resting elements appear.

@examples[#:eval the-eval
(enum->list (cons/e (take/e natural/e 4) (take/e natural/e 5)) 5)
(enum->list (cons/e natural/e (take/e natural/e 5)) 5)
(enum->list (cons/e (take/e natural/e 4) natural/e) 5)
(enum->list (cons/e natural/e natural/e) 5)]
}

@(begin
   (define listof/e-limit 500)
   (define lon (listof/e natural/e))
   (define lon2 (listof/e natural/e #:simple-recursive? #f))
   
   (define (build-length-stats)
     (define (get-points e color sym)
       (define lengths (make-hash))
       (define nums (make-hash))
       (for ([x (in-range listof/e-limit)])
         (define lst (from-nat e x))
         (define len (length lst))
         (hash-set! lengths len (+ 1 (hash-ref lengths len 0))))
       (points
        #:sym sym
        #:color color
        (for/list ([(k v) (in-hash lengths)])
          (vector k v))))
     (plot
      #:x-label "length"
      #:y-label "number of lists at that length"
      #:x-min -1
      #:y-min -10
      (list (get-points lon "red" 'circle) 
            (get-points lon2 "blue" '5star))))
   
   (define (build-value-stats)
     (define (get-points e color sym)
       (define values (make-hash))
       (define nums (make-hash))
       (for ([x (in-range listof/e-limit)])
         (define lst (from-nat e x))
         (for ([value (in-list lst)])
           (hash-set! values value (+ 1 (hash-ref values value 0)))))
       (points
        #:color color
        #:sym sym
        (for/list ([(k v) (in-hash values)])
          (vector k v))))
     (parameterize ([plot-y-transform  log-transform])
       (plot
        #:x-label "value"
        #:y-label "number of lists that contain that value"
        (list (get-points lon "red" 'circle)
              (get-points lon2 "blue" '5star))))))

@defproc[(listof/e [e (if simple-recursive?
                          enum?
                          infinite-enum?)]
                   [#:simple-recursive? simple-recursive? any/c #t])
         enum?]{

An @tech{enumeration} of lists of values
enumerated by @racket[e].


If @racket[simple-recursive?] is @racket[#f], then the enumeration
is constructed by first choosing a length and then using @racket[list/e]
to build lists of that length. If not, it builds a recursive enumeration
using @racket[delay/e]. The second option (which is the default) method is significantly
more efficient when calling @racket[from-nat] with large numbers, but
it also has much shorter lists near the beginning of the enumeration.

@examples[#:eval the-eval
(enum->list (listof/e natural/e #:simple-recursive? #f) 10)
(enum->list (listof/e natural/e) 10)
(to-nat (listof/e natural/e #:simple-recursive? #f) '(1 2 3 4 5 6))
(to-nat (listof/e natural/e) '(1 2 3 4 5 6))
]


This plot shows some statistics for the first @(number->string listof/e-limit)
items in each enumeration. The first plot shows how many different lengths
each encounters. The red circles are when the @racket[#:simple-recursive?]
argument is @racket[#t] and the blue stars are when that argument is
@racket[#f].

@(build-length-stats)

This plot shows the different values, but this time on a log scale. As you can
see, zero appears much more frequently when the @racket[#:simple-recursive?]
argument is @racket[#f].

@(build-value-stats)
}

@defproc[(non-empty-listof/e [e (if simple-recursive?
                                    enum?
                                    infinite-enum?)]
                             [#:simple-recursive? simple-recursive? any/c #t]) 
         enum?]{

Like @racket[listof/e], but without the empty list.

@examples[#:eval the-eval
(enum->list (non-empty-listof/e natural/e) 5)
]}

@defproc[(listof-n/e [e (if simple-recursive?
                            enum?
                            infinite-enum?)]
                     [n exact-nonnegative-integer?])
         enum?]{
                
  @examples[#:eval 
            the-eval
            (enum->list (listof-n/e natural/e 3) 10)]
}

@defform[(delay/e enum-expression ... keyword-options)
         #:grammar ([keyword-options
                     (code:line)
                     (code:line #:count count-expression keyword-options)
                     (code:line #:two-way-enum? two-way-boolean-expression keyword-options)
                     (code:line #:flat-enum? flat-boolean-expression keyword-options)])]{
 Returns an @tech{enumeration} immediately, without
 evaluating the @racket[enum-expression]s. When the result
 enumeration is inspected (directly or indirectly) via 
 @racket[from-nat], @racket[to-nat], or 
 @racket[enum-contract], the @racket[enum-expression]s are
 evaluated and the value of the last one is cached. The value is then used as
 the enumeration.
           
  If the @racket[count-expression] is not supplied or if it evaluates to @racket[+inf.0],
  the resulting enumeration is a @tech{infinite enumeration}. Otherwise the
  expression must evaluate to an @racket[exact-nonnegative-integer?] and the resulting
  enumeration is a @tech{finite enumeration} of the given count.
  
  If @racket[two-way-boolean-expression] is supplied and it evaluates to anything
  other than @racket[#f], the resulting
  enumeration must be a @tech{two way enumeration}; otherwise it must be a
  @tech{one way enumeration}.
  
  If @racket[flat-boolean-expression] is supplied and it evaluates to anything 
  other than @racket[#f], the resulting
  enumeration must be a @tech{flat enumeration}; otherwise it must not be.

  This expression form is useful for building recursive enumerations.
  @examples[#:eval
            the-eval
            (letrec ([bt/e (delay/e 
                            (or/e (single/e #f)
                                  (list/e bt/e bt/e)))])
              (enum->list bt/e 5))]

}

@defproc[(take/e [e enum?]
                 [n (if (finite-enum? e)
                        (integer-in 0 (enum-count e))
                        exact-nonnegative-integer?)]
                 [#:contract contract
                             (λ (x)
                               (and ((enum-contract e) x)
                                    (< (to-nat e x) n)))])
         finite-enum?]{

Identical to @racket[e] but only includes the first @racket[n] values.
             
If the @racket[contract] argument is not supplied, then @racket[e] must
be both a @tech{two way enumeration} and a @tech{flat enumeration}.

@examples[#:eval the-eval
                 (enum->list (take/e natural/e 5))]
}

@defproc[(slice/e [e enum?]
                  [lo (and/c (if (finite-enum? e)
                                 (integer-in 0 (enum-count e))
                                 exact-nonnegative-integer?)
                             (<=/c hi))]
                  [hi (if (finite-enum? e)
                          (integer-in 0 (enum-count e))
                          exact-nonnegative-integer?)]
                  [#:contract contract
                              (and/c (enum-contract e)
                                     (λ (x)
                                       (<= lo (to-nat e x))
                                       (< (to-nat e x) hi)))])
         finite-enum?]{

Identical to @racket[e] but only includes the values between
@racket[lo] (inclusive) and @racket[hi] (exclusive).

@examples[#:eval the-eval
                 (enum->list (slice/e natural/e 5 10))
                 (slice/e natural/e 20 20)]
}


@defproc[(fin/e [x any/c] ...)
         (and/c finite-enum? flat-enum?)]{

 Builds an @tech{enumeration} containing each @racket[x], in the order
 given.

 If there are multiple arguments, then they must all be
 distinct; numbers except for @racket[+nan.0] and @racket[+nan.f] are
 compared using @racket[=] and all others are compared using
 @racket[equal?]).
 
 If some other
 equality function is appropriate, use @racket[map/e]
 with @racket[(below/e n)] as the first argument to explicitly specify
 how to differentiate the elements of the
 enumeration.

 If all of the arguments match the contract
 @racketblock[(or/c symbol? boolean? char? keyword? null?
                    string? bytes? number?)]
 then the result is a @tech{two way enumeration}, otherwise it
 is a @tech{one way enumeration}.

 @examples[#:eval 
           the-eval
           (enum->list (fin/e "Brian" "Jenny" "Ki" "Ted"))
           (enum->list (fin/e 1 3 5 7 9 11 13 15))]
}

@defproc[(single/e [v any/c]
                   [#:equal? same? equal?])
         (and/c finite-enum? two-way-enum?)]{
  Returns an enumeration of count one containing only @racket[v].
                                 
  It uses @racket[same?] to build the contract in
  the enumeration, always passing @racket[v] as the first
  argument to @racket[same?].
  
  @examples[#:eval the-eval 
                   (enum->list (single/e 12345))
                   (enum->list (single/e (λ (x) x)))]
}


@defproc[(range/e [lo (and/c (or/c -inf.0 exact-integer?)
                             (<=/c hi))]
                  [hi (or/c exact-integer? +inf.0)])
         (and/c two-way-enum? flat-enum?)]{

An @tech{enumeration} of the exact integers between @racket[lo] and @racket[hi].

@examples[#:eval the-eval
(enum->list (range/e 10 20))
(enum->list (range/e 10 10))
(enum->list (range/e -inf.0 0) 10)
(enum->list (range/e -inf.0 +inf.0) 10)
]}

@defproc[(nat+/e [lo exact-nonnegative-integer?]) (and/c infinite-enum? two-way-enum? flat-enum?)]{

An @tech{enumeration} of natural numbers larger than @racket[lo].

@examples[#:eval the-eval
(enum->list (nat+/e 42) 5)
]}

@defproc[(vector/e [#:ordering ordering (or/c 'diagonal 'square) 'square]
                   [e enum?] ...) 
         enum?]{

An @tech{enumeration} of vectors of values enumerated by the
@racket[e].

The @racket[ordering] argument is the same as the one to @racket[list/e].

@examples[#:eval the-eval
                 (enum->list (vector/e (fin/e "Brian" "Jenny" "Ki" "Ted") 
                                       natural/e
                                       (fin/e "Terra" "Locke" "Edgar" "Mash"))
                             5)]
}

@defproc[(permutations-of-n/e [n exact-nonnegative-integer?])
         (and/c finite-enum? two-way-enum? flat-enum?)]{

Returns an @tech{enumeration} of the permutations of the natural
numbers smaller than @racket[n].

@examples[#:eval the-eval
(enum->list (permutations-of-n/e 3))
]}

@defproc[(permutations/e [l list?])
         enum?]{

Returns an @tech{enumeration} of the permutations of @racket[l].

@examples[#:eval the-eval
(enum->list (permutations/e '(Brian Jenny Ted Ki)))
]}

@defproc[(set/e [e enum?]) enum?]{

Returns an @tech{enumeration} of finite sets of values from @racket[e].

@examples[#:eval the-eval
(enum->list (set/e (fin/e "Brian" "Jenny" "Ki")))
(enum->list (set/e natural/e) 10)
]}

@defproc[(infinite-sequence/e [e finite-enum?])
         one-way-enum?]{

Returns an @tech{enumeration} of infinite sequences of elements of
@racket[e]. If @racket[e] is an empty enumeration, returns an empty enumeration.

The infinite sequence corresponding to the natural number @racket[_n]
is based on dividing the bits of @racket[(* (+ 1 _n) pi)] into chunks
of bits where the largest value is @racket[(enum-count e)]. Since
@racket[(* (+ 1 _n) pi)] has infinite digits, there are infinitely
many such chunks. Since @racket[*] is defined on all naturals, there
are infinitely many such numbers. The generation of the sequence is
efficient in the sense that the digits are generated incrementally
without needing to go deeper than to find the requested value. 
The generation of the sequence is inefficient in the sense that
the approximation of @racket[(* (+ 1 _n) pi)] gets larger and larger
as you go deeper into the sequence.

@examples[#:eval the-eval
(define bjtks/e (infinite-sequence/e 
                 (fin/e 'Brian 'Jenny 'Ted 'Ki)))
(for ([e (from-nat bjtks/e 42)]
      [i (in-range 10)])
  (printf "~a = ~a\n" i e))]}

@defproc[(hash-traverse/e [f (-> any/c enum?)]
                          [xs (hash/c any/c any/c)]
                          [#:get-contract get-contract (-> any/c contract?)])
         enum?]{

Constructs an @tech{enumeration} that simultaneously enumerates each
of the enumerations returned by @racket[f] applied to each value of
@racket[xs].

The @racket[get-contract] argument is applied to the keys in the
hash and is expected to return the contract for the corresponding
enumeration.

@examples[#:eval the-eval
(define hash-traverse-1/e
  (let ([h (hash "Brian" 5 "Jenny" 15 "Ted" 25 "Ki" 30)])
    (hash-traverse/e (λ (n) (below/e n))
                     h
                     #:get-contract
                     (λ (v) (and/c exact-integer? (<=/c (hash-ref h v)))))))
(enum->list hash-traverse-1/e 5)
(to-nat hash-traverse-1/e
        '#hash(("Brian" . 4) ("Jenny" . 1) ("Ted" . 16) ("Ki" . 7)))
]}


@defproc[(fold-enum [f (if f-range-finite?
                           (-> list? any/c finite-enum?)
                           (-> list? any/c infinite-enum?))]
                    [bs list?]
                    [#:f-range-finite? f-range-finite? #f])
         enum?]{

This is like @racket[foldr], but @racket[f] returns
@tech{enumerations} of @racket[_a]s and assumes that the accumulator
is initialized to @racket['()].

@examples[#:eval the-eval
(define fold-enum-1/e
  (fold-enum (λ (as b)
               (below/e (+ (foldr + 0 as) b)))
             (list 1 2 3)
             #:f-range-finite? #t))
(enum->list fold-enum-1/e 5)
(to-nat fold-enum-1/e (list 0 1 1))
]}


@subsection{Enumeration Utility}


@defproc[(random-index [e enum?])
         exact-nonnegative-integer?]{

Returns a random index into @racket[e]. This works for 
 finite and infinite enumerations, regardless of the count
 of the enumeration. For finite enumerations, it picks
 an index uniformly at random using @racket[random-natural]
 and for infinite enumerations it picks a natural number 
 @racket[n]
 from the geometric distribution and uses that as an
 exponent, picking uniformly at random in the interval
 between @racket[(expt 2 n)] and @racket[(expt 2 (+ n 1))].

@examples[#:eval the-eval
(random-index natural/e)
(random-index (below/e 5000000000))
]}


@subsection{Pre-built Enumerations}

This section describes enumerations of some common Racket
datatypes.

@defthing[char/e (and/c finite-enum? two-way-enum? flat-enum?)]{

An @tech{enumeration} of characters.

@examples[#:eval the-eval
(enum->list char/e 5)
(to-nat char/e #\λ)
]}

@defthing[string/e (and/c infinite-enum? two-way-enum? flat-enum?)]{

An @tech{enumeration} of strings.

@examples[#:eval the-eval
(enum->list string/e 5)
(to-nat string/e "racket")
]}

@defthing[bool/e (and/c finite-enum? two-way-enum? flat-enum?)]{

An @tech{enumeration} of booleans.

@examples[#:eval the-eval
(enum->list bool/e)
]}

@defthing[symbol/e (and/c infinite-enum? two-way-enum? flat-enum?)]{

An @tech{enumeration} of symbols.

@examples[#:eval the-eval
(enum->list symbol/e 5)
(to-nat symbol/e 'racket/base)
]}

@defthing[integer/e (and/c infinite-enum? two-way-enum? flat-enum?)]{

An @tech{enumeration} of the integers.

@examples[#:eval the-eval
(enum->list integer/e 10)
]}

@defthing[flonum/e (and/c infinite-enum? two-way-enum? flat-enum?)]{

An @tech{enumeration} of @racket[flonum?]s.

@examples[#:eval the-eval
(enum->list flonum/e 10)
(to-nat flonum/e 1.0)
(to-nat flonum/e -1.0)
]}

@defthing[exact-rational/e (and/c infinite-enum? one-way-enum? flat-enum?)]{
  An enumeration of rational numbers that
  duplicates entries (roughly, it enumerates
  all pairs of integers and natural numbers
  and then divides them which leads to duplicates).
  
  @examples[#:eval the-eval
                   (enum->list exact-rational/e 13)]
  }

@defthing[two-way-real/e (and/c infinite-enum? two-way-enum? flat-enum?)]{

An @tech{enumeration} of reals; it includes
   only @racket[integer/e] and @racket[flonum/e].

@examples[#:eval the-eval
(enum->list two-way-real/e 5)
]}


@defthing[real/e (and/c infinite-enum? one-way-enum? flat-enum?)]{

An @tech{enumeration} of reals; it includes
   @racket[exact-rational/e] and @racket[flonum/e].

@examples[#:eval the-eval
(enum->list real/e 10)
]}


@defthing[two-way-number/e (and/c infinite-enum? two-way-enum? flat-enum?)]{

An @tech{enumeration} of numbers; it includes
   @racket[two-way-real/e] and complex numbers
   made from pairs of those real numbers.

@examples[#:eval the-eval
(enum->list two-way-number/e 10)
]}

@defthing[number/e (and/c infinite-enum? one-way-enum? flat-enum?)]{

An @tech{enumeration} of numbers; it
   includes @racket[real/e] and complex
   numbers made from pairs of those real numbers.

@examples[#:eval the-eval
(enum->list number/e 10)
]}


@close-eval[the-eval]
