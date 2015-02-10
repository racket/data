#lang scribble/manual
@(require scribble/eval
          (for-label data/enumerate
                     data/enumerate/lib
                     racket/math
                     racket/set
                     racket/contract
                     racket/match
                     racket/base))

@title{Enumerations}
@defmodule[data/enumerate #:no-declare]
@declare-exporting[data/enumerate data/enumerate/lib]

@(define the-eval (make-base-eval))
@(the-eval '(require data/enumerate data/enumerate/lib
                     racket/set racket/string 
                     racket/contract racket/match))
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
@racket[nat/e] is just a pair of identity functions:
@interaction[#:eval
             the-eval
             (from-nat nat/e 0)
             (to-nat nat/e 1)]
but the library builds up more complex enumerations from
simple ones. For example, you can enumerate lists of the
elements of other enumerations using @racket[list/e]:
@interaction[#:eval
             the-eval
             (from-nat (list/e nat/e nat/e nat/e) 0)
             (from-nat (list/e nat/e nat/e nat/e) 1)
             (from-nat (list/e nat/e nat/e nat/e) (expt 2 100))
             (to-nat (list/e nat/e nat/e nat/e) (list 123456789 123456789 123456789))]
To interleave two enumerations, use @racket[or/e]:
@interaction[#:eval
             the-eval
             (from-nat (or/e nat/e (list/e nat/e nat/e)) 0)
             (from-nat (or/e nat/e (list/e nat/e nat/e)) 1)
             (from-nat (or/e nat/e (list/e nat/e nat/e)) 2)
             (from-nat (or/e nat/e (list/e nat/e nat/e)) 3)
             (from-nat (or/e nat/e (list/e nat/e nat/e)) 4)]
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
           (cons/de [hd nat/e]
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
            (from-nat ordered-pair/e i))]

Until we got to @racket[map/e], all of the enumeration functions have built
enumerations that are guaranteed to be bijections. But since @racket[map/e]
accepts arbitrary functions, enumerations that it produces may not be bijections.
To help avoid errors, it's contract does some random checking to see if
the argument functions form a bijection. Here's an example that, with high
probability, signals a contract violation.
@interaction[#:eval
             the-eval
             (map/e (λ (x) (floor (/ x 100)))
                    (λ (x) (* x 100))
                    nat/e
                    #:contract exact-nonnegative-integer?)]


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
enumeration also has a contract, a size, and three boolean
properties associated with it: if it is finite
or not, if it is a bijection to the natural numbers or
merely maps from the natural numbers without going back, and
if the contract is has is a @racket[flat-contract?].

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

@defproc[(enum-size [e finite-enum?]) exact-nonnegative-integer?]{
  Returns the size of an @tech{enumeration}.
}

@defproc[(enum-contract [e finite-enum?]) exact-nonnegative-integer?]{
  Returns the @racket[contract?] that @racket[e] enumerates.
}

@section{Querying Enumerations}

The functions in this section exercise the enumeration,
turning natural numbers back and forth to the values
that an enumeration enumerates.

@defproc[(from-nat [e enum?] [n (if (finite-enum? e)
                                    (integer-in 0 (enum-size e))
                                    exact-nonnegative-integer?)])
         (enum-contract e)]{
  Decodes @racket[n] from @racket[e].
}

@defproc[(to-nat [e two-way-enum?] [x (enum-contract e)])
         (if (finite-enum? e)
             (integer-in 0 (enum-size e))
             exact-nonnegative-integer?)]{
  Encodes @racket[x] from @racket[e].
}

@defproc[(approximate [e enum?] 
                      [n (if (finite-enum? e)
                             (integer-in 0 (enum-size e))
                             exact-nonnegative-integer?)]) 
         (listof (enum-contract e))]{
  Returns a list of the first @racket[n] values in @racket[e].

  @examples[#:eval 
            the-eval
            (approximate (list/e nat/e nat/e) 8)]
}

@section{Constructing Enumerations}

This section contains the fundamental operations for building
enumerations.

@defthing[nat/e enum?]{

An @tech{enumeration} of the natural numbers.
   
@examples[#:eval the-eval
(from-nat nat/e 5)
(to-nat nat/e 5)
]}

@defproc[(below/e [max exact-nonnegative-integer?]) enum?]{

An @tech{enumeration} of the first @racket[max] naturals.

@examples[#:eval the-eval
(to-list (below/e 10))
]}

@defthing[empty/e enum?]{

The empty @tech{enumeration}.

@examples[#:eval the-eval
(to-list empty/e)
]}


@defproc[(map/e [f (dynamic->* #:mandatory-domain-contracts (map enum-contract e)
                               #:range-contracts (list c))]
                [f-inv (dynamic->* #:mandatory-domain-contracts (list c)
                                   #:range-contracts (map enum-contract e))]
                [#:contract c contract?]
                [e enum?] ...+)
         enum?]{
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
                    nat/e
                    #:contract (and/c exact-nonnegative-integer?
                                      even?)))
           (approximate evens/e 10)
           (define odds/e
             (map/e add1
                    sub1
                    evens/e
                    #:contract (and/c exact-nonnegative-integer?
                                      odd?)))
           (approximate odds/e 10)]
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
           (approximate rationals/e 10)]
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
                   (except/e nat/e 3))
                 (from-nat except-1/e 2)
                 (from-nat except-1/e 4)
                 (to-nat except-1/e 2)
                 (to-nat except-1/e 4)]}

@defproc[(or/e [e-p (or/c flat-enum? (cons/c enum? (-> any/c boolean?)))] ...) 
         enum?]{

An @tech{enumeration} of all of the elements of the enumerations in
the @racket[e-p] arguments. If an @racket[e-p] is a pair, then the predicate is used
to identify its elements (the predicate needs only to be able
to distinguish elements of its enumeration from the others). If
@racket[e-p] is a @tech{flat enumeration}, the predicate is extracted from the
@tech{enumeration}'s predicate.

@examples[#:eval the-eval
                 (approximate (or/e nat/e (list/e nat/e nat/e))
                              10)]
}

@defproc[(append/e [e-p (or/c flat-enum? (cons/c enum? (-> any/c boolean?)))] ...+) 
         enum?]{

An @tech{enumeration} of the elements of the enumerations given in
@racket[e-p] that enumerates the elements in order that the enumerations
are supplied. All but the last enumeration must be finite.

@examples[#:eval the-eval
                 (approximate 
                  (append/e (take/e nat/e 4)
                            (list/e nat/e nat/e))
                  10)]
}

@defproc[(thunk/e [eth (-> (and/c (if (= size +inf.0)
                                      infinite-enum?
                                      (and/c finite-enum?
                                             (let ([matching-size? (λ (e) (= (enum-size e) size))])
                                               matching-size?)))
                                  (if is-two-way-enum?
                                      two-way-enum?
                                      one-way-enum?)
                                  (if is-flat-enum?
                                      flat-enum?
                                      (not/c flat-enum?))))]
                  [#:size size (or/c +inf.0 exact-nonnegative-integer?) +inf.0]
                  [#:two-way-enum? is-two-way-enum? any/c #t]
                  [#:flat-enum? is-flat-enum? any/c #t])
         enum?]{

A delayed @tech{enumeration} identical to the result of @racket[eth].
          
The @racket[size], @racket[is-two-way-enum?], and @racket[is-flat-enum?]
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
                   (approximate bt/e 5))]
}

@defproc[(list/e [#:ordering ordering (or/c 'diagonal 'square) 'square] [e enum?] ...) enum?]{

An @tech{enumeration} of lists of values enumerated by the
@racket[e].

If @racket[ordering] is @racket['square], it uses a generalized form
of Szudzik's ``elegant'' ordering and if @racket[ordering] is @racket['diagonal],
it uses a generalized form of Cantor's mapping from pairs of naturals
to naturals.

@examples[#:eval the-eval
                 (approximate (list/e
                               (fin/e "Brian" "Jenny" "Ki" "Ted") 
                               nat/e
                               (fin/e "Terra" "Locke" "Edgar" "Mash"))
                              5)
                 (approximate (list/e nat/e nat/e)
                              10)
                 (approximate (list/e #:ordering  'diagonal nat/e nat/e)
                              10)]
}

@defproc[(dep/e [e enum?] 
                [f (-> (enum-contract e)
                       (and/c (if f-range-finite?
                                  finite-enum?
                                  infinite-enum?)
                              (if (two-way-enum? e)
                                  two-way-enum?
                                  one-way-enum?)))]
                [#:f-range-finite? f-range-finite? boolean? #f])
         enum?]{
  Constructs an @tech{enumeration} of pairs like the first case of @racket[cons/de].
        
  @examples[#:eval
            the-eval
            (define dep/e-ordered-pair/e
              (dep/e nat/e 
                     (λ (hd) (nat+/e (+ hd 1)))))
            (approximate dep/e-ordered-pair/e 10)]
}

@defproc[(bounded-list/e [k exact-nonnegative-integer?] [n exact-nonnegative-integer?]) enum?]{

An @tech{enumeration} of tuples of naturals up to @racket[n] of length @racket[k].

@examples[#:eval the-eval
(approximate (bounded-list/e 3 2)
             5)
]}


@section{More Enumeration Operations}
@defmodule[data/enumerate/lib]

The @racket[data/enumerate/lib] extends @racket[data/enumerate] with a bunch of
new ways to build enumerations, some utility functions, and a bunch of pre-built
enumerations.

@subsection{More Enumeration Constructors}


@defform*[[(cons/de [car-id car-enumeration-expr] 
                    [cdr-id (car-id) cdr-enumeration-expr] 
                    cons/dc-option)
           (cons/de [car-id (cdr-id) car-enumeration-expr]
                    [cdr-id cdr-enumeration-expr]
                    cons/dc-option)]
          #:grammar ([cons/de-option (code:line)
                                     (code:line #:dep-expression-finite? expr)])]{
  Constructs an @tech{enumeration} of pairs where the first component
                of the pair is drawn from the @racket[car-enumeration-expr]'s
                value and the second is drawn from the @racket[cdr-enumeration-expr]'s
                value.
                
  In the first form, the @racket[cdr-enumeration-expr] can use @racket[car-id], which
  is bound to the value of the car position of the pair, mutatis mutandis in the second case.
  
  If @racket[#:dep-expression-finite?] keyword and expression are present, then the
  value of the dependent expression is expected to be an infinite enumeration 
  if the expression evaluates to @racket[#f] and a finite enumeration otherwise. If
  the keyword is not present, then the dependent expressions are expected to always
  produce infinite enumerations.
  
  The dependent expressions are expected to always produce @tech{two way enumerations}
  if the non-dependent expression is a @tech{two way enumeration} and the dependent
  the dependent expressions are expected to always produce @tech{one way enumerations}
  if the non-dependent expression is a @tech{one way enumeration}.
  
  @examples[#:eval
            the-eval
            (define ordered-pair/e
              (cons/de [hd nat/e]
                       [tl (hd) (nat+/e (+ hd 1))]))
            (approximate ordered-pair/e 10)]
}

@defproc[(flip-dep/e [e enum?] 
                     [f (-> (enum-contract e)
                            (and/c (if f-range-finite?
                                       finite-enum?
                                       infinite-enum?)
                                   (if (two-way-enum? e)
                                       two-way-enum?
                                       one-way-enum?)))]
                     [#:f-range-finite? f-range-finite? boolean? #f])
         enum?]{
  Constructs an @tech{enumeration} of pairs like the second case of @racket[cons/de].
        
  @examples[#:eval
            the-eval
            (define flip-dep/e-ordered-pair/e
              (flip-dep/e nat/e 
                          (λ (tl) (below/e tl))
                          #:f-range-finite? #t))
            (approximate flip-dep/e-ordered-pair/e 10)]
}

@defform[(delay/e enum-expression keyword-options)
         #:grammar ([keyword-options
                     (code:line)
                     (code:line #:size size-expression keyword-options)
                     (code:line #:two-way-enum? two-way-boolean-expression keyword-options)
                     (code:line #:flat-enum? flat-boolean-expression keyword-options)])]{
 Returns an @tech{enumeration} immediately, without
 evaluating @racket[enum-expression]. When the result
 enumeration is inspected (directly or indirectly) via 
 @racket[from-nat], @racket[to-nat], or 
 @racket[enum-contract], the @racket[enum-expression] is
 evaluated and it's value cached. The value is then used as
 the enumeration.
           
  If the @racket[size-expression] is not supplied or if it evaluates to @racket[+inf.0],
  the resulting enumeration is a @tech{infinite enumeration}. Otherwise the
  expression must evaluate to an @racket[exact-nonnegative-integer?] and the resulting
  enumeration is a @tech{finite enumeration} of the given size.
  
  If @racket[two-way-boolean-expression] is supplied and it evaluates to anything
  other than @racket[#f], the resulting
  enumeration must be a @tech{one way enumeration}; otherwise it must be a
  @tech{two way enumeration}.
  
  If @racket[flat-boolean-expression] is supplied and it evaluates to anything 
  other than @racket[#f], the resulting
  enumeration must be a @tech{flat enumeration}; otherwise it must not be.

  This expression form is useful for building recursive enumerations.
  @examples[#:eval
            the-eval
            (letrec ([bt/e (delay/e 
                            (or/e (single/e #f)
                                  (list/e bt/e bt/e)))])
              (approximate bt/e 5))]

}

@defproc[(take/e [e enum?]
                 [n (if (finite-enum? e)
                        (integer-in 0 (enum-size e))
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
                 (to-list (take/e nat/e 5))]
}

@defproc[(slice/e [e enum?]
                  [lo (and/c (if (finite-enum? e)
                                 (integer-in 0 (enum-size e))
                                 exact-nonnegative-integer?)
                             (<=/c hi))]
                  [hi (if (finite-enum? e)
                          (integer-in 0 (enum-size e))
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
                 (to-list (slice/e nat/e 5 10))
                 (slice/e nat/e 20 20)]
}


@defproc[(fin/e [x (or/c symbol? boolean? char? keyword? null?
                         string? bytes? number?)] ...) 
         enum?]{

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

 @examples[#:eval 
           the-eval
           (to-list (fin/e "Brian" "Jenny" "Ki" "Ted"))
           (to-list (fin/e 1 3 5 7 9 11 13 15))]
}

@defproc[(single/e [v any/c]
                   [#:equal? same? equal?])
         (and/c finite-enum? bijective-enum?)]{
  Returns an enumeration of size @racket[1] containing
                                 @racket[v].
                                 
  It uses @racket[same?] to build the contract in
  the enumeration, always passing @racket[v] as the first
  argument to @racket[same?].
  
  @examples[#:eval the-eval 
                   (to-list (single/e 12345))
                   (to-list (single/e (λ (x) x)))]
                                               
}
@defproc[(cons/e [e1 enum?] [e2 enum?]
                 [#:ordering ordering (or/c 'diagonal 'square) 'square])
         enum?]{

An @tech{enumeration} of pairs of the values from @racket[e1] and
@racket[e2]. Like @racket[list/e], the @racket[ordering] argument
controls how the resting elements appear.

@examples[#:eval the-eval
(approximate (cons/e (take/e nat/e 4) (take/e nat/e 5)) 5)
(approximate (cons/e nat/e (take/e nat/e 5)) 5)
(approximate (cons/e (take/e nat/e 4) nat/e) 5)
(approximate (cons/e nat/e nat/e) 5)]
}

@defproc[(hash-traverse/e [f (-> any/c enum?)] [xs (hash/c any/c any/c)]) enum?]{

Constructs an @tech{enumeration} that simultaneously enumerates each
of the enumerations returned by @racket[f] applied to each value of
@racket[xs].

@examples[#:eval the-eval
(define hash-traverse-1/e
  (let ([h (hash "Brian" 5 "Jenny" 15 "Ted" 25 "Ki" 30)])
    (hash-traverse/e (λ (n) (below/e n))
                     h
                     #:get-contract
                     (λ (v) (and/c exact-integer? (<=/c (hash-ref h v)))))))
(approximate hash-traverse-1/e 5)
(to-nat hash-traverse-1/e
        '#hash(("Brian" . 4) ("Jenny" . 1) ("Ted" . 16) ("Ki" . 7)))
]}


@defproc[(fold-enum [f (-> (listof a) b enum?)] [bs (listof b)]) enum?]{

This is like @racket[foldr], but @racket[f] returns
@tech{enumerations} of @racket[_a]s and assumes that the accumulator
is initialized to @racket['()].

@examples[#:eval the-eval
(define fold-enum-1/e
  (fold-enum (λ (as b)
               (below/e (+ (foldr + 0 as) b)))
             (list 1 2 3)))
(approximate fold-enum-1/e 5)
(to-nat fold-enum-1/e (list 0 1 1))
]}

@defproc[(range/e [lo (and/c (or/c -inf.0 exact-integer?)
                             (<=/c hi))]
                  [hi (or/c exact-integer? +inf.0)])
         enum?]{

An @tech{enumeration} of the exact integers between @racket[lo] and @racket[hi].

@examples[#:eval the-eval
(to-list (range/e 10 20))
(to-list (range/e 10 10))
(approximate (range/e -inf.0 0) 10)
(approximate (range/e -inf.0 +inf.0) 10)
]}


@defproc[(listof/e [e enum?]) enum?]{

An @tech{enumeration} of lists of length @racket[n] of values
enumerated by @racket[e]. If @racket[n] is not given, lists of any
size are enumerated.

@examples[#:eval the-eval
(approximate (many/e nat/e) 5)
(approximate (many/e nat/e 5) 5)
]}

@defproc[(non-empty-listof [e enum?]) enum?]{

An @tech{enumeration} of non-empty lists of values enumerated by
@racket[e].

@examples[#:eval the-eval
(approximate (many1/e nat/e) 5)
]}

@defproc[(vector/e [e enum?] ...) enum?]{

An @tech{enumeration} of vectors of values enumerated by the
@racket[e].

@examples[#:eval the-eval
(approximate (cantor-vec/e (fin/e "Brian" "Jenny" "Ki" "Ted") 
                           nat/e
                           (fin/e "Terra" "Locke" "Edgar" "Mash"))
             5)
]}

@defproc[(nat+/e [lo exact-nonnegative-integer?]) enum?]{

An @tech{enumeration} of tuples of naturals of larger than @racket[lo].

@examples[#:eval the-eval
(approximate (nat+/e 42)
             5)
]}


@defproc[(permutations-of-n/e [n exact-nonnegative-integer?])
         enum?]{

Returns an @tech{enumeration} of the permutations of the natural
numbers smaller than @racket[n].

@examples[#:eval the-eval
(approximate (permutations-of-n/e 3) 5)
]}

@defproc[(permutations/e [l list?])
         enum?]{

Returns an @tech{enumeration} of the permutations of @racket[l].

@examples[#:eval the-eval
(approximate (permutations/e '(Brian Jenny Ted Ki)) 5)
]}

@defproc[(infinite-sequence/e [e enum?])
         one-way-enum?]{

Returns an @tech{enumeration} of infinite sequences of elements of
@racket[e].

The infinite sequence corresponding to the natural number @racket[_n]
is based on dividing the bits of @racket[(* (+ 1 _n) pi)] into chunks
of bits where the largest value is @racket[(enum-size e)]. Since
@racket[(* (+ 1 _n) pi)] has infinite digits, there are infinitely
many such chunks. Since @racket[*] is defined on all naturals, there
are infinitely many such numbers. The generation of the sequence is
efficient in the sense that the digits are generated incrementally
without needing to go deeper than to find the requested value. 
The generation of the sequence is inefficient in the sense that
the approximation of @racket[(* (+ 1 _n) pi)] gets larger and larger
as you go deeper into the sequence.

@examples[#:eval the-eval
(define bjtk/e (from-list/e '(Brian Jenny Ted Ki)))
(define bjtks/e (infinite-sequence/e bjtk/e))
(for ([e (from-nat bjtks/e 42)]
      [i (in-range 10)])
  (printf "~a = ~a\n" i e))]}

@subsection{Enumeration Utilities}


@defproc[(random-index [e enum?])
         exact-nonnegative-integer?]{

Returns a random index into @racket[e]. This works for 
 finite and infinite enumerations, regardless of the size
 of the enumeration. For finite enumerations, it picks
 an index uniformly at random using @racket[random-natural]
 and for infinite enumerations it picks a natural number 
 from the geometric distribution and uses that as an
 exponent, picking uniformly at random in the interval
 between 2 to that number and 2 to that power plus one.

@examples[#:eval the-eval
(random-index nat/e)
(random-index (below/e 5000000000))
]}


@defproc[(to-stream [e enum?]) stream?]{

Returns a stream of the values in @racket[e].

@examples[#:eval the-eval
(to-stream map-2/e)
]}

@defproc[(to-list [e enum?]) list?]{

Returns a list of the @racket[n] values in @racket[e]. This will
diverge if @racket[e] is infinite.

@examples[#:eval the-eval
(to-list (take/e map-2/e 5))
]}

@subsection{Pre-built Enumerations}

@defthing[integer/e enum?]{

An @tech{enumeration} of the integers.

@examples[#:eval the-eval
(approximate int/e 10)
]}



@defthing[char/e enum?]{

An @tech{enumeration} of characters.

@examples[#:eval the-eval
(approximate char/e 5)
]}

@defthing[string/e enum?]{

An @tech{enumeration} of strings.

@examples[#:eval the-eval
(approximate string/e 5)
]}

@defthing[float/e enum?]{

An @tech{enumeration} of flonums.

@examples[#:eval the-eval
(approximate float/e 5)
]}

@defthing[real/e enum?]{

An @tech{enumeration} of reals.

@examples[#:eval the-eval
(approximate real/e 5)
]}

@defthing[non-real/e enum?]{

An @tech{enumeration} of non-real numbers.

@examples[#:eval the-eval
(approximate non-real/e 5)
]}

@defthing[num/e enum?]{

An @tech{enumeration} of numbers.

@examples[#:eval the-eval
(approximate num/e 5)
]}

@defthing[bool/e enum?]{

An @tech{enumeration} of booleans.

@examples[#:eval the-eval
(to-list bool/e)
]}

@defthing[symbol/e enum?]{

An @tech{enumeration} of symbols.

@examples[#:eval the-eval
(approximate symbol/e 5)
]}

@defthing[base/e enum?]{

An @tech{enumeration} of atomic Racket values.

@examples[#:eval the-eval
(approximate base/e 5)
]}

@defthing[any/e enum?]{

An @tech{enumeration} of S-expressions.

@examples[#:eval the-eval
(approximate any/e 5)
]}

@close-eval[the-eval]
