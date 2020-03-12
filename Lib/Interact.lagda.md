Contingent Interaction for a Turbulent World
============================================

```agda
module Lib.Interact where

open import Lib.Zero
open import Lib.One
open import Lib.Two
open import Lib.Sum
open import Lib.Pi
open import Lib.Sigma
open import Lib.Equality
open import Agda.Builtin.Nat renaming (_*_ to _*N_)
--open import Lib.Nat
open import Lib.Star
```



It's all very well enforcing the property that the answer is appropriate
to the question, but there's more to building interactive systems than
that. There should also be some situational awareness, and some
acknowledgement that no party to the interaction necessarily has things
all their own way.


Interaction Structures from Hancock and Setzer
----------------------------------------------

Peter Hancock and Anton Setzer came up with a recipe for modelling this
more contingent notion of interaction. Instead of working in Set, we
work in Set indexed by some notion of "status of the system".

In the following, `O` represents the possible statuses before one
interaction, and `I` represents the possible statuses afterwards.
To interact, we should know what constitutes a status-appropriate question;
we should know what constitutes a question-appropriate answer; and we
should know how the whole of that interaction determines the resulting
status.

```agda
record _?>_ (I O : Set) : Set1 where
  constructor _<?_/_
  field
    Question  : O -> Set
    Answer    : (o : O) -> Question o -> Set
    status    : (o : O)(q : Question o) ->
                Answer o q -> I
  --^^ wot no WTF?

  _-Chat_ : (I -> Set) -> (O -> Set)
  _-Chat_ G o = Question o >< \ q ->
                (a : Answer o q) ->
                G (status o q a)
open _?>_ public                
```

(In the future, we'll be able to ensure that the status is purely
*static* information, using the `@0` modality. `@0` before a variable
binding means "known to the typechecker but not at runtime". The
Indian invention of zero, as passed on to us by Arabic mathematicians,
was a significant liberation. I remembered that lesson while staring
into an empty pint in 2014: it's useful to be able to talk about
having none of something.  In 2015, I wrote a paper about that called
"I got plenty o' nuttin'" which seems have caused quite a stir. And in
particular, it provoked Andreas Abel to add zero-quantity variables to
Agda. Here, we could use them to ensure that the "status" is a purely
*static* model of significant aspects of the interactive system,
rather than an actual run-time data structure. However, in the current
version, the compiler does not handle them correctly and generated
code has scope errors. Oops!)

The plan is to use status information only to index sets of data which
*do* exist at runtime, and we exploit propositions-as-types to
conflate the logical notions of "precondition" and "postcondition"
with the programming notions of "input" and "output". Given any such
interaction structure `F` and a goal `G : I -> Set` for our status
afterwards, we obtain `F -Chat G : O -> Set` which is the property
that our goal is *achievable* by *one* interaction. That property is
witnessed by the *strategy* for achieving the goal, consisting of a
choice of question and the means to continue to a `G` given the
answer. `G` must hold for whatever the final `status` may be, and that
is not necessarily under the entire control of either party.

We're working in categories where the objects are indexed sets in some
`X -> Set` and the arrows are index-respecting maps in `[ P -:> Q
]`. That is, *all* we know about the initial status is whatever `P`
tells us.

```agda
_-chat_ : forall {I O : Set}(F : I ?> O)
          {P Q : I -> Set} ->
          [ P -:> Q ] ->
          [ F -Chat P -:> F -Chat Q ]
(F -chat f) (q , k) = q , (\ a -> f (k a))
```


Clients, a.k.a. The Free Monad on an Interaction Structure
----------------------------------------------------------

Let's think through what a client strategy becomes. Fix `F`, an interaction
structure. Explain what it is to have a plan to be a client achieving *goal*
`G`.

```agda
module _ {I : Set}(F : I ?> I) where

  data Client (G : I -> Set)(i : I) : Set where
    return : G i -> Client G i
    ask    : (F -Chat Client G) i -> Client G i
```

Here are some handy combinators for programming with these structures.
We get the means to ask `get -eh?` and `put s -eh?`: programs which
issue a single question and succeed in the goal of giving back a single
answer resulting in exactly the advertised `status`. Those single
question programs can be plugged together with a monadic "bind" operator,
`>>=`, whose type gets cuter if you write its flipped version, `=<<`,
instead. The behaviour is to glue more client strategy on at all the
leaves of an existing client strategy.

```agda
module _ {I : Set}{F : I ?> I} where

  _-eh? : {i : I}(q : Question F i) ->
    Client F (\ j -> Answer F i q >< \ a -> status F i q a ~ j) i
  q -eh? = ask (q , \ a -> return (a , r~))

  _=<<_ : forall {P Q : I -> Set} ->
    [ P -:> Client F Q ] ->
    [ Client F P -:> Client F Q ]
  k =<< return p = k p
  k =<< ask (q , j) = ask (q , \ a -> k =<< j a)

  _>>=_ : forall {P Q : I -> Set} ->
    {i : I} -> Client F P i ->
    [ P -:> Client F Q ] ->
    Client F Q i
  c >>= k = k =<< c

  infixr 10 _>>=_
  infix 11 _-eh?
```

At some point, we should define equivalence of strategies and prove that
the `[ P -:> Client F Q ]` give us the arrows of a category (the "Kleisli
Category"). They are programs which achieve postcondition `Q` given
precondition `P`. We end up with something a lot like Sir Tony Hoare's
logic for reasoning about imperative programming, except that we're using
it as our type system. The identity is Tony's `skip` operator (which does
nothing), and composition behaves like Tony's `;` where the postcondition
of the first component becomes the precondition for the second.


I should say something about why we have a *monad* and what makes it
*free*.  Note that it's not a monad in the category of types and
functions, like in Haskell, but it's still a monad. We've moved to the
category of indexed sets and index-preserving functions, but the idea
of monad stays the same. Now, our client strategy trees can be
interpreted recursively as computations in any other monad, but you'd
expect `return` to be interpreted as return and `>>=` to be interpreted
as bind (or equivalently that we have a functor between Kleisli categories,
making skip skip and semicolon semicolon). An interpreter which satisfies
this entirely reasonable condition is called a "monad homomorphism", because
it preserves the meaning of the monadic gadgetry. It's fairly clear that if
you can explain how to run every possible `q -eh?` program, you've got
yourself an interpreter: just answer the questions one at a time. What's
less obvious is that those are the only *monad* homomorphisms. Remember the way
lists can't help being monoidal because they're built by concatenating stuff,
and their monoid homomorphisms just say what to do with the stuff? We say
lists are *free* monoids because being monoidal is all there is to them.
Same here. Clients can't help being monadic, and being monadic is all there
is to them: to construct a monad homomorphism, explain how to handle the
underlying interaction structure.


Servers for Clients, a.k.a., Cofree Comonads
--------------------------------------------

We should say how to be a server for an interaction structure. That amounts
to explaining two things:

  * why we satisfy some condition for being "happy"
  * how to answer a question and evolve

(I've tweaked this from lectures. We should be able to display happiness
even when not asked a question.)

```agda
module _ {I : Set}
         (F : I ?> I)    -- interaction structure
         (H : I -> Set)  -- happiness: think Mickey Mouse in DisneyWorld
  where

  record Server (i : I) : Set where
    coinductive
    field
      display : H i                      -- we can always display happiness
      react   : (q : Question F i)       -- and given a question...
             -> Answer F i q >< \ a
             -> Server (status F i q a)  -- what answer we give

  open Server public
```  

Now, we can log the behaviour of a server, with entries like the following:

```agda
  record LogEntry (i j : I) : Set         -- how an i-to-j step happened
    where
    constructor log
    field
      displayed : H i                            -- we were happy at i
      asked     : Question F i                   -- a question was asked
      answered  : Answer F i asked               -- we answered it
      reached   : status F i asked answered ~ j  -- we reached j
```

The `Rats` (i.e. `Star` backwards) data structure allows us to record a
sequence of log entries stretching leftward into the past, all connecting
up properly.

```agda
module _ {I : Set}{F : I ?> I}{G H : I -> Set} where

  interact : {i j : I}                 -- we started at i, we're j now
          -> Rats (LogEntry F H) i j   -- how we got to j
          -> Client F G j              -- the client wants G
          -> Server F H j              -- the server is happy like H
          -> I >< \ k ->                 -- we will reach k
             Rats (LogEntry F H) i k     -- (and remember our history), where
           * G k                         -- the client will achieve its goal
           * Server F H k                -- and the server will still be happy
  interact lz (return g) s = _ , lz  , g , s
  interact lz (ask (q , k)) s with display s | react s q
  ... | h | a , s' = interact (lz -, log (display s) q a r~) (k a) s'
```

