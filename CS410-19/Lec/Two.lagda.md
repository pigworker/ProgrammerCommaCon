A Digression On Ordering
========================

```agda
module CS410-19.Lec.Two where

open import Lib.Zero
open import Lib.One
open import Lib.Splatoid
open import Lib.Nat
open import Lib.Sigma
open import Lib.Equality
```

Let me refactor `LeNat` from [the previous lecture](One.lagda.md) as a
`Splatoid`. (A `Splatoid` is a set with *at most one* element; i.e., all
elements are equal; i.e., there are no actual bits in an element.)
Right-click on `Splatoid` in the Agda code to check out its definition. 

```agda
LeNat : Nat -> Nat -> Splatoid
LeNat ze     y      = SplatOne
LeNat (su x) ze     = SplatZero
LeNat (su x) (su y) = LeNat x y
```

(Another wee note (pun intended). When we began the construction, with a
goal like

```agda-example
LeNat : Nat -> Nat -> Splatoid
LeNat x y = ?? -- agda-mode gets confused by question marks in non-Agda code blocks
```

the `Splatoid` type had a *yellow* background. That's because Agda was sus-*pish*-ous
of it. Specifically, Agda was unable to infer the hidden `Level` argument to `Splatoid`.
As soon as we fill in `SplatOne` or `SplatZero`, the `Level` is determined to be the
lowest level.)

(What's this `Level` business? Well, to avoid logical paradoxes, e.g.,
[Russell's Paradox](https://en.wikipedia.org/wiki/Russell%27s_paradox),
Agda stratifies types as ordinary sets (which don't mention the set of sets)
at level zero, sets which talk about all level zero sets at level one,
sets which talk about all level one sets at level two, and so on. If you want
to hear Bertrand Russell aged 93 talking about science and politics and
stuff, I have a recording of him:
[Side 1](https://personal.cis.strath.ac.uk/conor.mcbride/BR-1.mp3)
[Side 2](https://personal.cis.strath.ac.uk/conor.mcbride/BR-2.mp3).)

But I digress...

Preorders
---------

A *preorder* is a set `X` equipped with a *relation* `R` which is both
*reflexive* and *transitive*. By relation, I mean "family of `Splatoid`s",
so that there's at most one way for something to be related to something
else.

```agda
record Preorder {X : Set}(R : X -> X -> Splatoid) : Set where
  field
    reflexive  : forall x -> Splat (R x x)
    transitive : forall x y z
              -> Splat (R x y) -> Splat (R y z) -> Splat (R x z)
```

You can picture a preorder as a diagram of blobs corresponding to the
elements of `X`, some of which are joined by arrows corresponding to
evidence of related ness between two elements.

```asciiart
        o
       ^^^
      / | \
     o  |  o
      ^ | ^
       \|/
        o
```

*Reflexivity* means that every blob has an arrow to itself. (We don't normally
draw them, but we know they're there.)

```asciiart
     ->o-
    /    \
    \____/
```

*Transitivity* means that whenever there's an *indirect* route from one blob to
another, there's also a *direct* route. (Again, we often omit the implied arrows,
whenever a path is visible, to reduce clutter.)

```asciiart
   o----->o----->o
    \            ^
     \__________/
```

Let's show that `LeNat` is a preorder on numbers.

```agda
module _ where  -- Conor, remember to say something about what this is for

  open Preorder
```

I'm glad I reminded myself. What's going on with this `module _` business?
Agda lets you create anonymous modules which are opened as soon as they're
finished (as they have no name, it would be hard to open them otherwise).
Why would anyone do such a thing? Tidiness! I want to open `Preorder`, so
that its fields are in scope while I make *one* construction, but I don't
want its fields to be in scope globally. The anonymous module gives me a
private workspace in which I can say `open Preorder`. Crucially, I *don't*
say `open Preorder public`, so the fields of `Preorder` don't escape.

```agda
  leNat : Preorder LeNat
  reflexive leNat ze = <>
  reflexive leNat (su x) = reflexive leNat x
  transitive leNat ze y z xy yz = <>
  transitive leNat (su x) (su y) (su z) xy yz = transitive leNat x y z xy yz
```

There's lots more to say about the above. Firstly, I've chosen to give the
fields of the `Preorder` record by *copattern matching*. (You don't get that
in Haskell.) The fields are just functions, so I should be able to define them
by equations, and here I do. By making that choice, I stay working on the *left*,
and in particular, I can start *pattern* matching on the numbers. It's called
"copattern matching" because were writing about how things are used, instead of
about how they're made.

Secondly, notice that *proof by induction* becomes "writing functions by
structural recursion". There was only one idea, after all.

Thirdly (and perhaps most importantly), the pattern matching strategy for these
proofs is not an accident. It is found by asking the question "Why is it stuck?".
That is a CS410 mantra. We look at how `LeNat` computes, and we do the case
analysis which makes it get off its arse.

Fourthly, notice the missing cases in `transitive`. Agda asks us for no work
for `transitive leNat (su x) ze z xy yz` because it can see that `xy : Zero`.


```agda
Extra : Nat -> Nat -> Set
Extra x z = Nat >< \ y -> x +N y ~ z
```

```agda
extra : forall x z -> Splat (LeNat x z) -> Extra x z
extra x z xz = {!!}
```

```agda
record Monoid (X : Set) : Set where
  field
    neutral : X
    compose : X -> X -> X
    compose-neutral-thing : forall x -> compose neutral x ~ x
    compose-thing-neutral : forall x -> compose x neutral ~ x
    compose-compose       : forall x y z ->
      compose (compose x y) z ~ compose x (compose y z)
```

```agda
module _ where
  open Monoid
  
  monoid+N : Monoid Nat
  monoid+N = {!!}
```

```agda
record Monotone {X}{R : X -> X -> Splatoid}(PR : Preorder R)
                {Y}{S : Y -> Y -> Splatoid}(PS : Preorder S)
  : Set where
  field
    transport : X -> Y
    respect   : forall x0 x1 -> Splat (R            x0             x1 )
                             -> Splat (S (transport x0) (transport x1))
```

```agda
module _ where
  open Monotone

  monotone-x+N : Nat -> Monotone leNat leNat
  monotone-x+N x = {!!}
```
