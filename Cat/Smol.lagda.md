Small (Intensional) Categories
==============================

```agda
module Cat.Smol where

open import Lib.One
open import Lib.Pi
open import Lib.Sigma
open import Lib.Nat
open import Lib.Equality
open import Lib.Splatoid
```

![A smol cat](../CS410-19/Lec/pomeloSmol.jpg?raw=true)

The cat picture (thanks, Fred!) is for a moment of cheer before things get depressing.

Doing Category Theory in Type Theory often sounds like a better idea than it
is. There are at least three things which go wrong:

1. Size Misery: are the objects a Set or a Set1? are the arrows a Set or a Set1?
2. Propositional Equality Misery: equality for arrows in Sets-and-functions should be extensional, etc.
3. Definitional Equality Misery: when you do not get, e.g., associativity of append for free, managing the kinds of coherence you need is going to get rather bureaucratic rather quickly.

Three candidate coping strategis:

* *heart* Spend your life trying to make type theory more categorical. There are people who do this and I'm with them. The situation is improving but these things take time.
* *brain* Tell lies. Switch on "Type in Type", postulate extensionality. Get to the flavour of the ideas all the sooner.
* *bowel* Struggle and strain to tell a more carefully managed story about the truths which are available.

I'm afraid, today, we're going with *bowel*.

```agda
record SmolCat {Obj : Set}(_=>_ : Obj -> Obj -> Set) : Set where
  field

    identity : forall {T}
      -> T => T

    compose  : forall {R S T}
      -> R => S -> S => T -> R => T

    compose-identity-arrow : forall {S T}(f : S => T)
      -> compose identity f ~ f

    compose-arrow-identity : forall {S T}(f : S => T)
      -> compose f identity ~ f

    compose-compose : forall {R S T U}(f : R => S)(g : S => T)(h : T => U)
      -> compose (compose f g) h ~ compose f (compose g h)
```

Here, we have small objects, small arrows, and equality of arrows
is *intensional*. In particular, Sets-and-functions is *not* a `SmolCat`.

We can identify some special cases. Preorders are, famously, categories
with boring arrows.

```agda
Preorder : forall {X : Set} -> (X -> X -> Splatoid) -> Set
Preorder R = SmolCat \ x y -> Splat (R x y)
```

Note that the proofs of the laws for a preorder will always be trivial.

```agda
module _
  {X}(R : X -> X -> Splatoid)
  (reflexivity  : forall {x} -> Splat (R x x))
  (transitivity : forall {x y z} -> Splat (R x y) -> Splat (R y z) -> Splat (R x z))
  where
  open SmolCat
  
  preorder : Preorder R
  identity preorder = reflexivity
  compose  preorder = transitivity
  compose-identity-arrow preorder _ = splat (R _ _) _ _
  compose-arrow-identity preorder _ = splat (R _ _) _ _
  compose-compose preorder _ _ _    = splat (R _ _) _ _
```

In particular, we have discrete categories.

```agda
module _ where
  open SmolCat
  
  Discrete : (X : Set) -> Preorder {X} SplatEq
  Discrete X = preorder SplatEq r~ _-~-_
```

Meanwhile, monoids are one-object categories.

```agda
Monoid : Set -> Set
Monoid X = SmolCat {One} \ _ _ -> X
```

