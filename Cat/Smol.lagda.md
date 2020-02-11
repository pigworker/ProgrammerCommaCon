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

Three candidate coping strategies:

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

Every category has a *dual*.

```agda
module _ {Obj : Set}{_=>_ : Obj -> Obj -> Set}(C : SmolCat _=>_) where

  open SmolCat

  OP : SmolCat \ S T -> T => S
  identity OP    = identity C
  compose OP f g = compose C g f
  compose-identity-arrow OP = compose-arrow-identity C
  compose-arrow-identity OP = compose-identity-arrow C
  compose-compose OP f g h  = (compose-compose C h g f) ~o
```


Functors between `SmolCat`s
---------------------------

We have a `Map` action on objects, and a `map` action on arrows.
The latter preserves identity and composition *intensionally*.

```agda
module _ {X : Set}{_=C>_ : X -> X -> Set}(C : SmolCat _=C>_)
         {Y : Set}{_=D>_ : Y -> Y -> Set}(D : SmolCat _=D>_)
  where
  open SmolCat

  record _-SmolCat>_ : Set where  -- functor
    field
      Map : X -> Y
      map : forall {S T}
         -> S =C> T -> Map S =D> Map T
      map-identity : forall {T}
                  -> map (identity C {T}) ~ identity D {Map T}
      map-compose  : forall {R S T}(f : R =C> S)(g : S =C> T)
                  -> map (compose C f g) ~ compose D (map f) (map g)
```

Of course, as suggested by the notation, functors make perfectly
respectable arrows, between objects which are `SmolCat`s. We can
define the identity functor and functor composition. We obtain
the category of `SmolCat`s, but it is *not* itself a `SmolCat`
because its objects are large (even though its arrows are
small).


Extensional Interpretations of `SmolCat`s
-----------------------------------------

```agda
module _ {Obj : Set}{_=>_ : Obj -> Obj -> Set}(C : SmolCat _=>_) where
  open SmolCat C

  record _->Set : Set1 where
    field
      Map : Obj -> Set
      map : forall {S T}
         -> S => T -> Map S -> Map T
      map-identity : forall {T}(t : Map T)
                  -> map (identity {T}) t ~ t
      map-compose  : forall {R S T}(f : R => S)(g : S => T)(r : Map R)
                  -> (map f - map g) r ~ map (compose f g) r
```
