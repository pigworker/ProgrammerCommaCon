# Splatoid

```agda
module Lib.Splatoid where

open import Agda.Primitive

open import Lib.Zero 
open import Lib.One
open import Lib.Equality
open import Lib.Sigma
```

A *splatoid* is a type whose inhabitants convey at most zero bits. That is,
they are inhabited uniquely, if at all.

```agda
record Splatoid {l} : Set (lsuc l) where
  constructor Splatter
  field
    Splat : Set l
    splat : (x y : Splat) -> x ~ y
open Splatoid public
```

The `Zero` and `One` types are both splatoids, but for different reasons.

```agda
SplatZero : forall {l} -> Splatoid {l}
Splat SplatZero = Zero
splat SplatZero () _

SplatOne : forall {l} -> Splatoid {l}
Splat SplatOne = One
splat SplatOne x y = r~
```

(I have used *copattern* style to construct these records, field by field.)

(Note that I have changed the naming convention so that what comes out is
on the left.)

Controversially, every equality type is also a splatoid.

```agda
module _ {l}{X : Set l}(x : X) where

 SplatEq : X -> Splatoid
 Splat (SplatEq y) = x ~ y
 splat (SplatEq .x) r~ r~ = r~
```

It's controversial, because *uniqueness of identity proofs* is
validated by dependent pattern matching, but refuted by some models of
dependent type theory, notably the *groupoid* model of [Martin Hofmann
and Thomas
Streicher](https://www.tcs.ifi.lmu.de/publikationen/HofmannStreicher1994).

It is, however, uncontroversial to contract singletons.

```agda
 SplatSing : Splatoid
 Splat SplatSing = X >< \ x' -> x' ~ x
 splat SplatSing (.x , r~) (.x , r~) = r~
```
