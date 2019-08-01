# Splatoid

```agda
module Lib.Splatoid where

open import Agda.Primitive

open import Lib.Zero 
open import Lib.One
open import Lib.Equality
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
ZeroSplat : Splatoid
Splat ZeroSplat = Zero
splat ZeroSplat () _

OneSplat : Splatoid
Splat OneSplat = One
splat OneSplat x y = r~
```

(I have used *copattern* style to construct these records, field by field.)

Controversially, every equality type is also a splatoid.

```agda
EqSplat : forall {l}{X : Set l}(x y : X) -> Splatoid
Splat (EqSplat x y) = x ~ y
splat (EqSplat x y) r~ r~ = r~
```

It's controversial, because *uniqueness of identity proofs* is
validated by dependent pattern matching, but refuted by some models of
dependent type theory, notably the *groupoid* model of [Martin Hofmann
and Thomas
Streicher](https://www.tcs.ifi.lmu.de/publikationen/HofmannStreicher1994).

