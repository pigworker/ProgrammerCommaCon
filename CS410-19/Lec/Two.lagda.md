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

```agda
LeNat : Nat -> Nat -> Splatoid
LeNat ze     y      = SplatOne
LeNat (su x) ze     = SplatZero
LeNat (su x) (su y) = LeNat x y
```

```agda
record Preorder {X : Set}(R : X -> X -> Splatoid) : Set where
  field
    reflexive  : forall x -> Splat (R x x)
    transitive : forall x y z
              -> Splat (R x y) -> Splat (R y z) -> Splat (R x z)
```

```agda
module _ where  -- Conor, remember to say something about what this is for

  open Preorder

  leNat : Preorder LeNat
  reflexive leNat ze = <>
  reflexive leNat (su x) = reflexive leNat x
  transitive leNat ze y z xy yz = <>
  transitive leNat (su x) (su y) (su z) xy yz = transitive leNat x y z xy yz
```

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
