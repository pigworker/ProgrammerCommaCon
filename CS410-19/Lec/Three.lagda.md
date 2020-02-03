```agda
module CS410-19.Lec.Three where

open import Lib.One
open import Lib.Pi
open import Lib.Sigma
open import Lib.Nat
open import Lib.Equality
open import Lib.Splatoid
open import CS410-19.Lec.Two
```

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

```agda
module _ {X : Set}{R : X -> X -> Splatoid}(P : Preorder R) where
  open Preorder P
  open SmolCat
  open Splatoid

  PREORDER : SmolCat \ s t -> Splat (R s t)
  PREORDER = {!!}
```

```agda
module _ {X : Set}(M : Monoid X) where

  open Monoid M
  open SmolCat

  MONOID : SmolCat {One} \ _ _ -> X
  MONOID = {!!}
```

```agda
module _ (X : Set) where

  DISCRETE : SmolCat {X} _~_
  DISCRETE = {!!}
```

```agda
module _ {Obj : Set}{_=>_ : Obj -> Obj -> Set}(C : SmolCat _=>_) where

  OP : SmolCat \ S T -> T => S
  OP = {!!}
```

```agda
module _ {X : Set}{_=C>_ : X -> X -> Set}(C : SmolCat _=C>_)
         {Y : Set}{_=D>_ : Y -> Y -> Set}(D : SmolCat _=D>_)
  where
  open SmolCat

  record _-SmolCat>_ : Set where
    field
      Map : X -> Y
      map : forall {S T}
         -> S =C> T -> Map S =D> Map T
      map-identity : forall {T}
                  -> map (identity C {T}) ~ identity D {Map T}
      map-compose  : forall {R S T}(f : R =C> S)(g : S =C> T)
                  -> map (compose C f g) ~ compose D (map f) (map g)
```

```agda
module _ where
  open _-SmolCat>_
  open Preorder leNat
  open Monoid monoid+N
  
  EXTRA : PREORDER leNat -SmolCat> MONOID monoid+N
  Map EXTRA = _
  map EXTRA {x}{z} = extra x z - fst
  map-identity EXTRA {x} = {!!}
  map-compose EXTRA {x}{y}{z} = {!!}
```

```agda
module _ {Obj : Set}{_=>_ : Obj -> Obj -> Set}(C : SmolCat _=>_) where
  open SmolCat

  From : Obj -> Set
  From X = Obj >< (X =>_)
  Triangle : (X : Obj) -> From X -> From X -> Set
  Triangle X (Y , f) (Z , h) =
    (Y => Z) >< \ g ->
    compose C f g ~ h

  module _ (X : Obj) where

    _-FROM_ : SmolCat (Triangle X)
    _-FROM_ = {!!}
```

What is `C -TO Y`?

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

```agda
module _ (X : Set) where
  open _->Set

  TUPLE : OP (PREORDER leNat) ->Set
  TUPLE = {!!}
```
