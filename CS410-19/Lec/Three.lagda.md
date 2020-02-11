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

![A smol cat](pomeloSmol.jpg?raw=true)


```agda
module _ {X : Set}{R : X -> X -> Splatoid}(P : Preorder R) where
  open Preorder P
  open SmolCat
  open Splatoid

  PREORDER : SmolCat \ s t -> Splat (R s t)
  identity PREORDER = reflexive _
  compose PREORDER = transitive _ _ _
  compose-identity-arrow PREORDER f = splat (R _ _) _ _
  compose-arrow-identity PREORDER f = splat (R _ _) _ _
  compose-compose PREORDER f g h = splat (R _ _) _ _
```

```agda
module _ {X : Set}(M : Monoid X) where

  open Monoid M
  open SmolCat

  MONOID : SmolCat {One} \ _ _ -> X
  identity MONOID = neutral
  compose MONOID = Monoid.compose M
  compose-identity-arrow MONOID = compose-neutral-thing
  compose-arrow-identity MONOID = compose-thing-neutral
  compose-compose MONOID = Monoid.compose-compose M
```

```agda
module _ (X : Set) where

  open SmolCat

  DISCRETE : SmolCat {X} _~_
  identity DISCRETE = r~
  compose DISCRETE r~ r~ = r~
  compose-identity-arrow DISCRETE r~ = r~
  compose-arrow-identity DISCRETE r~ = r~
  compose-compose DISCRETE r~ r~ r~ = r~
```

```agda
module _ {Obj : Set}{_=>_ : Obj -> Obj -> Set}(C : SmolCat _=>_) where

  open SmolCat

  OP : SmolCat \ S T -> T => S
  identity OP = identity C
  compose OP f g = compose C g f
  compose-identity-arrow OP = compose-arrow-identity C
  compose-arrow-identity OP = compose-identity-arrow C
  compose-compose OP f g h = (compose-compose C h g f) ~o
```

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

```agda
module _ where
  open _-SmolCat>_
  open Preorder leNat
  open Monoid monoid+N

  EXTRA : PREORDER leNat -SmolCat> MONOID monoid+N
  Map EXTRA = _
  map EXTRA {x} {y} xy = fst (extra x y xy)
  map-identity EXTRA {ze} = r~
  map-identity EXTRA {su x} = map-identity EXTRA {x}
  map-compose EXTRA {ze} {ze} {z} xy yz = r~
  map-compose EXTRA {ze} {su y} {su z} xy yz = su $~ map-compose EXTRA {ze} {y} {z} xy yz
  map-compose EXTRA {su x} {su y} {su z} xy yz =  map-compose EXTRA {x} {y} {z} xy yz
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

  triEq : forall {X}{f g : From X}{p q : Triangle X f g} ->
          fst p ~ fst q ->
          p ~ q
  triEq {p = f , r~} {q = .f , r~} r~ = r~

  module _ (X : Obj) where

    _-FROM_ : SmolCat (Triangle X)
    identity _-FROM_ {Y , f} =
      identity C {Y} , compose-arrow-identity C f
    compose _-FROM_ {R , f} {S , g} {T , h} (fg , q0) (gh , q1) =
      compose C fg gh , 
        compose C f (compose C fg gh)
          < compose-compose C _ _ _ ]~
        compose C (compose C f fg) gh
          ~[ (\ a -> compose C a gh) $~ q0 >
        compose C g gh
          ~[ q1 >
        h
          [QED]
    compose-identity-arrow _-FROM_ f = triEq (compose-identity-arrow C _)
    compose-arrow-identity _-FROM_ f = triEq (compose-arrow-identity C _)
    compose-compose _-FROM_ f g h = triEq (compose-compose C _ _ _)
```

What is `C -TO Y`?

```agda
module _ {Obj : Set}{_=>_ : Obj -> Obj -> Set}(C : SmolCat _=>_)(Y : Obj) where
  _-TO_ : SmolCat (Triangle (OP C) Y)
  _-TO_ = OP C -FROM Y
```

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
         -- why not? forall {T} -> map (identity {T}) ~ id -- \ x -> x
      map-compose  : forall {R S T}(f : R => S)(g : S => T)(r : Map R)
                  -> (map f - map g) r ~ map (compose f g) r
```

```agda
module _ (X : Set) where
  open _->Set

  TUPLE : OP (PREORDER leNat) ->Set
  Map TUPLE ze = One
  Map TUPLE (su n) = X * Map TUPLE n
  map TUPLE {m} {ze} mn xs = <>
  map TUPLE {su m} {su n} mn (x , xs) = x , map TUPLE {m} {n} mn xs
  map-identity TUPLE {ze} xs = r~
  map-identity TUPLE {su n} (x , xs) = (x ,_) $~ map-identity TUPLE {n} xs
  map-compose TUPLE {m} {n} {ze} mn np xs = r~
  map-compose TUPLE {su m} {su n} {su p} mn np (x , xs) =
    (x ,_) $~ map-compose TUPLE {m} {n} {p} mn np xs
```
