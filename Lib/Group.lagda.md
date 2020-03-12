```agda
module Lib.Group where

open import Lib.One
open import Lib.Two
open import Lib.Sigma
open import Lib.Sum
open import Lib.Equality
open import Lib.Datoid
```

```agda
record Group (X : Set) : Set where
  field
    one  : X
    inv  : X -> X
    mult : X -> X -> X
    one-mult  : forall x     -> mult one x ~ x
    inv-mult  : forall x     -> mult (inv x) x ~ one
    mult-mult : forall x y z -> mult (mult x y) z ~ mult x (mult y z)
  square-one : forall x -> mult x x ~ x -> x ~ one
  square-one x h = 
    x < one-mult x ]~
    mult one x < (\ y -> mult y x) $~ inv-mult x ]~
    mult (mult (inv x) x) x ~[ mult-mult (inv x) x x >
    mult (inv x) (mult x x) ~[ mult (inv x) $~ h >
    mult (inv x) x ~[ inv-mult x >
    one [QED]
  mult-inv : forall x -> mult x (inv x) ~ one
  mult-inv x = square-one (mult x (inv x))
    (mult (mult x (inv x)) (mult x (inv x)) ~[ mult-mult _ _ _ >
    mult x (mult (inv x) (mult x (inv x))) < mult x $~ mult-mult _ _ _ ]~
    mult x (mult (mult (inv x) x) (inv x)) ~[ (\ y -> mult x (mult y (inv x))) $~ inv-mult x >
    mult x (mult one (inv x)) ~[ mult x $~ one-mult (inv x) >
    mult x (inv x) [QED])
  mult-one : forall x -> mult x one ~ x
  mult-one x = 
    mult x one < mult x $~ inv-mult x ]~
    mult x (mult (inv x) x) < mult-mult _ _ _ ]~
    mult (mult x (inv x)) x ~[ (\ y -> mult y x) $~ mult-inv x >
    mult one x ~[ one-mult x >
    x [QED]
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

module _ {X : Set}(Plus : Monoid X)(Mult : Monoid X) where
  module PLUS where
    open Monoid Plus
    zero = neutral
    _+X_ = compose
  module MULT where
    open Monoid Mult
    one = neutral
    _*X_ = compose
  open PLUS
  open MULT
  record Rig : Set where
    field
      comm-plus : forall x y -> (x +X y) ~ (y +X x)
      zero-mult : forall x -> (zero *X x) ~ x
      plus-mult : forall x y z -> ((x +X y) *X z) ~ ((x *X z) +X (y *X z))
      mult-zero : forall x -> (x *X zero) ~ x
      mult-plus : forall x y z -> (x *X (y +X z)) ~ ((x *X y) +X (x *X z))

module _ {X : Datoid}(G : Group (Data X)) where
  open Group G
  open Monoid

  module ARGGH where
    lum lup : (One + Data X) -> (One + Data X) -> (One + Data X)
    lum (inr x) (inr y) = inr (mult x y)
    lum _ _ = inl <>

    lup (inr x) (inr y) with eq? X x y
    lup (inr x) (inr y) | ff , _ = inl <>
    lup (inr x) (inr y) | tt , _ = inr x
    lup _ _ = inl <>

  LiftMult LiftPlus : Monoid (One + Data X)
  neutral LiftMult = inr one
  compose LiftMult = ARGGH.lum
  compose-neutral-thing LiftMult (inl <>) = r~
  compose-neutral-thing LiftMult (inr y) = inr $~ one-mult y
  compose-thing-neutral LiftMult (inl <>) = r~
  compose-thing-neutral LiftMult (inr x)  = inr $~ mult-one x
  compose-compose LiftMult (inr x) (inr y) (inr z) = inr $~ mult-mult _ _ _
  compose-compose LiftMult (inl <>) y z = r~
  compose-compose LiftMult (inr x) (inl <>) z = r~
  compose-compose LiftMult (inr x) (inr y) (inl <>) = r~

  neutral LiftPlus = inl <>
  compose LiftPlus = ARGGH.lup
  compose-neutral-thing LiftPlus x = {!!}  -- n.g.h.
  compose-thing-neutral LiftPlus x = {!!}  -- n.g.h.
  compose-compose LiftPlus x y z = {!!}

   --- so what is it then?
```
