# Natural Numbers

```agda
module Lib.Nat where

open import Lib.Sum
open import Lib.Equality
open import Lib.Datoid
```

```agda
data Nat : Set where
  ze : Nat
  su : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

NatD : Datoid
Data NatD = Nat
eq? NatD ze     ze               = inr r~
eq? NatD ze     (su y)           = inl \ ()
eq? NatD (su x) ze               = inl \ ()
eq? NatD (su x) (su y)  with eq? NatD x y
eq? NatD (su x) (su y)  | inl n  = inl \ { r~ -> n r~ }
eq? NatD (su x) (su .x) | inr r~ = inr r~
```
