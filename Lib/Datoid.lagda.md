# Datoid

```agda
module Lib.Datoid where

open import Lib.Sum
open import Lib.Sigma
open import Lib.Equality
open import Lib.Splatoid
```

A datoid is a `Set` with decidable equality.

```agda
Dec~ : Set -> Set
Dec~ X = (x y : X) -> Dec (x ~ y)

record Datoid : Set1 where
  constructor Datter
  field
    Data : Set
    eq?  : Dec~ Data
open Datoid public
```

## Datoids by Injection

```agda
module _ (Y : Datoid)
         {X : Set}(i : X `-> Data Y)
           
 where

 InjDat : Datoid
 Data InjDat = X
 eq? InjDat x0 x1 with eq? Y (inj i x0) (inj i x1)
 eq? InjDat x0 x1 | inl n = inl \ q -> n (inj i $~ q)
 eq? InjDat x0 x1 | inr q = inr (injective i x0 x1 q)
```


## A Splatoid is a Datoid

```agda
SplatDat : Splatoid -> Datoid
Data (SplatDat X) = Splat X
eq?  (SplatDat X) _ _ = inr (splat X _ _)
```


## Closure under Pairing

```agda
_>D<_ : (S : Datoid)(T : Data S -> Datoid) -> Datoid
Data (S >D< T) = Data S >< \ s -> Data (T s)
eq?  (S >D< T) (s0 , t0) (s1 , t1) with eq? S s0 s1
eq? (S >D< T) (s0 , t0) (s1 , t1) | inl n = inl \ { r~ -> n r~ }
eq? (S >D< T) (s , t0) (.s , t1) | inr r~ with eq? (T s) t0 t1
eq? (S >D< T) (s , t0) (.s , t1) | inr r~ | inl n = inl \ { r~ -> n r~ }
eq? (S >D< T) (s , t0) (.s , .t0) | inr r~ | inr r~ = inr r~
```
