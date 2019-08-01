# Datoid

```agda
module Lib.Datoid where

open import Lib.Sum
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

 injDat : Datoid
 Data injDat = X
 eq? injDat x0 x1 with eq? Y (inj i x0) (inj i x1)
 eq? injDat x0 x1 | inl n = inl \ q -> n (inj i $~ q)
 eq? injDat x0 x1 | inr q = inr (injective i x0 x1 q)
```


## A Splatoid is a Datoid

```agda
splatDat : Splatoid -> Datoid
Data (splatDat X) = Splat X
eq?  (splatDat X) _ _ = inr (splat X _ _)
```
