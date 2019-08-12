# A Universe of DeBruijn Syntaxes

This is, to be frank, a bait-and-switch operation...

```agda
module Meta19.DeBruijn where

open import Lib.One
open import Lib.Sigma
open import Lib.Pi
open import Lib.Bwd
open import Lib.Datoid
open import Thin.Thin
```

```agda
data Args (I : Set) : Set where
  #    : I -> Args I
  One' : Args I
  _*'_ : Args I -> Args I -> Args I

Tuple : {I : Set} -> (I -> Set) -> Args I -> Set
Tuple X (# i)    = X i
Tuple X One'     = One
Tuple X (S *' T) = Tuple X S * Tuple X T
```

```agda
record TermDesign : Set1 where
  field
    TermSort : Set
    Constructor : TermSort -> Datoid
    ConArgs : {i : TermSort} -> Data (Constructor i) -> Args TermSort
```

```agda
module _ (D : TermDesign) where

 open TermDesign D

 data Term (i : TermSort) : Set where
   var : Term i
   _$_ : (c : Data (Constructor i)) -> Tuple Term (ConArgs c) -> Term i
```
