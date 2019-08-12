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
data Args : Set where

Tuple : Args -> Set
```

```agda
record TermDesign : Set1 where
```

```agda
module _ (D : TermDesign) where

 open TermDesign D

 data Term : Set where
   var : Term
   _$_ : Term
```
