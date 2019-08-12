# A Universe of DeBruijn Syntaxes

```agda
module Meta19.DeBruijn where

open import Lib.One
open import Lib.Sigma
open import Lib.Bwd
open import Thin.Thin
```

```agda
record TermDesign : Set1 where
```

```agda
module _ (D : TermDesign) where

 open TermDesign D

 data Term : Set where
```
