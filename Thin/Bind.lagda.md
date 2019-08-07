# Relevance-Aware Binding

```agda
module Thin.Bind where

open import Lib.Pi
open import Lib.Bwd
open import Thin.Thin
open import Thin.Thinned
```

```agda
module _ {X : Set}
         where
```

```agda
 data _|-_  (x : X)(T : Bwd X -> Set)(ga : Bwd X) : Set where
   kk : T ga        -> (x |- T) ga
   ll : T (ga -, x) -> (x |- T) ga

```

```agda
 data Only (P : X -> Set) : Bwd X -> Set where
  only : forall {x} -> P x -> Only P ([] -, x)
```
