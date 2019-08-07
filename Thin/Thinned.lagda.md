# Thinned Things

```agda
module Thin.Thinned where

open import Lib.Sigma
open import Lib.Pi
open import Lib.Bwd
open import Thin.Thin
```

```agda
module _ {X : Set} where

 _:^_ : (Bwd X -> Set) -> (Bwd X -> Set)
 T :^ de = < T :* (_<= de) >
```

```agda
 Relevant : ((X -> Set) -> Bwd X -> Set) -> Set1
 Relevant F = forall {P} -> [ F P -:> Env P ]
```
