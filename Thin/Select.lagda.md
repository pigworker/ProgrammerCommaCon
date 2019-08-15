# Thinning acts by Selection

```agda
module Thin.Select where
open import Lib.Bwd
open import Thin.Thin
open import Thin.Triangle
```

```agda
module _ {X : Set} where

 infixr 21 _<?_
 _<?_ : forall {P : X -> Set}{ga de : Bwd X}
        (th : ga <= de) -> Env P de -> Env P ga
 (th -^ x) <? (pz -, _) = th <? pz
 (th -, x) <? (pz -, p) = th <? pz -, p
 []        <? []        = []
```
