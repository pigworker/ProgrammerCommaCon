# Covers and Pullbacks

```agda
module Thin.PullCover where

open import Lib.Bwd
open import Lib.Sigma
open import Thin.Thin
open import Thin.Cover
open import Thin.Pullback
```

```agda
module _ {X : Set} where

 pullCover  :   forall {ga0 ga ga1 : Bwd X}{th0 : ga0 <= ga}{th1 : ga1 <= ga}
            ->  th0 /u\ th1 -> {de : Bwd X}(ph : de <= ga)
            ->  let ph0 ^ ps0 , _ = pullback th0 ph
                    ph1 ^ ps1 , _ = pullback th1 ph
                in  ps0 /u\ ps1
 pullCover (u -^, .x) (ph -^ x) = pullCover u ph
 pullCover (u -,^ .x) (ph -^ x) = pullCover u ph
 pullCover (u -, .x)  (ph -^ x) = pullCover u ph
 pullCover (u -^, .x) (ph -, x) = pullCover u ph -^, x
 pullCover (u -,^ .x) (ph -, x) = pullCover u ph -,^ x
 pullCover (u -, .x)  (ph -, x) = pullCover u ph -, x
 pullCover []         []        = []
```
