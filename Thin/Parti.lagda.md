```agda
module Thin.Parti where

open import Lib.Splatoid
open import Lib.Bwd
open import Lib.Sigma
open import Thin.Thin
open import Thin.Triangle
open import Thin.Cover
open import Thin.Pullback
```

```agda
module _ {X : Set} where

 record _<-[_]->_ (ga ze de : Bwd X) : Set where
   field
     lpart : ga <= ze
     rpart : de <= ze
     lrcov : lpart /u\ rpart
     lrdis : Disjoint lpart rpart
 open _<-[_]->_ public
```

```agda
 allRightParti : forall {de} -> [] <-[ de ]-> de
 lpart (allRightParti {de}) = noth
 rpart (allRightParti {de}) = io
 lrcov (allRightParti {de}) = allRight
 lrdis (allRightParti {de}) = noth-pull _
```

```agda
 swapParti : forall {ga ze de} -> ga <-[ ze ]-> de -> de <-[ ze ]-> ga
 lpart (swapParti p) = rpart p
 rpart (swapParti p) = lpart p
 lrcov (swapParti p) = swapCover (lrcov p)
 lrdis (swapParti p) = swapPullback (lrdis p)
```
