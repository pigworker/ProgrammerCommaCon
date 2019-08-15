```agda
module Thin.Parti where

open import Lib.Splatoid
open import Lib.Bwd
open import Lib.Sigma
open import Lib.Equality
open import Thin.Thin
open import Thin.Triangle
open import Thin.Cover
open import Thin.Pullback
open import Thin.PullCover
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
 selParti : forall {ga de ze' ze : Bwd X}(ps : ze' <= ze) ->
   (p : ga <-[ ze ]-> de) ->
   (Bwd X * Bwd X) >< \ a -> let ga' , de' = a in
   ga' <-[ ze' ]-> de' >< \ p' ->
   (ga' <= ga * de' <= de) >< \ b -> let thl , thr = b in
   (Square (thl ^ lpart p) (lpart p' ^ ps) >< Pullback) *
   (Square (rpart p' ^ ps) (thr ^ rpart p) >< Pullback)
   
 selParti ps p with pullCover ps (lrcov p)
 ... | (ph0 ^ ps0 , ph1 ^ ps1)
     , ((th0 , v0 , w0), pl)
     , u'
     , ((th1 , w1 , v1), pr)
   with pullback ps0 ps1
 ... | ch0 ^ ch1 , (om , v0' , v1') , d
   with assoc03 (v0' ^ w0) | assoc03 (v1' ^ w1)
 ... | v2 ^ w2 | v3 ^ w3
   with splat splatTri (! w2) (! w3)
 ... | r~
   with assoc02 (v2 ^ v0) | assoc02 (v3 ^ v1)
 ... | v4 ^ w4 | v5 ^ w5
   with pullU (w4 ^ w5) (lrdis p)
 ... | [] , v6 , v7 , v8
   with noth~ ch0 noth | noth~ ch1 noth | noth~ om noth
 ... | r~ | r~ | r~
   with splat splatTri (! v0') (! noth- ps0)
      | splat splatTri (! v1') (! noth- ps1)
 ... | r~ | r~ = ! record
   { lpart = _
   ; rpart = _
   ; lrcov = u'
   ; lrdis = d
   } , ! (! pl) , ! pr
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
