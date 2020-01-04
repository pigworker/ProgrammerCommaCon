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

 data _/x\_ : forall {ga ze de : Bwd X}
              (th : ga <= ze)(ph : de <= ze) -> Set where
   _-^,_ : forall {ga ze de}{th : ga <= ze}{ph : de <= ze} ->
           th /x\ ph -> forall x -> th -^ x /x\ ph -, x
   _-,^_ : forall {ga ze de}{th : ga <= ze}{ph : de <= ze} ->
           th /x\ ph -> forall x -> th -, x /x\ ph -^ x
   []    : [] /x\ []

 infix 15 _/x\_
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
 partiL : forall {ga ze de}(p : ga <-[ ze ]-> de) b ->
   (ga -, b) <-[ ze -, b ]-> de
 lpart (partiL p b) = _
 rpart (partiL p b) = _
 lrcov (partiL record { lrcov = u } b) = u -,^ b
 lrdis (partiL record { lrdis = d } b) = d -,^ b

 partiR : forall {ga ze de}(p : ga <-[ ze ]-> de) b ->
   ga <-[ ze -, b ]-> (de -, b)
 lpart (partiR p b) = _
 rpart (partiR p b) = _
 lrcov (partiR record { lrcov = u } b) = u -^, b
 lrdis (partiR record { lrdis = d } b) = d -^, b

 parti[] : [] <-[ [] ]-> []
 lpart parti[] = _
 rpart parti[] = _
 lrcov parti[] = []
 lrdis parti[] = []

 data PartiV : forall {ga ze de} -> ga <-[ ze ]-> de -> Set
   where
   [] : PartiV parti[]
   _-,^_ : forall {ga ze de}{p : ga <-[ ze ]-> de}
           (_ : PartiV p) b -> PartiV (partiL p b)
   _-^,_ : forall {ga ze de}{p : ga <-[ ze ]-> de}
           (_ : PartiV p) b -> PartiV (partiR p b)

 partiV : forall {ga de ze}(p : ga <-[ ze ]-> de) -> PartiV p
 partiV record { lrcov = (u -^, b) ; lrdis = (d -^, .b) } =
   partiV record { lrcov = u ; lrdis = d } -^, b
 partiV record { lrcov = (u -,^ b) ; lrdis = (d -,^ .b) } =
   partiV record { lrcov = u ; lrdis = d } -,^ b
 partiV record { lrcov = (u -, b) ; lrdis = () }
 partiV record { lrcov = [] ; lrdis = [] } = []
```


```agda
 selParti : forall {ga de ze' ze : Bwd X}(ps : ze' <= ze) ->
   (p : ga <-[ ze ]-> de) ->
   (Bwd X * Bwd X) >< \ a -> let ga' , de' = a in
   ga' <-[ ze' ]-> de' >< \ p' ->
   (ga' <= ga * de' <= de) >< \ b -> let thl , thr = b in
   (Square (thl ^ lpart p) (lpart p' ^ ps) >< Pullback) *
   (Square (rpart p' ^ ps) (thr ^ rpart p) >< Pullback)

 selParti ps p
   with    (ph0 ^ ps0 , ph1 ^ ps1) , ((th0 , v0 , w0), pl)
         , u' , ((th1 , w1 , v1), pr)
         <- pullCover ps (lrcov p)
   = record { lrcov = u' ; lrdis = d } ^ (! (! pl) , ! pr)
   where
   d : _
   d with ch0 ^ ch1 , (om , v0' , v1') , d <- pullback ps0 ps1
     | v2 ^ w2 <- assoc03 (v0' ^ w0)
     | v3 ^ w3 <- assoc03 (v1' ^ w1)
     | r~ <- splat splatTri (! w2) (! w3)
     | v4 ^ w4 <- assoc02 (v2 ^ v0)
     | v5 ^ w5 <- assoc02 (v3 ^ v1)
     | [] , v6 , v7 , v8 <- pullU (w4 ^ w5) (lrdis p)
     | r~ , r~ , r~ <- noth~ ch0 noth , noth~ ch1 noth , noth~ om noth
     | r~ , r~ <- splat splatTri (! v0') (! noth- ps0)
                , splat splatTri (! v1') (! noth- ps1)
     = d
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
