# The Relevance-Aware Universe

```agda
module Univ.Relevant where

open import Lib.Bwd
open import Lib.Sigma
open import Lib.Sum
open import Lib.Pi
open import Lib.Equality
open import Lib.Datoid
open import Lib.Star
open import Thin.Thin
open import Thin.Thinned
open import Thin.Triangle
open import Thin.Cover
open import Thin.Bind
```

```agda
data RDesc (X I : Set) : Set where
  #_ : I -> RDesc X I
  _*'_ : (S T : RDesc X I) -> RDesc X I
  _>'_ : X -> RDesc X I -> RDesc X I
```

```agda
module _ {X I : Set} where
 Tuple  :   (I -> Bwd X -> Set)
        ->  (RDesc X I -> Bwd X -> Set)
 Tuple R (# i) ga = R i ga
 Tuple R (S *' T) ga = (Tuple R S /*\ Tuple R T) ga
 Tuple R (x >' T) ga = (x |- Tuple R T) ga

 module TM (b2s : X -> I)
           (C : I -> Datoid)
           (F : {i : I} -> Data (C i) -> RDesc X I)
         where
  data Tm (i : I)(ga : Bwd X) : Set
  Term : RDesc X I -> Bwd X -> Set
  Term = Tuple Tm
  data Tm i ga where
    var : Only (b2s - (_~ i)) ga -> Term (# i) ga
    _$_ : (c : Data (C i)) -> Term (F c) ga -> Term (# i) ga
```

```agda
  data Jc : RDesc X I * Bwd X -> RDesc X I * Bwd X -> Set where
    rpl : forall {S T ga de ze} ->
          (th : ga <= ze) ->
          Term T de -> (ph : de <= ze) ->
          th /u\ ph ->
          Jc (S *' T , ze) (S , ga)
    rpr : forall {S T ga de ze} ->
          Term S ga -> (th : ga <= ze) ->
          (ph : de <= ze) ->
          th /u\ ph ->
          Jc (S *' T , ze) (T , de)
    ll  : forall {x T ze} -> Jc (x >' T , ze) (T , ze -, x)
    kk  : forall {x T ze} -> Jc (x >' T , ze) (T , ze)
    cu  : forall {i ze}(c : Data (C i)) -> Jc (# i , ze) (F c , ze)

  plug : forall {R ga H de} -> Jc (R , ga) (H , de) -> Term H de -> Term R ga
  plug (rpl th t ph u) h = rp (h ^ th) (t ^ ph) u
  plug (rpr s th ph u) h = rp (s ^ th) (h ^ ph) u
  plug ll h = ll h
  plug kk h = kk h
  plug (cu c) h = c $ h

  rootle : forall {R ga H de} ->
           Star Jc (R , ga) (H , de) -> Term H de -> Term R ga
  rootle [] h = h
  rootle (c ,- cs) h = plug c (rootle cs h)

  Has : forall T {ga}(t : Term T ga)(x : X) -> Set
  Has T {ga} t x
    = (Star Jc (T , ga) (# b2s x , [] -, x)) >< \ cs ->
      x <- ga
    * t ~ rootle cs (var (only r~))

  cHas : forall {R ga H de x h}
         (c : Jc (R , ga) (H , de)) -> x <- ga ->
         Has H h x -> Has R (plug c h) x
  cHas c j (cs , _ , r~) = c ,- cs , j , r~

  relevant : forall T {ga}(t : Term T ga) -> Env (Has T t) ga
  relevant (# .(b2s _)) (var (only r~)) = [] -, ([] , io , r~)
  relevant (# i) (c $ t) = purE (cHas (cu c)) $E envPos $E relevant (F c) t
  relevant (S *' T) (rp (s ^ th) (t ^ ph) u) =
    merge (purE (cHas (rpl th t ph u)) $E env (_-<= th) envPos $E relevant S s)
          u
          (purE (cHas (rpr s th ph u)) $E env (_-<= ph) envPos $E relevant T t)
  relevant (x >' T) (kk t) = purE (cHas kk) $E envPos $E relevant T t
  relevant (x >' T) (ll t) with relevant T t
  relevant (x >' T) (ll t) | csz -, _ = purE (cHas ll) $E envPos $E csz
```
