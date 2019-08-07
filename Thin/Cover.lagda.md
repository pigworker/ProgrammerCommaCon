# Thinning Coverings

```agda
module Thin.Cover where

open import Lib.Bwd
open import Lib.Sigma
open import Thin.Thin
open import Thin.Triangle
open import Thin.Thinned
```

```agda
module _ {X : Set} where

 data _/u\_ : forall {ga ze de : Bwd X}
              (th : ga <= ze)(ph : de <= ze) -> Set where
   _-^,_ : forall {ga ze de}{th : ga <= ze}{ph : de <= ze} ->
           th /u\ ph -> forall x -> th -^ x /u\ ph -, x
   _-,^_ : forall {ga ze de}{th : ga <= ze}{ph : de <= ze} ->
           th /u\ ph -> forall x -> th -, x /u\ ph -^ x
   _-,_  : forall {ga ze de}{th : ga <= ze}{ph : de <= ze} ->
           th /u\ ph -> forall x -> th -, x /u\ ph -, x
   []    : [] /u\ []

 infix 15 _/u\_
 infixr 20 _-,^_
```

```agda
 _/+\_ : forall {ga ze de : Bwd X}(th : ga <= ze)(ph : de <= ze) ->
         (_ >< \ ze' -> ga <= ze' * ze' <= ze * de <= ze')
         >< \ { (_ , th' , ps , ph') ->
         [ th' - ps ]~ th * th' /u\ ph' * [ ph' - ps ]~ ph }
 (th -^ x) /+\ (ph -^ .x) =
   let ! v , u , w = th /+\ ph in ! v -^ x  , u       , w -^ x
 (th -^ x) /+\ (ph -, .x) =
   let ! v , u , w = th /+\ ph in ! v -^, x , u -^, x , w -, x
 (th -, x) /+\ (ph -^ .x) =
   let ! v , u , w = th /+\ ph in ! v -, x  , u -,^ x , w -^, x
 (th -, x) /+\ (ph -, .x) =
   let ! v , u , w = th /+\ ph in ! v -, x  , u -, x  , w -, x
 []        /+\ []         =       ! []      , []      , []
```

```agda
 merge : {ga ze de : Bwd X}{th : ga <= ze}{ph : de <= ze}{P : X -> Set} ->
         Env P ga -> th /u\ ph -> Env P de -> Env P ze
 merge lz        (u -^, x) (rz -, p) = merge lz u rz -, p
 merge (lz -, p) (u -,^ x) rz        = merge lz u rz -, p
 merge (lz -, p) (u -, x)  (rz -, _) = merge lz u rz -, p
 merge []        []        []        = []
```

```agda
 module _ (F G : Bwd X -> Set) where

  record _/*\_ (ga : Bwd X) : Set where
    constructor rp
    field
      outl    : F :^ ga
      outr    : G :^ ga
      cover   : snd (snd outl) /u\ snd (snd outr)
```
