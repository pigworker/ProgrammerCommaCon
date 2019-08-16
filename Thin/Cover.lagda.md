# Thinning Coverings

```agda
module Thin.Cover where

open import Lib.Bwd
open import Lib.Sigma
open import Lib.Pi
open import Lib.Equality
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
 Coproduct : forall {ga ze de : Bwd X}(th : ga <= ze)(ph : de <= ze) -> Set
 Coproduct {ga}{ze}{de} th ph =
         (_ >< \ ze' -> ga <= ze' * ze' <= ze * de <= ze')
         >< \ { (_ , th' , ps , ph') ->
         [ th' - ps ]~ th * th' /u\ ph' * [ ph' - ps ]~ ph }

 _/+\_ : forall {ga ze de : Bwd X}(th : ga <= ze)(ph : de <= ze) ->
         Coproduct th ph
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

 module _ {F G : Bwd X -> Set} where

  data Pair {ga} : F :^ ga -> G :^ ga -> (F /*\ G) :^ ga -> Set
    where
    pair : forall {de0}(f : F de0){th0 : de0 <= ga}
                  {de1}(g : G de1){th1 : de1 <= ga}
                  (c : Coproduct th0 th1) ->
           let (! ph0 , ps , ph1) , v0 , u , v1 = c
           in  Pair (f ^ th0) (g ^ th1) (rp (f ^ ph0) (g ^ ph1) u ^ ps)

  mkPair : forall {ga}(f : F :^ ga)(g : G :^ ga) -> < Pair f g >
  mkPair (f ^ th) (g ^ ph) = ! pair f g (th /+\ ph)

 _/,\_ : forall {F G : Bwd X -> Set} ->
         [ (F :^_) -:> (G :^_) -:> ((F /*\ G) :^_) ]
 f /,\ g = fst (mkPair f g)
```

```agda
 copU : forall {ga ze de : Bwd X}{th : ga <= ze}{ph : de <= ze} ->
        {ze0 : Bwd X}{th0 : ga <= ze0}{ph0 : de <= ze0}{ps0 : ze0 <= ze} ->
        [ th0 - ps0 ]~ th -> [ ph0 - ps0 ]~ ph ->
        (c : Coproduct th ph) -> let (_ , th' , ps' , ph') , v , w = c
        in 

           <([ th' -_]~ th0) :*
            ([_- ps0 ]~ ps') :*
            ([ ph' -_]~ ph0)>
 copU (v0 -^ x) (v1 -^ .x) (! w0 -^, .x , () , w1 -^, .x)
 copU (v0 -^, x) (v1 -^, .x) (! w0 -^, .x , () , w1 -^, .x)
 copU (v0 -^ x) (v1 -^ .x) (! w0 -^ .x , u , w1 -^ .x)
   with copU v0 v1 (! w0 , u , w1)
 ... | ! t0 , t1 , t2 = ! t0 , t1 -^ x , t2
 copU (v0 -^, x) (v1 -^, .x) (! w0 -^ .x , u , w1 -^ .x)
   with copU v0 v1 (! w0 , u , w1)
 ... | ! t0 , t1 , t2 = ! t0 -^ x , t1 -^, x , t2 -^ x
 copU (v0 -^, x) (v1 -, .x) (! w0 -^, .x , u -^, .x , w1 -, .x)
   with copU v0 v1 (! w0 , u , w1)
 ... | ! t0 , t1 , t2 = ! t0 -^, x , t1 -, x , t2 -, x
 copU (v0 -, x) (v1 -^, .x) (! w0 -, .x , u -,^ .x , w1 -^, .x)
   with copU v0 v1 (! w0 , u , w1)
 ... | ! t0 , t1 , t2 = ! t0 -, x , t1 -, x , t2 -^, x
 copU (v0 -, x) (v1 -, .x) (! w0 -, x , u -, x , w1 -, x)
   with copU v0 v1 (! w0 , u , w1)
 ... | ! t0 , t1 , t2 = ! t0 -, x , t1 -, x , t2 -, x
 copU [] [] (! [] , [] , []) = ! [] , [] , []
```

```agda
 allRight : forall {ga} -> noth {ga = ga} /u\ io
 allRight {[]} = []
 allRight {ga -, x} = allRight {ga} -^, x

 isAllRight : forall {de ze}{th : [] <= ze}{ph : de <= ze}(u : th /u\ ph)
   -> (de ~ ze) >< \ { r~ -> ph ~ io }
 isAllRight (u -^, x) with isAllRight u
 ... | r~ , r~ = r~ , r~
 isAllRight [] = r~ , r~
```

```agda
 swapCover : forall {ga ze de}{th : ga <= ze}{ph : de <= ze} -> th /u\ ph -> ph /u\ th
 swapCover (u -^, x) = swapCover u -,^ x
 swapCover (u -,^ x) = swapCover u -^, x
 swapCover (u -, x)  = swapCover u -, x
 swapCover []        = []
```


```agda
 allLeft : forall {ga} -> io /u\ noth {ga = ga}
 allLeft = swapCover allRight

 isAllLeft : forall {ga ze}{th : ga <= ze}{ph : [] <= ze}(u : th /u\ ph)
   -> (ga ~ ze) >< \ { r~ -> th ~ io }
 isAllLeft u with isAllRight (swapCover u)
 ... | r~ , r~ = r~ , r~
```
