Ornaments on Datatype Descriptions
==================================

```agda
module CS410-19.Lec.Nine where

open import Agda.Primitive -- we'll need universe levels

open import Lib.Zero
open import Lib.One
open import Lib.Two
open import Lib.Equality
open import Lib.Bwd
open import Lib.Sigma
open import Lib.Sum
open import Lib.Pi
open import Lib.Nat
open import Cat.Setoid
```

Descriptions of first-order data.

```agda
module _ (I : Set) where

  data Desc : Set1 where  -- `Desc`ription of datatypes
    `V     : I -> Desc
    `0 `1  : Desc
    _`*_   : Desc -> Desc -> Desc
    _`><_  : (S : Set)(T : S -> Desc) -> Desc
```

Action on objects:

```agda
[[_]]0 : forall {I : Set}(D : Desc I) -> (I -> Set) -> Set
[[ `V i    ]]0 X = X i
[[ `0      ]]0 X = Zero
[[ `1      ]]0 X = One
[[ D `* E  ]]0 X = [[ D ]]0 X * [[ E ]]0 X
[[ S `>< T ]]0 X = S >< \ s -> [[ T s ]]0 X
```

Action on arrows:

```agda
[[_]]1 : forall {I : Set}(D : Desc I){X Y : I -> Set}
      -> [ X -:> Y ] -> [[ D ]]0 X -> [[ D ]]0 Y
[[ `V i    ]]1 f x  = f x
[[ `1      ]]1 f <> = <>
[[ D `* E  ]]1 f (xd , xe) = ([[ D ]]1 f xd) , ([[ E ]]1 f xe)
[[ S `>< T ]]1 f (s , xt)  = s , [[ T s ]]1 f xt
```

Simplified data: no "payload", just recursive substructures.

```agda
module _ {I : Set}          -- what indexes nodes?
         (F : I -> Desc I)  -- what is the node structure for each index?
  where
  
  data Data (i : I)           -- what is the index of the top node?
    : Set
    where
    con : [[ F i ]]0 Data -> Data i

  module _ {X : I -> Set}(alg : {i : I} -> [[ F i ]]0 X -> X i) where

    fold     : [ Data -:> X ]
    mapFold  : (D : Desc I) -> [[ D ]]0 Data -> [[ D ]]0 X
    fold (con ts) = alg (mapFold (F _) ts)
    mapFold (`V i)    t         = fold t
    mapFold `1        <>        = <>
    mapFold (D `* E)  (td , te) = mapFold D td , mapFold E te
    mapFold (S `>< T) (s , ts)  = s , mapFold (T s) ts
```

```agda
NatDesc : One {lzero} -> Desc One
NatDesc <> = Two `>< (`1 <2> `V <>)

Nat' : Set
Nat' = Data NatDesc <> where

ze' : Nat'
ze' = con (ff , <>)

su' : Nat' -> Nat'
su' n = con (tt , n)
```

```agda
module _ {I J : Set}(f : J -> I) where

  Inv : I -> Set
  Inv i = J >< \ j -> f j ~ i

  data Orn : Desc I -> Set1 where  -- ornaments of `Desc`riptions of datatypes
    `V     : {i : I}(j : Inv i) -> Orn (`V i)
    `0     : Orn `0
    `1     : Orn `1
    _`*_   : {S T : Desc I} -> Orn S -> Orn T -> Orn (S `* T)
    _`><_  : (S : Set){T : S -> Desc I}(O : (s : S) -> Orn (T s)) -> Orn (S `>< T)
    ins><  : {D : Desc I}(S : Set) -> (S -> Orn D) -> Orn D
    del><  : {S : Set}{T : S -> Desc I}(s : S) -> Orn (T s) -> Orn (S `>< T)

  orn : {D : Desc I} -> Orn D -> Desc J
  orn (`V (j , _)) = `V j
  orn `0 = `0
  orn `1 = `1
  orn (O `* P) = orn O `* orn P
  orn (S `>< T) = S `>< \ s -> orn (T s)
  orn (ins>< S T) = S `>< \ s -> orn (T s)
  orn (del>< s O) = orn O

  fog : {D : Desc I}(O : Orn D){X : I -> Set} ->
        [[ orn O ]]0 (f - X) -> [[ D ]]0 X
  fog (`V (j , r~)) x = x
  fog `1 <> = <>
  fog (O `* P) (xo , xp) = fog O xo , fog P xp
  fog (S `>< T) (s , xt) = s , fog (T s) xt
  fog (ins>< S T) (s , xt) = fog (T s) xt
  fog (del>< s O) xo = s , fog O xo
```

```agda
OrnData : {I : Set} -> (I -> Desc I) -> (J : Set) -> (J -> I) -> Set1
OrnData {I} F J f = (j : J) -> Orn f (F (f j))

DataO : {I : Set}(F : I -> Desc I){J : Set}{f : J -> I}(O : OrnData F J f) ->
  J -> Set
DataO F {f = f} O = Data (\ j -> orn f (O j))

datFog : {I : Set}(F : I -> Desc I){J : Set}{f : J -> I}(O : OrnData F J f) ->
  {j : J} -> DataO F O j -> Data F (f j)
datFog F {f = f} O =
  fold (\ j -> orn f (O j)) (\ {j} ts -> con (fog f (O j) ts))

Nat2List : Set -> OrnData NatDesc One _
Nat2List X <> = Two `>< \ { ff -> `1 ; tt -> ins>< X \ _ -> `V (<> , r~) }


```
