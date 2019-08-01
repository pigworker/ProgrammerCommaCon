# A Universe of Datoids

```agda
module Univ.Datoid where

open import Lib.One
open import Lib.Sigma
open import Lib.Pi
open import Lib.Equality
open import Lib.Sum
open import Lib.Datoid
```

Define a datatype of tuple structures with
places given sorts in `I`.

```agda
data TDesc (I : Set) : Set where
  #_   : I -> TDesc I
  _*'_ : TDesc I -> TDesc I -> TDesc I
  One' : TDesc I

infixr 5 _*'_
infix 6 #_

Tuple : forall {I} -> (I -> Set) -> TDesc I -> Set
Tuple P (# i)     = P i
Tuple P (S *' T)  = Tuple P S * Tuple P T
Tuple P One'      = One
```

We can obtain a bunch of first order data structures
as follows.

```agda
module _ {J I : Set}
         (C : I -> Datoid)
         (F : {i : I} -> Data (C i) -> TDesc (J + I))
 where
```

We fix a type `J` of *payload* sorts and a type `I` of tree sorts.
For each tree sort, we have a datoid of its constructors.
For each constructor, we know the tuple of its components, which
are either payload or subtrees.

Let us now tie the recursive knot. To build a tree, pick a
constructor and fill in the associated tuple.

```agda
 data Tree (X : J -> Set)(i : I) : Set where
   _$_ : (c : Data (C i)) ->
         Tuple (X <?> Tree X) (F c) ->
         Tree X i

 infix 1 _$_
```

Now let us show that if the payload inhabits datoids, so do trees.

```agda
 module _ (X : J -> Datoid) where
 
  TreeDat : I -> Datoid
  tupEq? : (T : TDesc (J + I)) ->
           Dec~ (Tuple ((X - Data) <?> Tree (X - Data)) T)
  Data (TreeDat i) = Tree (X - Data) i
  eq? (TreeDat i) (c $ s) (d $ t) with eq? (C _) c d
  eq? (TreeDat i) (c $ s) (d $ t)  | inl n = inl \ { r~ -> n r~}
  eq? (TreeDat i) (c $ s) (.c $ t) | inr r~
    with tupEq? (F c) s t
  eq? (TreeDat i) (c $ s) (.c $ t)  | inr r~ | inl n
    = inl \ { r~ -> n r~ }
  eq? (TreeDat i) (c $ s) (.c $ .s) | inr r~ | inr r~ = inr r~

  tupEq? (# inl j) x0 x1 = eq? (X j) x0 x1
  tupEq? (# inr i) t0 t1 = eq? (TreeDat i) t0 t1
  tupEq? (S *' T) (s0 , t0) (s1 , t1)
    with tupEq? S s0 s1 | tupEq? T t0 t1
  tupEq? (S *' T) (s0 , t0) (s1 , t1) | inl n  | _
    = inl \ { r~ -> n r~ }
  tupEq? (S *' T) (s  , t0) (.s , t1) | inr r~ | inl n
    = inl \ { r~ -> n r~ }
  tupEq? (S *' T) (s  , t)  (.s , .t) | inr r~ | inr r~
    = inr r~
  tupEq? One' <> <> = inr r~
```
