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
record TreeDesign : Set1 where
  field
    PayloadSort   : Set
    RecursiveSort : Set
    Constructor   : RecursiveSort -> Datoid
    ConArguments  : forall {i} -> Data (Constructor i)
                               -> TDesc (PayloadSort + RecursiveSort)
```

We fix a type of *payload* sorts and a type of recursive sorts.
For each recursive sort, we have a datoid of its constructors.
For each constructor, we know the tuple of its components, which
are either payload or recursive.

Let us now tie the recursive knot. To build a tree, pick a
constructor and fill in the associated tuple.

```agda
module _ (D : TreeDesign) where

 open TreeDesign D

 data Tree (X : PayloadSort -> Set)(i : RecursiveSort) : Set where
   _$_ : (c : Data (Constructor i))
      -> Tuple (X <?> Tree X) (ConArguments c)
      -> Tree X i

 infix 1 _$_
```

Now let us show that if the payload inhabits datoids, so do trees.

```agda
 module _ (X : PayloadSort -> Datoid) where
 
  DatTree : RecursiveSort -> Datoid
  tupEq? : (T : TDesc (PayloadSort + RecursiveSort)) ->
           Dec~ (Tuple ((X - Data) <?> Tree (X - Data)) T)
  Data (DatTree i) = Tree (X - Data) i
  eq? (DatTree i) (c $ s) (d $ t) with eq? (Constructor _) c d
  eq? (DatTree i) (c $ s) (d $ t)  | inl n = inl \ { r~ -> n r~}
  eq? (DatTree i) (c $ s) (.c $ t) | inr r~
    with tupEq? (ConArguments c) s t
  eq? (DatTree i) (c $ s) (.c $ t)  | inr r~ | inl n
    = inl \ { r~ -> n r~ }
  eq? (DatTree i) (c $ s) (.c $ .s) | inr r~ | inr r~ = inr r~

  tupEq? (# inl j) x0 x1 = eq? (X j) x0 x1
  tupEq? (# inr i) t0 t1 = eq? (DatTree i) t0 t1
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
