# A Universe of Ordered Data Structures

```agda
module Univ.Ordered where

open import Lib.Zero
open import Lib.One
open import Lib.Equality
open import Lib.Pi
open import Lib.Sigma
open import Lib.Sum
open import Lib.Splatoid
open import Lib.Datoid
open import Univ.Datoid
```

In this file, I refine our first-order universe to represent
*ordered* data structures.

I'll need some basic ingredients

## Numbers

We can code up lists by introducing the datoid of list constructors,
`nil` and `cons`. We then say that `nil` maps to an empty tuple and
`cons` maps to the pair of a head and a tail.

```agda
data NatCons : Set where
  ze : NatCons
  su : NatCons

NatC : Datoid
Data NatC = NatCons
eq? NatC ze ze = inr r~
eq? NatC ze su = inl \ ()
eq? NatC su ze = inl \ ()
eq? NatC su su = inr r~

Nat : Set
Nat = Tree {Zero}{One}
  (\ _ -> NatC)
  (\ { ze -> One'
     ; su -> One' *' # inr <>   -- gratuitous?
     })
  naughty
  <>

pattern zero = ze $ <>
pattern suc n = su $ <> , n
```


## 2,3-Trees

Now that we have natural numbers, we can obtain the type of
balanced 2,3-trees. Only leaves have height zero, but at greater
heights, we can have nodes with either two or three subtrees.

```agda
data T23Cons : Nat -> Set where
  leaf       : T23Cons zero
  two three  : forall {n} -> T23Cons (suc n)

T23C : Nat -> Datoid
Data (T23C n) = T23Cons n
eq? (T23C .zero) leaf leaf = inr r~
eq? (T23C .(suc _)) two two = inr r~
eq? (T23C .(suc _)) two three = inl \ ()
eq? (T23C .(suc _)) three two = inl \ ()
eq? (T23C .(suc _)) three three = inr r~

T23D : {n : Nat} -> Data (T23C n) -> TDesc (Zero + Nat)
T23D {zero}  leaf  = One'
T23D {suc n} two   = # inr n *' # inr n
T23D {suc n} three = # inr n *' # inr n *' # inr n
```

## The Proto-Interval

Lastly, let us define a funny little type whose values are
pairs of empty tuples. The motivation will appear, below.

```agda
IntvD : TDesc (Zero + One)
IntvD = One' *' One'
```

## How To Order

Now, fix a datoid of *keys*.

```agda
module _ (Key : Datoid)
 where
```

We may extend a type of keys to a type of *bounds* by gluing
on `bot`tom and `top` elements.

```agda
 data Bound : Set where
   bot : Bound
   val : Data Key -> Bound
   top : Bound
```

We can extend an ordering relation on keys to an ordering
relation on bounds.

```agda
 module _ (Le : Data Key * Data Key -> Splatoid)
  where

  LeB : Bound * Bound -> Splatoid
  LeB (bot   ,     _) = OneSplat
  LeB (val x , val y) = Le (x , y)
  LeB (_     ,   top) = OneSplat
  LeB (_     ,     _) = ZeroSplat
```

Now, let us construct the datoid of node data that fits a
given tuple structure, when we know lower and upper bounds
for the data. Crucially, every time we see a pair, we ask for
a key.


```agda
  Keys : forall {I} -> TDesc I -> Datoid
  Keys (S *' T)  = Keys S >D< \ _ -> Key >D< \ _ -> Keys T
  Keys (# i)     = SplatDat OneSplat
  Keys One'      = SplatDat OneSplat
```

Given this information, we can transform tuple types with
no payload to *bounded* tuple types which ask for ordering evidence
as payload at the leaves. The key for each pair is used to
bound the left component above and the right component below.

```agda
  tupRefine : forall {I}(T : TDesc (Zero + I))
    (lu : Bound * Bound) ->
    Data (Keys T) ->
    TDesc ((Bound * Bound) + (I * Bound * Bound))
  tupRefine (# inr i) lu <>                   = # inr (i , lu)
  tupRefine (S *' T) (l , u) (s , k , t) =
    tupRefine S (l , val k) s *' tupRefine T (val k , u) t
  tupRefine One'      lu <>                   = # inl lu
```

Putting the pieces together, we can take any no-payload
type descriptor and turn it into an ordered data structure.
We attach keys to the constructors and refine the argument
tuple. Ordering evidence is now the payload.

```agda
  module _
    {I : Set}
    (C : I -> Datoid)
    (F : {i : I} -> Data (C i) -> TDesc (Zero + I))
   where

   OTree : I * Bound * Bound -> Set
   OTree = Tree
     (\ { (i , lu) -> C i >D< \ c -> Keys (F c) })
     (\ { {i , lu} (c , ks) -> tupRefine (F c) lu ks })
     (LeB - Splat)
```

## Intervals

Our weird pair-of-ones type now becomes the type of a key
between bounds, carrying the evidence.

```agda
  Intv = OTree (\ _ -> SplatDat OneSplat) (\ _ -> IntvD)
  pattern intv lk k ku = (<> , <> , k , <>) $ (lk , ku)
```

## Ordered 2,3-Trees

Meanwhile, we can store keys in and impose the ordering invariant
on 2,3-Trees.

```agda
  OT23 = OTree T23C T23D
  pattern leaf0 lu = (leaf , <>) $ lu
  pattern node2 lk k ku = (two , <> , k , <>) $ (lk , ku)
  pattern node3 lj j jk k ku =
    (three , <> , j , <> , k , <>) $ (lj , jk , ku)
```

Now, suppose the order is total.
```agda
  module _ (owoto : ((x , y) : Data Key * Data Key) ->
                    Splat (Le (x , y)) + Splat (Le (y , x)))
   where
```

(That's &lsquo;one way or the other&rsquo;, for Debbie Harry.)

Let's write `insert`. We start from an interval and a tree
with common bounds. We preserve those bounds and end up either
with a tree the same height, or the components of a 2-node
one taller.

```agda
   insert : forall {n l u} ->
     Intv (<> , l , u) -> OT23 (n , l , u) ->
        ((Data Key >< \ k ->  OT23 (n , l , val k)
                           *  OT23 (n , val k , u)))
      + OT23 (n , l , u)

   pattern twoBig lk k ku = inl (k , lk , ku)
```

I didn't pull the &lsquo;twoBig&rsquo; type out of a hat. I
discovered what it had to be by writing the program. It turns
out that

1. inserting into a leaf makes a 2-node-one-taller

```agda
   insert (intv li i iu) (leaf0 lu) = twoBig (leaf0 li) i (leaf0 iu)
```

2. inserting into a 2-node at worst makes a 3-node 
```agda
   insert (intv li i iu) (node2 lk k ku) with owoto (i , k)
   insert (intv li i iu) (node2 lk k ku) | inl ik
     with insert (intv li i ik) lk
   ... | twoBig lm m mk  = inr (node3 lm m mk k ku)
   ... | inr lk'         = inr (node2 lk' k ku)
   insert (intv li i iu) (node2 lk k ku) | inr ki
     with insert (intv ki i iu) ku
   ... | twoBig km m mu  = inr (node3 lk k km m mu)
   ... | inr ku'         = inr (node2 lk k ku')
```

3. inserting into a 3-node at worst makes a 2-node-one-taller

```agda
   insert (intv li i iu) (node3 lj j jk k ku) with owoto (i , j)
   insert (intv li i iu) (node3 lj j jk k ku) | inl ij
     with insert (intv li i ij) lj
   ... | twoBig lm m mj  = twoBig (node2 lm m mj) j (node2 jk k ku)
   ... | inr lj'         = inr (node3 lj' j jk k ku)
   insert (intv li i iu) (node3 lj j jk k ku) | inr ji with owoto (i , k)
   insert (intv li i iu) (node3 lj j jk k ku) | inr ji | inl ik
     with insert (intv ji i ik) jk
   ... | twoBig jm m mk  = twoBig (node2 lj j jm) m (node2 mk k ku)
   ... | inr jk'         = inr (node3 lj j jk' k ku)
   insert (intv li i iu) (node3 lj j jk k ku) | inr ji | inr ki
     with insert (intv ki i iu) ku
   ... | twoBig km m mu  = twoBig (node2 lj j jk) k (node2 km m mu)
   ... | inr ku'         = inr (node3 lj j jk k ku')
```

