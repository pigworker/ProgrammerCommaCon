# Splatoids and Datoids

```agda
module SPLV.Tuesday where
```

(Since giving the lecture, I've refactored this content and added more
examples. I'll review what's changed.)


## Splatoids and Examples Thereof

```agda
open import Lib.Zero
open import Lib.One
open import Lib.Equality
open import Lib.Pi
open import Lib.Splatoid   -- go and look at it
```

The following are in my library but are worth seeing live.

```agda
{-(-}
SplatZero' SplatOne' : Splatoid
Splat SplatZero' = Zero
splat SplatZero' x y = naughty x
Splat SplatOne' = One
splat SplatOne' _ _ = r~
{-)-}
```

(I changed around the order of words in my naming convention to be more
&lsquo;diagrammatic&rsquo;.)

Add this to the library. (I just did!)

```agda
open import Lib.Sigma   -- also worth a look
{-(-}
module _ {l}{X : Set l}(x : X) where

 SplatSing' : Splatoid
 Splat SplatSing' = X >< \ x' -> x' ~ x
 splat SplatSing' (.x , r~) (.x , r~) = r~
{-)-}
```


## Calculating Splatoids

```agda
open import Lib.Nat

{-(-}
LeN : Nat * Nat -> Splatoid
LeN (ze   , m)    = SplatOne
LeN (su n , ze)   = SplatZero
LeN (su n , su m) = LeN (n , m)
{-)-}
```


## Calculating Tuple Types

```agda
data TDesc (I : Set) : Set where
  #_ : I -> TDesc I
  One' : TDesc I
  _*'_ : TDesc I -> TDesc I -> TDesc I

{-(-}
infixr 5 _*'_
infix  6 #_
{-)-}

open import Lib.Pi -- come back to this before tuple

{-(-}
module _ {I : Set} where

 Tuple  :   (I -> Set)
        ->  (TDesc I -> Set)
 Tuple P (# i) = P i
 Tuple P One' = One
 Tuple P (S *' T) = Tuple P S * Tuple P T
{-)-}

{-(-}
 tuple :   {P Q : I -> Set}
       ->  [ P -:> Q ]
       ->  [ Tuple P -:> Tuple Q ]
 tuple f {# i} p = f p
 tuple f {One'} <> = <>
 tuple f {S *' T} (s , t) = tuple f {S} s , tuple f {T} t
{-)-}
```



```agda
open import Lib.Datoid -- worth a look
open import Lib.Sum
```

## Calculating Datoids

What are the data?

In the lecture, I introduced some equipment as module parameters.

```agda
{-
module _ {J I : Set}(C : I -> Datoid)
         (F : {i : I}(c : Data (C i)) -> TDesc (J + I))
-}
```

I now think it is both clearer and more convenient to pack the equipment
up in a record. Here it is.

```agda
record TreeDesign : Set1 where
  field
    PayloadSort   : Set
    RecursiveSort : Set
    Constructor   : RecursiveSort -> Datoid
    ConArguments  : forall {i} -> Data (Constructor i)
                               -> TDesc (PayloadSort + RecursiveSort)
```

A `TreeDesign` generates a type of trees, as follows.

```agda
{-(-}
module _ (D : TreeDesign) where

 open TreeDesign D

 data Tree (X : PayloadSort -> Set)(i : RecursiveSort) : Set where
   _$_ : (c : Data (Constructor i))
      -> Tuple (X <?> Tree X) (ConArguments c)
      -> Tree X i

 infix 1 _$_
{-)-}
```

We should show that if the payload types have decidable equality, then
so do the trees.

```agda
{-(-}
 module _ (X : PayloadSort -> Datoid) where

  DatTree : RecursiveSort -> Datoid
  tupEq? : (T : TDesc (PayloadSort + RecursiveSort)) ->
           Dec~ (Tuple ((X - Data) <?> Tree (X - Data)) T)
  Data (DatTree i) = Tree (X - Data) i
  eq? (DatTree i) (c $ x) (d $ y) with eq? (Constructor i) c d
  eq? (DatTree i) (c $ x) (d $ y) | inl n = inl \ { r~ -> n r~ }
  eq? (DatTree i) (c $ x) (.c $ y) | inr r~ with tupEq? (ConArguments c) x y
  eq? (DatTree i) (c $ x) (.c $ y) | inr r~ | inl n = inl \ { r~ -> n r~ }
  eq? (DatTree i) (c $ x) (.c $ .x) | inr r~ | inr r~ = inr r~
  tupEq? (# inl j) s t with eq? (X j) s t
  tupEq? (# inl j) s t | inl n = inl \ { r~ -> n r~ }
  tupEq? (# inl j) s .s | inr r~ = inr r~
  tupEq? (# inr i) s t with eq? (DatTree i) s t
  tupEq? (# inr i) s t | inl n = inl \ { r~ -> n r~ }
  tupEq? (# inr i) s t | inr r~ =  inr r~
  tupEq? One'     <> <> = inr r~
  tupEq? (S *' T) (s0 , t0) (s1 , t1) with tupEq? S s0 s1 | tupEq? T t0 t1
  tupEq? (S *' T) (s0 , t0) (s1 , t1) | inl n | _ = inl \ { r~ -> n r~ }
  tupEq? (S *' T) (s0 , t0) (.s0 , t1) | inr r~ | inl n = inl \ { r~ -> n r~ }
  tupEq? (S *' T) (s0 , t0) (.s0 , .t0) | inr r~ | inr r~ = inr r~
{-)-}
```

The following is homework.

```agda
{-+}
 tree :  {P Q : J -> Set}
      -> [ P -:> Q ]
      -> [ Tree P -:> Tree Q ]
 tree f t = {!!}
{+-}
```

It is now worth bringing `TreeDesign`'s projections into scope.

```agda
open TreeDesign public
```


## Example 1 Natural Numbers Revisited

```agda
{-(-}
data NatuCons : Set where
  ze su : NatuCons

NatuC : Datoid
Data NatuC = NatuCons
eq? NatuC ze ze = inr r~
eq? NatuC ze su = inl \ ()
eq? NatuC su ze = inl \ ()
eq? NatuC su su = inr r~

DesignNatu : TreeDesign
PayloadSort   DesignNatu = Zero
RecursiveSort DesignNatu = One
Constructor   DesignNatu <> = NatuC
ConArguments  DesignNatu ze = One'
ConArguments  DesignNatu su = One' *' # inr <>    -- gratuitous?

Natu : Set
Natu = Tree DesignNatu (naughty - Data) <>

pattern zero = ze $ <>
pattern suc n = su $ <> , n
{-)-}
```

## Example 2 Length-Indexed Vectors

Length-indexed vectors `Vec X n` are lists whose elements are drawn
from `X` with length exactly `n`. That is, they are built inductively
from *payload* (the elements) and *recursive substructures*
(subvectors). That means we have `One` sort of payload, but a sort of
recursive structure for each length in `Nat`.

```agda
Vec : Set -> Nat -> Set

DesignVec : TreeDesign
PayloadSort   DesignVec = One
RecursiveSort DesignVec = Nat
Constructor   DesignVec n = DatOne -- only one constructor for each length
ConArguments  DesignVec {ze}   <> = One'        -- at length `ze`, no arguments
ConArguments  DesignVec {su n} <> =             -- at length `su n`...
     # inl <>   -- ...one piece of payload (the head)...
  *'            -- ...and...
     # inr n    -- ...one subvector of length `n` (the tail)

Vec X n = Tree DesignVec (ko X) n

```

Let's show the data being built.

```agda
-- vnil  : forall {X} -> Vec X ze
pattern vnil = <> $ <>

-- vcons : forall {X n} -> X -> Vec X n -> Vec X (su n)
pattern vcons x xs = <> $ x , xs


vec : {X Y : Set} -> (X -> Y) -> [ Vec X -:> Vec Y ]
vec f {ze} vnil = vnil
vec f {su n} (vcons x xs) = vcons (f x) (vec f xs)

```


## Example 3 Unlabelled Two,Three-Trees

```agda
{-(-}
data T23Cons : Nat -> Set where
  leaf       : T23Cons ze
  two three  : forall {n} -> T23Cons (su n)

T23C : Nat -> Datoid
Data (T23C n) = T23Cons n
eq? (T23C .ze) leaf leaf = inr r~
eq? (T23C .(su _)) two two = inr r~
eq? (T23C .(su _)) two three = inl \ ()
eq? (T23C .(su _)) three two = inl \ ()
eq? (T23C .(su _)) three three = inr r~

DesignT23 : TreeDesign
PayloadSort   DesignT23 = Zero  -- no payload
RecursiveSort DesignT23 = Nat   -- heights of trees
Constructor   DesignT23 = T23C
ConArguments  DesignT23 {ze}   leaf  = One'
ConArguments  DesignT23 {su n} two   = # inr n *' # inr n
ConArguments  DesignT23 {su n} three = # inr n *' # inr n *' # inr n

T23D : {n : Nat} -> Data (T23C n) -> TDesc (Zero + Nat)
T23D {ze}  leaf  = One'
T23D {su n} two   = # inr n *' # inr n
T23D {su n} three = # inr n *' # inr n *' # inr n

T23 : Nat -> Set
T23 = Tree DesignT23 (naughty - Data)
{-)-}
```


## Examples 4, 5, 6, 7: Simply Typed Lambda Calculus

I have to prioritise, so I don't think I'll work through this in class.
This is what Phil would have done if he'd had another lecture, except that
it's coded within our little universe.

First, let us have simple types.

```agda
{-(-}
Ty : Set

DesignTy : TreeDesign
PayloadSort   DesignTy = Zero
RecursiveSort DesignTy = One
Constructor   DesignTy <> = DatOne +D+ DatOne            -- two constructors:
ConArguments  DesignTy (inl <>) = One'                   --   nullary, and
ConArguments  DesignTy (inr <>) = # inr <> *' # inr <>   --   binary
 
Ty = Tree DesignTy (naughty - Data) <>

pattern baseTy       = inl <> $ <>
pattern _-Ty>_ sg ta = inr <> $ sg , ta

IsArrow : Ty -> Splatoid
IsArrow baseTy       = SplatZero
IsArrow (sg -Ty> ta) = SplatOne
{-)-}
```

Next, let us have backward lists: with simple types as payload, these give us
contexts.

```agda
{-(-}
Bwd : Set -> Set

DesignBwd : TreeDesign
PayloadSort   DesignBwd = One
RecursiveSort DesignBwd = One
Constructor   DesignBwd <> = NatuC
ConArguments  DesignBwd ze = One'
ConArguments  DesignBwd su = # inr <>  -- recursive tail
                           *' # inl <>  -- payload head

Bwd X = Tree DesignBwd (ko X) <>

pattern []        = ze $ <>
pattern _-,_ xz x = su $ xz , x
{-)-}
```

Next, we can have typed de Bruijn indices, enforcing that the type of a
variable is exactly what the context says it is.

```agda
{-(-}
In : Bwd Ty * Ty -> Set

DesignIn : Ty -> TreeDesign
PayloadSort   (DesignIn ta) = Zero
RecursiveSort (DesignIn ta) = Bwd Ty
Constructor   (DesignIn ta) []         = DatZero  -- no vars in empty context
Constructor   (DesignIn ta) (Ga -, sg) = DatOne +D+ DatEq sg ta
ConArguments  (DesignIn ta) {[]}        ()
ConArguments  (DesignIn ta) {Ga -, sg}  (inl <>) = # inr Ga  -- keep looking in Ga
ConArguments  (DesignIn ta) {Ga -, .ta} (inr r~) = One'      -- stop, we found it

In (Ga , ta) = Tree (DesignIn ta) (naughty - Data) Ga

pattern dbZe   = inr r~ $ <>
pattern dbSu x = inl <> $ x
{-)-}
```

Finally, we have the well typed terms, with variables as payload.
Observe that there is a constructor for abstraction only when the
type is an arrow.

```agda
{-(-}
Term : Bwd Ty * Ty -> Set

DesignTerm : TreeDesign
PayloadSort   DesignTerm = Bwd Ty * Ty
RecursiveSort DesignTerm = Bwd Ty * Ty
Constructor   DesignTerm (Ga , ta) =
    (DatOne                         -- variables
     +D+
     DatTree DesignTy naughty <>)   -- application
  +D+
    DatSplat (IsArrow ta)           -- abstraction
ConArguments DesignTerm {Ga , ta}     (inl (inl <>)) =
  # inl (Ga , ta)
ConArguments DesignTerm {Ga , ta}     (inl (inr sg)) =
  # inr (Ga , sg -Ty> ta) *' # inr (Ga , sg)
ConArguments DesignTerm {Ga , (sg -Ty> ta)} (inr <>) =
  # inr ((Ga -, sg) , ta)

Term = Tree DesignTerm In

pattern vrbl x   = inl (inl <>) $ x
pattern appl f s = inl (inr _) $ f , s
pattern lmda t   = inr <> $ t

churchTwo : forall {Ga ta} -> Term (Ga , (ta -Ty> ta) -Ty> (ta -Ty> ta))
churchTwo =
  lmda (lmda (appl (vrbl (dbSu dbZe)) (appl (vrbl (dbSu dbZe)) (vrbl dbZe))))
{-)-}
```


## Here in the File, but not in the Story

This stays commented out until it's needed.

```agda
{-(-}
DesignIntv : TreeDesign
PayloadSort   DesignIntv = Zero
RecursiveSort DesignIntv = One
Constructor   DesignIntv <> = DatOne
ConArguments  DesignIntv <> = One' *' One'
{-)-}
```


## Order! Order!

In this segment, I'm going to give a *transformation* of datatype designs,
inducing an *ordering* invariant.

Fix a datoid of *keys*.

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
 module ORDER (Le : Data Key * Data Key -> Splatoid)
  where

  LeB : Bound * Bound -> Splatoid
  LeB (bot   ,     _) = SplatOne
  LeB (val x , val y) = Le (x , y)
  LeB (_     ,   top) = SplatOne
  LeB (_     ,     _) = SplatZero
```

It is a handy fact that every binary tree has n+1 leaves and n nodes,
and they alternate in the course of an *inorder* traversal.

If we start from a data structure with no payload, we can turn it into
a binary tree with a key for every pairing site, and ordering evidence
as payload.

```agda
{-(-}
  module _ (D : TreeDesign)(Q0 : PayloadSort D ~ Zero) where

   Keys : forall {I} -> TDesc I -> Datoid
   Keys (# x) = DatOne
   Keys One' = DatOne
   Keys (S *' T) = Keys S >D< \ _ -> Key >D< \ _ -> Keys T

   BoundTuple :   (T : TDesc (PayloadSort D + RecursiveSort D))
              ->  Bound * Bound
              ->  Data (Keys T)
              ->  TDesc ((Bound * Bound) + (RecursiveSort D * Bound * Bound))
   BoundTuple (# inl x) lu ks rewrite Q0 = naughty x
   BoundTuple (# inr i) lu ks = # inr (i , lu)
   BoundTuple One' lu ks = # inl lu
   BoundTuple (S *' T) (l , u) (ks , k , kt) =
     BoundTuple S (l , val k) ks *' BoundTuple T (val k , u) kt

   DesignOrder : TreeDesign
   PayloadSort   DesignOrder = Bound * Bound
   RecursiveSort DesignOrder = RecursiveSort D * (Bound * Bound)
   Constructor   DesignOrder (i , _) = Constructor D i >D< (ConArguments D - Keys)
   ConArguments  DesignOrder {i , lu} (c , ks) = BoundTuple (ConArguments D c) lu ks

   OTree : RecursiveSort D * Bound * Bound -> Set
   OTree = Tree DesignOrder (LeB - Splat)
{-)-}
```

## Intervals

Now go back to the interloper.

```agda
{-(-}
  Intv = OTree DesignIntv r~
  pattern intv lk k ku = (<> , <> , k , <>) $ (lk , ku)
{-)-}
```

## Ordered Lists

```agda
{-(-}
  OList = OTree DesignNatu r~
  pattern onil lu = (ze , <>) $ lu
  pattern ocons lk k ku = (su , <> , k , <>) $ (lk , ku)
{-)-}
```

## Ordered 2,3-Trees


```agda
{-(-}
  OT23 = OTree DesignT23 r~
  pattern leaf0 lu = (leaf , <>) $ lu
  pattern node2 lk k ku = (two , <> , k , <>) $ (lk , ku)
  pattern node3 lj j jk k ku =
    (three , <> , j , <> , k , <>) $ (lj , jk , ku)
{-)-}
```

## Insertion

```agda
{-(-}
  module _ (owoto : (x  y : Data Key) ->
                    Splat (Le (x , y)) + Splat (Le (y , x)))
   where

   TooBig : Nat * Bound * Bound -> Set
   TooBig (n , l , u) = {!!}

   insert : forall {n l u} ->
     Intv (<> , l , u) -> OT23 (n , l , u) ->
        TooBig (n , l , u)
      + OT23   (n , l , u)
   insert (intv lx x xu) (leaf0 lu) = {!!}
   insert (intv lx x xu) (node2 lk k ku) with owoto x k
   insert (intv lx x xu) (node2 lk k ku) | inl xk = {!!}
   insert (intv lx x xu) (node2 lk k ku) | inr kx = {!!}
   insert (intv lx x xu) (node3 lj j jk k ku) = {!!}
{-)-}
```


## Deletion is homework

All the hard work is contained in the problem
to extract and delete the rightmost (say) key
in a tree. That's a lot like insertion, except
that you need to figure out a TooSmall type.

You'll also need that Le is transitive.

Now to delete a particular key, go find it.
Once you've found it replace it by the rightmost
thing to its left.

Both rightmost extraction and general deletion
require the same method of bubbling a tree that
might be TooSmall back out to the root.


## Flattening


## Example

```agda
{-+}
open ORDER NatD LeN

myList : OList (<> , bot , top)
myList = ocons <> 0 (ocons <> 1 (ocons <> 10 (onil <>)))
{+-}
```
