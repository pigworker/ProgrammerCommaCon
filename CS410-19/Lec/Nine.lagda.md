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
```

Every datatype has a fold operator.

```agda
  module _ {X : I -> Set}
      (alg : {i : I} -> [[ F i ]]0 X -> X i)
```

An *algebra* is a reimplementation of `con` for some other family
of `I`-indexed types. It says how to turn a tree node into an `X`
if you have already turned its subtrees into `X`s.

```agda
    where

    fold     : [ Data -:> X ]
    mapFold  : (D : Desc I) -> [[ D ]]0 Data -> [[ D ]]0 X
    fold (con ts) = alg (mapFold (F _) ts)
    mapFold (`V i)    t         = fold t
    mapFold `1        <>        = <>
    mapFold (D `* E)  (td , te) = mapFold D td , mapFold E te
    mapFold (S `>< T) (s , ts)  = s , mapFold (T s) ts
```

Annoyingly, we have to write `mapFold` to shut the termination
checker up. In truth,

    mapFold D = [[ D ]]1 fold


Natural Numbers
---------------

Natural numbers, in this setting, are given as follows.
(Sorry about the universe polymorphism noise.)

I use the `One -> Desc One`, even though the `One ->` is useless,
because I'm feeding `Data` what it eats.

```agda
NatDesc : One {lzero} -> Desc One
NatDesc <> = Two `>< (`1 <2> `V <>)

Nat' : Set
Nat' = Data NatDesc <>

ze' : Nat'
ze' = con (ff , <>)

su' : Nat' -> Nat'
su' n = con (tt , n)
```


What is an ornament?
--------------------

It's a way of upgrading an `I`-indexed description to a `J`-indexed
description. We should think of `I` as *plain* indices and `J` as
*fancy* indices. We need a function, `f`, which throws away the fancy
stuff.

```agda
module _ {I J : Set}(f : J -> I) where

  Inv : I -> Set
  Inv i = J >< \ j -> f j ~ i

  data Orn : Desc I -> Set1 where  -- ornaments of `Desc`ription of datatypes
    `V     : {i : I} -> Inv i -> Orn (`V i)
    `0     : Orn `0
    `1     : Orn `1
    _`*_   : {S T : Desc I} -> Orn S -> Orn T -> Orn (S `* T)
    _`><_  : (S : Set){T : S -> Desc I}(O : (s : S) -> Orn (T s)) -> Orn (S `>< T)
    ins><  : {D : Desc I}(S : Set) -> (S -> Orn D) -> Orn D
    del><  : {S : Set}{T : S -> Desc I}(s : S) -> Orn (T s) -> Orn (S `>< T)
```

What's going on? We have a bunch of constructors which *copy* those of
`Desc`. The variable constructor needs to know which fancy index should
replace the given plain index, hence the use of *inverse image*.

The action is in `ins><` and `del><`, which *edit* the old description,
respectively inserting and deleting tags. If you insert a tag, you may
use the extra information to structure the rest of the ornament.
If you want to delete a tag, you have to say what it would have been.

We can now read off the description of the fancy datatype.

```agda
  orn : {D : Desc I} -> Orn D -> Desc J
  orn (`V (j , _)) = `V j
  orn `0           = `0
  orn `1           = `1
  orn (O `* P)     = orn O `* orn P
  orn (S `>< O)    = S `>< \ s -> orn (O s)
  orn (ins>< S O)  = S `>< \ s -> orn (O s)
  orn (del>< s O)  = orn O
```

The payoff is that we get an automatic forgetful operation from fancy
to plain.

```agda
  fog : {D : Desc I}(O : Orn D){X : I -> Set} -> [[ orn O ]]0 (f - X) -> [[ D ]]0 X
  fog (`V (j , r~)) x         = x
  fog `1            <>        = <>
  fog (O `* P)      (xo , xp) = fog O xo , fog P xp
  fog (S `>< O)     (s , xo)  = s , fog (O s) xo
  fog (ins>< S O)   (s , xo)  = fog (O s) xo
  fog (del>< s O)   xo        = s , fog O xo
```


Applying Ornaments to Datatypes
-------------------------------

(I did some tidying here, since lectures.)

This is what you need to provide to explain how to make a fancy version
of a datatype.

```agda
OrnData : {I : Set}               -- plain indices
          (J : Set)(f : J -> I)   -- fancy indices and how to recover the plain
          (F : I -> Desc I)       -- plain node structure for each plain index
       -> Set1
OrnData J f F = (j : J)           -- given a fancy index
             -> Orn f (F (f j))   -- how do you ornament the underlying plain node structure?
```

Given such a thing

```agda
module _ {I : Set}{J : Set}{f : J -> I}{F : I -> Desc I}(O : OrnData J f F) where
```

we obtain the node description for each fancy index,

```agda
  OrnDesc : J -> Desc J
  OrnDesc j = orn f (O j)
```

and we obtain an *algebra* for computing plain data from the nodes of fancy data.
That's called the *ornamental algebra*.

```agda
  ornAlg : {j : J} -> [[ OrnDesc j ]]0 (f - Data F) -> (f - Data F) j
  ornAlg {j} = fog f (O j) - con
```

Folding over fancy data with the ornamental algebra computes the plain data from
fancy data, throwing away the extra information demanded by the ornament. The
definition of ornament ensures that fancy data contain at least as much information
as plain data, so this operation comes for free.

```agda
  dataFog : [ Data OrnDesc -:> (f - Data F) ]
  dataFog = fold OrnDesc ornAlg
```


Example: Lists are Fancy Numbers
--------------------------------

Rather than inventing lists by pure inspiration, let us construct them from
natural numbers. Let's give all the succesors an extra tag, being some value
in a given type elements, `X`.

```agda
Nat2List : Set                       -- element type
        -> OrnData One _ NatDesc     -- how to make fancy numbers
Nat2List X <> =
  Two `>< \  -- zero-or-successor becomes nil-or-cons
    { ff -> `1                            -- leave zero alone
    ; tt -> ins>< X \ _ -> `V (<> , r~)   -- for suc, insert a tag of type `X`
    }
```

The resulting description induces a datatype. We can rebuild the constructors.

```agda
List' : Set -> Set
List' X = Data (OrnDesc (Nat2List X)) <>

nil' : forall {X} -> List' X
nil' = con (ff , <>)

cons' : forall {X} -> X -> List' X -> List' X
cons' x xs = con (tt , x , xs)
```

For free, we get that lists have a *length*. That's exactly what you
get when you take a list and forget the elements which label the
successors.

```agda
length : forall {X} -> List' X -> Nat'
length = dataFog (Nat2List _)
```


Algebraic Ornaments
-------------------

Any *algebra* gives us an ornament. We call that an *algebraic ornament*.
Not all ornaments are algebraic: in casual conversation, some people have
the bad habit of referring to my notion of "algebraic ornament" when they
just mean "ornament" in general, not the specific sort induced by an
algebra.

An algebra tells us how to compute a value by folding over some data. If
we can do that dynamically, we can just as well do it statically! The
computed value becomes an index, specifying the desired value ahead of
time. We need to enforce the property that we get the value we desire.

```agda
module _
  {I : Set}          -- what used to index the nodes?
  (F : I -> Desc I)  -- what was the node structure for each index?
  {X : I -> Set}     -- what's our extra index information?
  (alg : {i : I} -> [[ F i ]]0 X -> X i)  -- what algebra computes it?
  where
```

We're now going to ornament our plain `I`-indexed data to obtain data
indexed by dependent pairs in `I >< X`. The forgetful map is `fst`.

We'll get to `AlgOrnKids` in a moment. Let's build the `OrnData` for
our ornament. We receive a pair `(i , x)` where the `i` tells us which
plain node structure we have to follow, and the `x` tells us the target
value that the `alg`ebra must give back.

Our first move is to ask exactly for a plain node with `X`s as its
substructures. Let's call that the "node plan". It achieves three things:

1. we choose all the *tags* for our node;
2. we choose the fancy *indices* for all our substructures;
3. we have exactly the data that the `alg`ebra expects.

Our next move is to insist that the algebra computes the `x` we wanted.

```agda
  AlgOrnKids : (D : Desc I) -> [[ D ]]0 X -> Orn {J = I >< X} fst D
  
  AlgOrn : OrnData (I >< X) fst F
  AlgOrn (i , x) =
    ins>< ([[ F i ]]0 X) \ xf ->   -- choose tags and substructure indices
    ins>< (alg xf ~ x) \ _ ->      -- check that we get the demanded index
    AlgOrnKids (F i) xf            -- grab the recursive substructures
```

For the rest of the ornament, we must follow the plain description, but
do two things:

4. where the plain description asks for a substructure of index `i`, we
   should pair that `i` up with the extra `x` from the node plan;
5. where the plain description asks for a tag, we should delete it,
   because the node plan tells us that tag, so we can just copy it over.

```agda
  AlgOrnKids (`V i)    x         = `V ((i , x) , r~)
  AlgOrnKids `1        <>        = `1
  AlgOrnKids (D `* E)  (xd , xe) = AlgOrnKids D xd `* AlgOrnKids E xe
  AlgOrnKids (S `>< T) (s , xt)  = del>< s (AlgOrnKids (T s) xt)
```


Example: Vectors from Lists
---------------------------

Here's how we say "vectors are lists indexed by their length".

We ornament the list description by exactly the ornamental algebra
which computes length. It's algebraic ornament of an ornamental algebra:
we call that a *reornament*. It tells us what information was in the
fancy type that wasn't already in the plain type.

What information is in a list that was not already in its length?
Exactly one element per successor! A vector!

```agda
List2Vec : (X : Set) -> OrnData (One * Nat') fst (OrnDesc (Nat2List X))
List2Vec X =
  AlgOrn
    (OrnDesc (Nat2List X))  -- the description of lists
    (ornAlg  (Nat2List X))  -- the length algebra
```

Let's check that we really get vectors.

```agda
Vec : Set -> Nat' -> Set
Vec X n = Data (OrnDesc (List2Vec X)) (<> , n)

vnil : forall {X} -> Vec X ze'
vnil = con
  ( _    -- a list node, but with lengths instead of sublists
  , r~   -- which must be nil, because the required length is zero
  , <>   -- we already chose the tag, so we're done
  )

vcons : forall {X n} -> X -> Vec X n -> Vec X (su' n)
vcons x xs = con
  ( inr (x , _)  -- a cons node, where the x goes, but with a length for a tail
  , r~           -- which must be n, because we demand its successor
  , xs           -- we already chose the length of the tail, now give the tail
  )
```


The Reornament Lemma
--------------------

Consider a reornament, in general. If the original ornament goes from "plain" to
"fancy", then the reornament goes from "fancy" to "recherché".

```agda
module _ {I J : Set}{f : J -> I}{F : I -> Desc I}(O : OrnData J f F) where

  Reornament : OrnData (J >< (f - Data F)) fst (OrnDesc {F = F} O)
  Reornament = AlgOrn (OrnDesc {F = F} O) (ornAlg O)
```

We now have *two* forgetful maps between data

1. `dataFog Reornament : [ Data (OrnDesc Reornament) -:> (fst - Data (OrnDesc O)) ]`
   *forgets* an index in `Data F`. That is, we go from recherché to fancy, forgetting
   the plain index.

2. `dataFog O : [ Data (OrnDesc O) -:> (f - Data F) ]` *computes* an index in
   `Data F`. That is, we go from fancy to plain.

What happens if we compose them?

Funnily enough, you recompute dynamically exactly the static index you forgot!

```agda
  reornamentLemma :
    {j : J}{x : Data F (f j)} ->
    (t : Data (OrnDesc Reornament) (j , x)) ->
    dataFog {F = F} O (dataFog Reornament t) ~ x
  reornamentLemma (con ( p   -- the node plan
                       , r~  -- the proof that x is ornAlg O p
                       , ts  -- the subtrees
                       ))
    =  ornAlg O         -- both sides are computed by ornAlg O
    $~ help (O _) p ts  -- show that we recover p from ts
    where

    -- handy abbreviation
    AOK : (E : Desc J) -> [[ E ]]0 (f - Data F) -> Orn fst E
    AOK = AlgOrnKids (OrnDesc {F = F} O) (ornAlg O)

    -- this is a bit of a gobful, but it comes from the goal;
    help :
      -- abstract over the structure of the *top* node, so we can step through it
      -- without affecting the structure of its subnodes
      {D : Desc I}(OD : Orn f D) ->
      -- we will have part of the static node plan
      (p  : [[ orn f OD ]]0 (f - Data F))
      -- we will have the subtrees, from which we can recompute a dynamic node plan
      (ts : [[ orn fst (AOK (orn f OD) p) ]]0 (Data (OrnDesc Reornament))) ->
      -- the "dynamic" node plan, computed by recursion over the subtrees
      mapFold (OrnDesc {F = F} O) (ornAlg O) (orn f OD)
       -- make a fancy node full of plain subtrees, i.e., a node plan
        (fog fst (AOK (orn f OD) p)
         -- make a fancy node full of fancy subtrees
          (mapFold (OrnDesc Reornament) (ornAlg Reornament) (orn fst (AOK (orn f OD) p))
           -- make a recherché node full of fancy subtrees
           -- from a recherché node full of recherché subtrees
            ts))
      -- is the static node plan we first thought of
      ~ p

    -- the proof is a bit of an anticlimax, after that: structural induction!
    help (`V (j , r~)) x         t         = reornamentLemma t
    help `1            <>        <>        = r~
    help (OD `* OE)    (pd , pe) (td , te) = _,_ $~ help OD pd td ~$~ help OE pe te
    help (S `>< OD)    (s , p)   ts        = (s ,_) $~ help (OD s) p ts
    help (ins>< S OD)  (s , p)   ts        = (s ,_) $~ help (OD s) p ts 
    help (del>< s OD)  p         ts        = help OD p ts
```
