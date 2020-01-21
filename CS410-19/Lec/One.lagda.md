Binary Search Trees
===================

This file is literate Agda markdown. Here is the obligatory module header.
It looks quite like a Haskell module header...

```agda
module CS410-19.Lec.One where

open import Lib.Nat
open import Lib.Zero
open import Lib.One
open import Lib.Two
open import Lib.Sum
```

...but I've written an extra `open`. In **Agda**, `import` means "I want
that module from another file."; `open` means "I want that module's contents
in my current scope.". Haskell mashes the two ideas together, but it's
sometimes handy to separate them.

Yes, this will be a bit of a spot-the-difference game. As well as a development
of *sorting* by building a binary search tree and then flattening it.

Another difference...

```agda
module TREE
  (Key : Set)
  (LeKey : Key -> Key -> Set)
  (owoto : (x y : Key) -> LeKey x y + LeKey y x)
  where

  {- data Tree = Leaf | Node Tree Key Tree -}
{-
  data Tree : Set where
  
    leaf : Tree
    
    node : Tree -> Key -> Tree
        -> Tree

  data List : Set where
    []   : List
    _,-_ : Key -> List -> List
  infixr 4 _,-_

  insert : Key -> Tree -> Tree
  insert k leaf = node leaf k leaf
  insert k (node lt x rt) with leKey k x
  insert k (node lt x rt) | tt = node (insert k lt) x rt
  insert k (node lt x rt) | ff = node lt x (insert k rt)

  makeTree : List -> Tree
  makeTree [] = leaf
  makeTree (x ,- ks) = insert x (makeTree ks)
-}
```

```agda
leKey : Nat -> Nat -> Two
leKey ze y = tt
leKey (su x) ze = ff
leKey (su x) (su y) = leKey x y

LeKey : Nat -> Nat -> Set
LeKey ze y = One
LeKey (su x) ze = Zero
LeKey (su x) (su y) = LeKey x y

owoto : (x y : Nat) -> LeKey x y + LeKey y x
owoto ze y = inl <>
owoto (su x) ze = inr <>
owoto (su x) (su y) = owoto x y

open TREE Nat
{-
foo = makeTree (5 ,- 2 ,- 3 ,- 1 ,- 0 ,- [])
-}

```


