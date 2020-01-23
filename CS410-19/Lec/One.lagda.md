Binary Search Trees
===================

This file is literate Agda markdown. Here is the obligatory module header.
It looks quite like a Haskell module header...

[This repo](https://github.com/pigworker/ProgrammerCommaCon)

It's pretty to look at this file rendered as html on github, but it's better
to actually load it in emacs, because then you can right-click on things to
explore their definitions

```agda
module CS410-19.Lec.One where

open import Lib.Zero  -- for the type Zero
open import Lib.One   -- for the type One and its constructor <>
open import Lib.Two   -- for the type Two and its constructors ff and tt
open import Lib.Sum   -- for types S + T with "constructors" inl and inr
open import Lib.Nat   -- for the natural numbers, Nat, made by ze and su
```

...but I've written an extra `open`. In **Agda**, `import` means "I want
that module from another file."; `open` means "I want that module's contents
in my current scope.". Haskell mashes the two ideas together, but it's
sometimes handy to separate them.

Yes, this will be a bit of a spot-the-difference game. As well as a development
of *sorting* by building a binary search tree and then flattening it.

More differences:

```agda
module TREE-UNSAFE
  (Key : Set)                   -- the keys we shall store in the trees
  (leKey : Key -> Key -> Two)   -- how to test whether two keys are in order
  where
```

* modules in Agda can have *parameters* which can be instantiated differently, each time the module is *opened*
* Agda uses *one* colon for typing, not two.
* `Set` corresponds roughly to Haskell's *kind*, `*`, but it is a *type*. Types are values. Types have types.
* It is *my* habit to name types after the number of values inhabiting them. `Two` is my name for Haskell's `Bool`. I call its inhabitants `ff` and `tt` because I come from the era of the 80 column display.

On with the trees! In Haskell we would write

```haskell
  data Tree = Leaf | Node Tree Key Tree
```

In Agda, we just declare the existence of a *type* constructor and some *value* constructors,
by giving types to identifiers.

```agda
  data Tree : Set where
  
    leaf : Tree
    
    node : Tree -> Key -> Tree
        -> Tree
```

I'm going to declare lists locally. We'll think more about lists, real soon.

```agda
  data List : Set where
    []   : List
    _,-_ : Key -> List -> List
  infixr 4 _,-_
```

That `_,-_` is just an ordinary identifier in Agda. Agda is very relaxed about which characters
you can use in identifiers. (It is correspondingly quite demanding about where you need to put
*spaces*. If in doubt, space it out!) Underscores in identifiers turn them into templates for
*mixfix* usage. Here, when I call the cons operator `_,-_`, I'm saying I can write `x ,- xs`
(where those spaces are really necessary: `x,-xs` is one identifier, with a silly but legal name).

Now, let us define `insert`.

```agda
  insert : Key -> Tree -> Tree
  insert k leaf           = node leaf k leaf
  insert k (node lt x rt) with leKey k x
  insert k (node lt x rt) | tt = node (insert k lt) x rt
  insert k (node lt x rt) | ff = node lt x (insert k rt)
```

What is this `with` business? It's Agda's alternative to `case` expressions, but it happens on the
*left* of the `=` sign. We are bringing the value of `leKey k x` to the left hand side as an extra
column of data on which we can match. The column is separated from `insert`'s arguments by vertical
bars. The idea is that you don't have to stop matching on the arguments when you start matching on
other stuff. (The `with` construct has a further superpower which we'll encounter later. Historical
note: James McKinna and I invented `with`, in our paper, *The view from the left*.)

Finishing the job, we can build trees by iterating insertion...

```agda
  makeTree : List -> Tree
  makeTree []        = leaf
  makeTree (x ,- ks) = insert x (makeTree ks)
```

...concatenate lists...

```agda
  _++_ : List -> List -> List
  []        ++ ys = ys
  (x ,- xs) ++ ys = x ,- xs ++ ys
  infixr 4 _++_
```

...flatten trees...

```agda
  flatten : Tree -> List
  flatten leaf         = []
  flatten (node l x r) = flatten l ++ x ,- flatten r
```

...and sort.

```agda
  sort : List -> List
  sort xs = flatten (makeTree xs)
```

Let's have an example, sorting natural numbers.

```agda
module SORTNAT-UNSAFE where

  leKey : Nat -> Nat -> Two
  leKey ze     y      = tt
  leKey (su x) ze     = ff
  leKey (su x) (su y) = leKey x y

  open TREE-UNSAFE Nat leKey  -- instantiate the parameters

  myList : List
  myList = 5 ,- 7 ,- 4 ,- 9 ,- 10 ,- 3 ,- 6 ,- []

  myTree : Tree
  myTree = makeTree myList

  myListSorted : List
  myListSorted = sort myList  -- flatten myTree
```

As a thought experiment, consider all the ways we could have got the above
program wrong. The type `Two` doesn't really account for *what* is false
or true.

In Agda, we can treat data as evidence *about* data, because types can
*depend* on values in various ways. The most straightforward mechanism
is just computing types from values by ordinary functional programming.

Here, for example, we compute from two natural numbers the type of
*evidence* that the first is less than or equal to the second.

```agda
LeNat : Nat -> Nat -> Set
LeNat ze     y       = One         -- "that's obvious!"
LeNat (su x) ze      = Zero        -- "no way!"
LeNat (su x) (su y)  = LeNat x y   -- reduced to a simpler problem
```

`One` is the *unit* type (called `()` in Haskell). Its only value is given
by the constructor `<>` which I pronounce "void" (also called `()` in Haskell).

`Zero` is the *empty* type (`Data.Void` in Haskell; it's in the Haskell library
because I proposed it as a joke and they took me seriously.) and it's used to
represent things which we want to make impossible, like `LeNat 7 3`. `Zero` is
a datatype with *no* constructors.

Crucially, Agda's typechecker *runs programs*. That's why the following
program typechecks. It witness that `LeNat` gives us a *total* order.
The `+` type former is the analogue of Haskell's `Either`, with
constructors `inl` and `inr`. (That's a slight lie, but the truth will
emerge shortly.)

```agda
owotoNat : (x y : Nat) -> LeNat x y + LeNat y x
owotoNat ze     y      = inl <>
owotoNat (su x) ze     = inr <>
owotoNat (su x) (su y) = owotoNat x y
```

(`owoto` stands for "one way or the other")

Why does that typecheck?

* `LeNat ze y + LeNat y ze` = `One + LeNat y ze`, so `inl <>` typechecks
* `LeNat (su x) ze + LeNat ze (su x)` = `Zero + One`, so `inr <>` typechecks and no `inl` could possibly work
* `LeNat (su x) (su y) + LeNat (su y) (su x)` = `LeNat x y + LeNat y x`, so the recursive call does the right thing.

Let's reimagine how to build binary search trees, now that we have a way to demand and supply *evidence* of being in order.

```agda
module TREE
  (Key : Set)
  (Le : Key -> Key -> Set)
  (owoto : (x y : Key) -> Le x y + Le y x)
  where
```
