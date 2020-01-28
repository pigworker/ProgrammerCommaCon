Binary Search Trees
===================

This file is literate Agda markdown. Here is the obligatory module header.
It looks quite like a Haskell module header...

```agda
module CS410-19.Lec.One where

open import Lib.Zero  -- for the type Zero
open import Lib.One   -- for the type One and its constructor <>
open import Lib.Two   -- for the type Two and its constructors ff and tt
open import Lib.Sum   -- for types S + T with "constructors" inl and inr
open import Lib.Nat   -- for the natural numbers, Nat, made by ze and su
open import Lib.Pi    -- for functional plumbing
```

...but I've written an extra `open`. In **Agda**, `import` means "I want
that module from another file."; `open` means "I want that module's contents
in my current scope.". Haskell mashes the two ideas together, but it's
sometimes handy to separate them.

[This repo](https://github.com/pigworker/ProgrammerCommaCon) is linked from
this sentence so that people watching the lecture know where the repo is.

It's pretty to look at this file rendered as html on github, but it's better
to actually load it in emacs, because then you can right-click on things to
explore their definitions

Now, this will be a bit of a spot-the-difference game. As well as a development
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

The central idea to manage our *requirements* of the data. Think of
types as expressing those requirements, rather than as emerging from
the data. Most subtrees of a binary search tree have the property
that the keys in the tree are bounded above and below. We can get
rid of the edge cases by artificially introducing *extreme* bounds.

```agda
  data Bound : Set where
    -inf : Bound
    key  : Key -> Bound
    +inf : Bound

  LeB : Bound -> Bound -> Set
  LeB -inf    u       = One
  LeB (key x) (key y) = Le x y
  LeB l       +inf    = One
  LeB _       _       = Zero
```

Let us extend ordering from `Key` to `Bound`:
`-inf` is below everything; `+inf` is above everything;
`Key`s are ordered as before.

We may now define a *family* of datatypes of trees which is
*indexed* by lower and upper bounds.

```agda
  data Tree (l u : Bound) : Set where
  
    leaf : LeB l u -> Tree l u
    
    node : (k : Key) -> Tree l (key k) -> Tree (key k) u
      --  -> LeB l (key k) -> LeB (key k) u -- there is a better way
        -> Tree l u
```

The key at each `node` is used as the upper bound for the left subtree
and the lower bound for the right subtree.

Observe that in a tree like the following...

```asciiart
                      5
          ,-----------^-----------,
          2           :           8
        ,-^-------,   :   ,-------^---,
        o :       4   :   6       :   9
        : :   ,---^-, : ,-^---,   : ,-^-,
        : :   3   : o : o :   7   : o : o
        : : ,-^-, : : : : : ,-^-, : : : :
        : : o : o : : : : : o : o : : : :
        : : : : : : : : : : : : : : : : :
   -inf o 2 o 3 o 4 o 5 o 6 o 7 o 8 o 9 o +inf
```

...the leaves and nodes alternate as we make an inorder traversal.
Project the leaves and nodes down into a sequence and you see!
If we store at each leaf the evidence that its bounds are in order,
then we have the evidence that each neighbouring pair of keys in
the sequence are in order, bookended by -inf and +inf.

(I wrote about this idea in my 2014
paper *How To Keep Your Neighbours In Order*.)

At the top level, we use `Tree -inf +inf` as the type of trees
which are welcoming to all keys.

Now we can write `insert` in a *bounds-preserving* manner. A new
key which shares the bounds of an old tree can be inserted.

```agda
  insert : forall {l u} ->
           (k : Key) -> LeB l (key k) -> LeB (key k) u 
        -> Tree l u
        -> Tree l u
  insert k lk ku (leaf lu) = node k (leaf lk) (leaf ku)
  insert k lk ku (node j ljt jut) with owoto k j
  ... | inl kj = node j (insert k lk kj ljt) jut
  ... | inr jk = node j ljt (insert k jk ku jut)
```

Observe that the evidence generated by the `owoto` test plays
a crucial role in the process: it justifies that the new key
actually shares the bounds of exactly the subtree it belongs
in (and certainly not the other one). It is much harder to
get this program wrong.

Let's finish the job. First, `makeTree`.

```agda
  data List : Set where
    []   : List
    _,-_ : Key -> List -> List
  infixr 4 _,-_
  
  makeTree : List -> Tree -inf +inf
  makeTree []        = leaf <>
  makeTree (k ,- ks) = insert k <> <> (makeTree ks)
```

Now, let's not throw away the knowledge we've gained.
Here's a type of *ordered* lists (which are built just
like ordered trees, but in right-spine form).

```asciiart
  2
  ^
 o 3
   ^
  o 4
    ^
   o 5
     ^
    o 6
      ^
     o 7
       ^
      o 8
        ^
       o 9
         ^
        o o
```

That is, the `nil` carries the right most ordering proof,
while each `cons` carries the ordering proof to the left of
its key.

```agda
  data OList (l u : Bound) : Set where
  
    nil  : LeB l u -> OList l u
    
    cons : (k : Key) -> LeB l (key k) -> OList (key k) u
        -> OList l u
```

Defining *append* for `OList` with type
`OList a b -> OList b c -> OList a c`
is not such a good plan, because at the join, there are
two ordering proofs with no key in between.

```asciiart
   a             b  b             c
    o-P-o-Q-o-R-o ?? o-S-o-T-o-U-o
```

At the very least, we should need to know that the order
is *transitive* (which is not necessary for `insert`), so
that we can squish the two ordering proofs into one.

But there is an easier way, when you remember that the
operation you're looking for wasn't exactly concatenation
in the first place. Here's the most important piece of
advice in dependently typed programming:

> You can't always get what you want,
> but if you try sometime, you just might find,
> that you get what you need.
>
> Jagger, M. and Richards, K.

```agda
  flatNode : forall {l u}     k
          -> OList l (key k) -> OList (key k) u
          -> OList l                          u
  flatNode k (nil lk)       ku = cons k lk ku
  flatNode k (cons j lj jk) ku = cons j lj (flatNode k jk ku)
```

When we're flattening a tree, we exactly do have a key to
put between the two lists, because the two lists are the
flattened subtrees of a *node*.

That is, the operation we need has the *same type* as `node`,
except that `Tree` has been replaced by `OList`, just as
`nil` has the same type as `leaf`, but with `Tree` replaced
by `OList`. In due course, we'll learn how to be more precise
about this idea of 'bunch of operations which are like the
constructors but (perhaps) for a different type',
which we shall refer to as 'an algebra'.

When you have a `Tree`-algebra for `OList`, there's a standard
recursive strategy for turning a `Tree` into an `OList`.

```agda
  flatten : forall {l u} -> Tree l u -> OList l u
  flatten (leaf lu)      = nil lu
  flatten (node k lk ku) = flatNode k (flatten lk) (flatten ku)
```

So now you can sort!

```agda
  sort : List -> OList -inf +inf
  sort = makeTree - flatten
```

And there you have another difference, which I'm afraid is one of
my idiosyncrasies: where Haskell's `.` operator has type

```haskell
(b -> c) -> (a -> b) -> (a -> c)
```

and may be pronounced "after" as an aide-memoire,
I define `-` to be *diagrammatic* composition, also pronounced
"then". One of its types is

```agda-example
  forall {A B C} -> (A -> B) -> (B -> C) -> (A -> C)
```

but its full dependent type is more...flexible. It's
"diagrammatic" in the sense that the components are placed
like edges in a graph, meeting at the vertices they share.

That's probably enough for this file.

Except that you might want to think about how to refactor
`flatten` to avoid left-nested calls to `flatNode`. The
traditional trick of introducing an accumulator is a good
start, but it's not quite enough to solve the problem...
