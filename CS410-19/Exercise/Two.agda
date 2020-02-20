module CS410-19.Exercise.Two where

open import Lib.Zero
open import Lib.One
open import Lib.Two
open import Lib.Pi
open import Lib.Equality
open import Lib.Sigma
open import Lib.Nat
open import Lib.Sum
open import Cat.Cat

open import CS410-19.Exercise.One

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- How To Cut Things Up
------------------------------------------------------------------------------
------------------------------------------------------------------------------

-- The following record type gives a way to describe the possible ways to
-- cut shapes into finitely many pieces. The shape of each piece is given
-- by a value in type I. You give a type, Cut, to specify the ways things can
-- be cut, then a function which gives the list of the shapes of the pieces
-- the cut produces.

record CutInto (I : Set) : Set1 where
  constructor Space
  field
    Cut    : Set
    pieces : Cut -> List I

open CutInto public

-- We will often use the following notion of arrow, to talk about how to cut
-- up an "outside" shape of type O into a bunch of pieces whose "inside"
-- shapes have type I. Think of these things as templates, where O gives the
-- shapes of the templates and I gives the shapes of their holes.

_>8_ : Set -> Set -> Set1
I >8 O = O -> CutInto I

-- Let's have an example straight away. If we think of numbers as lengths,
-- we can specify how to cut a length into two pieces which sum to it.

Length : Nat >8 Nat
Cut    (Length n) = Nat >< \ i   -- length of first piece
                 -> Nat >< \ j   -- length of second piece
                 -> i +N j ~ n   -- proof that they add to what we're cutting
pieces (Length n) (i , j , _) = i ,- j ,- []   -- the two pieces

-- Suppose we have some P : I -> Set which specifies stuff fitting a given
-- inside shape. Well then, given some outside shape, we can say how to
-- cut it into pieces with inside shapes which we fill with Ps.

_-Frag_ : {I O : Set}(C : I >8 O) -> (I -> Set) -> (O -> Set)
(C -Frag P) o = Cut (C o) >< pieces (C o) - All P


------------------------------------------------------------------------------
-- 2.1 "Identity" and "Composition"
------------------------------------------------------------------------------

-- Define the identity cutting, where there is one piece, and the inside shape
-- is the same as the output shape.

Id>8 : forall {I} -> I >8 I
Id>8 i = {!!}


-- Define the composition of cuttings.

_->8-_ : forall {I J K} -> I >8 J -> J >8 K -> I >8 K
(IJ ->8- JK) k = {!!}

-- Here, a composite cut should explain how to cut a K into Js, then each J
-- into Is. The pieces you end up with should be all the Is from all the Js.
-- Hints: (i) Cut IJ : J -> Set; (ii) you may need a helper function to
-- assemble the pieces.

-- Check that -Frag makes them behave like identity and composition, up to
-- isomorphism.

toId>8 : forall {I}{P : I -> Set} -> [ P -:> Id>8 -Frag P ]
toId>8 p = {!!}

fromId>8 : forall {I}{P : I -> Set} -> [ Id>8 -Frag P -:> P ]
fromId>8 p = {!!}

to->8- : forall {I J K}(IJ : I >8 J)(JK : J >8 K){P : I -> Set} ->
  [ JK -Frag (IJ -Frag P) -:> (IJ ->8- JK) -Frag P ]
to->8- IJ JK (c , ijps) = {!!}

from->8- : forall {I J K}(IJ : I >8 J)(JK : J >8 K){P : I -> Set} ->
  [ (IJ ->8- JK) -Frag P -:> JK -Frag (IJ -Frag P) ]
from->8- IJ JK (c , ijps) = {!!}

-- The "to"s and "from"s should be mutally inverse, but I'll let you off that
-- proof task.


------------------------------------------------------------------------------
-- Trees made by repeated cutting
------------------------------------------------------------------------------

module _
  {I : Set}            -- shapes of things
  (C : I >8 I)         -- a way of cutting, where insides are like outsides
  (Leaf : I -> Set)    -- leaves of a given shape
  where

  data _-Tree_ (i : I) : Set where  -- trees have shapes in I

      -- if you have a leaf the right shape, it can be a tree
    leaf  : Leaf i -> _-Tree_ i

      -- otherwise cut into pieces where you plug in subtrees
    [8<_] : (C -Frag _-Tree_) i -> _-Tree_ i


------------------------------------------------------------------------------
-- 2.2 Folding over Trees
------------------------------------------------------------------------------

module _ {I : Set}{C : I >8 I} where

-- Define fold for trees. I.e., show that you can make a V from a tree if
--   (i)  you can make a V from a leaf
--   (ii) you can make a V from a tree whose subtrees have already been
--          made into Vs
-- To appease the termination checker, you need to define this mutually with
-- allFold (which is morally the same as all (fold ...))

  fold : forall {L V}
      -> [ L -:> V ]
      -> [ C -Frag V -:> V ]   -- an "algebra"
      -> [ C -Tree L -:> V ]
  allFold : forall {L V}
      -> [ L -:> V ]
      -> [ C -Frag V -:> V ]   -- an "algebra"
      -> [ All (C -Tree L) -:> All V ]
  fold leaf' algebra t = {!!}
  allFold leaf' algebra ts = {!!}

-- Prove that if you plug the constructors for trees into fold, you get
-- the identity.

  fold-rebuild : forall {L}{i}(t : (C -Tree L) i) ->
    fold leaf [8<_] t ~ t
  allFold-rebuild : forall {L}{is}(ts : All (C -Tree L) is) ->
    allFold leaf [8<_] ts ~ ts
  fold-rebuild t = {!!}
  allFold-rebuild ts = {!!}

-- Prove the following fusion law, which holds when the first fold acts
-- only at leaves.

  module _ {L U V}
    (l : [ L -:> C -Tree U ])
    (f : [ U -:> V ])
    (g : [ C -Frag V -:> V ])
    where

    fold-fusion : forall 
      {i}(t : (C -Tree L) i) ->
      fold f g (fold l [8<_] t) ~ fold (l - fold f g) g t
    allFold-fusion : forall 
      {is}(ts : All (C -Tree L) is) ->
      allFold f g (allFold l [8<_] ts) ~ allFold (l - fold f g) g ts
    fold-fusion t = {!!}
    allFold-fusion ts = {!!}


------------------------------------------------------------------------------
-- 2.3 Flattening Trees
------------------------------------------------------------------------------

-- By way of an example of folding, let us flatten.

-- Here are lists indexed by length (a.k.a. "vectors").

data _-Vec_ (X : Set) : Nat -> Set where
  [] : X -Vec 0
  _,-_ : forall {n} -> X -> X -Vec n -> X -Vec su n

-- Define their concatenation.

_+V_ : forall {X m n} -> X -Vec m -> X -Vec n -> X -Vec (m +N n)
xs +V ys = {!!}

-- We may define singletons of Xs (to put at the leaves of trees).

OneOf : Set -> Nat -> Set
OneOf X 1 = X
OneOf X _ = Zero

-- A (Length -Tree OneOf X) n is a binary tree with n leaves, each of
-- which stores *one* X. Show how to flatten such a tree to a vector,
-- using fold. Hint: you may need to define some helpers or learn to
-- use fancy lambdas
-- \ { pattern1 -> expression1 ; .. ; patternk -> expressionk }

flatten : forall {X} ->
          [ Length -Tree OneOf X -:> (X -Vec_) ]
flatten {X} = fold {V = (X -Vec_)}
  {!!}
  {!!}


------------------------------------------------------------------------------
-- 2.4 Binary Search Trees, Revisited
------------------------------------------------------------------------------

-- Remember this business from Lecture One?

module BST
  (Key : Set)
  (Le : Key -> Key -> Set)
  (owoto : (x y : Key) -> Le x y + Le y x)
  where

  data Bound : Set where
    -inf : Bound
    key  : Key -> Bound
    +inf : Bound

  LeB : Bound -> Bound -> Set
  LeB -inf    u       = One
  LeB (key x) (key y) = Le x y
  LeB l       +inf    = One
  LeB _       _       = Zero

  {-
  data Tree (l u : Bound) : Set where
  
    leaf : LeB l u -> Tree l u
    
    node : (k : Key) -> Tree l (key k) -> Tree (key k) u
        -> Tree l u
  -}

-- We can see these trees as a special case of our cutting-up constructions.

  BSTCut : (Bound * Bound) >8 (Bound * Bound)
  Cut    (BSTCut (l , u)) = Key
  pieces (BSTCut (l , u)) k = (l , key k) ,- (key k , u) ,- []

  LeB' : Bound * Bound -> Set
  LeB' (l , u) = LeB l u

  BST : Bound * Bound -> Set
  BST = BSTCut -Tree LeB'

-- Check that you can still write insert.

  insert : [ (BSTCut -Frag LeB') -:> BST -:> BST ]
  insert (k , lk ,- ku ,- []) t = {!!}


------------------------------------------------------------------------------
-- 2.5 Two-Three Trees
------------------------------------------------------------------------------

-- [2-3 trees](https://en.wikipedia.org/wiki/2%E2%80%933_tree) are a variant
-- on binary search trees which are well enough *balanced* to ensure
-- logarithmic access times. Crucially
--
--  * they have uniform height, i.e. all paths from the root to a leaf have
--    the same length
--  * each node has either one key  and   two subtrees
--                      or two keys and three subtrees

-- Your mission is to build 2-3 trees as an instance of -Tree by explaining
-- the meaningful ways to cut up intervals. The shape of a 2-3 tree is given
-- by a        Nat  -- the height
--         * Bound  -- the lower bound
--         * Bound  -- the upper bound

-- Please complete this datatype:

  data Cut23 : Nat * Bound * Bound -> Set where
    -- give a constructor for 2-nodes
    -- give a constructor for 3-nodes

-- With that done, explain the subtree structure:

  TwoThree : (Nat * Bound * Bound) >8 (Nat * Bound * Bound)
  Cut (TwoThree hlu) = Cut23 hlu
  pieces (TwoThree hlu) c = {!!}

-- Meanwhile, leaves must have height exactly 0, and should, as before,
-- contain ordering evidence.

  Leafy : Nat * Bound * Bound -> Set
  Leafy (0 , l , u) = LeB l u
  Leafy _           = Zero

-- We obtain 2-3 trees, enforcing both order and balance.

  Tree23 : Nat * Bound * Bound -> Set
  Tree23 = TwoThree -Tree Leafy

-- Now, let's figure out how to do insertion with *rebalancing*. When you
-- insert into a tree of a given height, most of the time, there's enough
-- slack in the tree to return a tree of the same height. E.g., if you
-- insert into a 2-node of height 1, you can give back a 3-node of height 1.
-- But sometimes, the original tree is *full*, so you have no option but
-- to increase the height. E.g., if you insert into a 3-node of height 1,
-- you have no choice but to give back a tree of height 2.

-- We can explain these possibilities as a way of cutting.

-- You will need to add information to the following datatype, but wait
-- until you see what you need.

  data CutInsert (nlu : Nat * Bound * Bound) : Set where
    asSmall : CutInsert nlu
    tooTall : {- what goes here? -> -} CutInsert nlu

-- Likewise, explain what pieces you get when we're too tall.

  Insert : (Nat * Bound * Bound) >8 (Nat * Bound * Bound)
  Cut (Insert nlu) = CutInsert nlu
  pieces (Insert nlu) asSmall                      = nlu ,- []
  pieces (Insert nlu) (tooTall {- what's here?-})  = {!!}

-- What you need the above to be should arise from trying to implement
-- the following.

  insert23 : [ (snd - BSTCut -Frag LeB') -:> Tree23 -:> Insert -Frag Tree23 ]
  insert23 (k , lk ,- ku ,- []) t = {!!}

-- This gives us the guts of an n * log n complexity sorting algorithm,
-- provided you can flatten efficiently.

-- First, wrap 2-3 trees as trees of some height between the widest bounds.

  BalanceTree : Set
  BalanceTree = Nat >< \ height -> Tree23 (height , -inf , +inf)

-- Now, you wrap insertion.

  insertBal : Key -> BalanceTree -> BalanceTree
  insertBal k (h , t) = {!!}

-- So that we have makeTree as before:

  makeBalTree : List Key -> BalanceTree
  makeBalTree []        = 0 , leaf <>
  makeBalTree (k ,- ks) = insertBal k (makeBalTree ks)

-- In lecture 1, we defined ordered lists as follows
  {-
  data OList (l u : Bound) : Set where
  
    nil  : LeB l u -> OList l u
    
    cons : (k : Key) -> LeB l (key k) -> OList (key k) u
        -> OList l u
  -}

-- Refactor that definition in terms of -Tree.

  OList : Bound * Bound -> Set
  OList = {!!} -Tree LeB'

-- Use fold to define flatten.

  flattenBalTree : BalanceTree -> OList (-inf , +inf)
  flattenBalTree = {!!}

-- (There is a bonus for avoiding quadratic complexity by eliminating
-- left-nested concatenations.)

-- We should now have, as before:

  sort : List Key -> OList (-inf , +inf)
  sort = makeBalTree - flattenBalTree



-- TO BE CONTINUED...
