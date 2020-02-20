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
xs +V ys = ?

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
  ?
  ?


-- TO BE CONTINUED...
