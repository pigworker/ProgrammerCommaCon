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


-- TO BE CONTINUED...
