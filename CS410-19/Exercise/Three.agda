module CS410-19.Exercise.Three where

open import Lib.One
open import Lib.Two
open import Lib.Sum
open import Lib.Sigma
open import Lib.Pi
open import Lib.Nat

open import CS410-19.Exercise.One
open import CS410-19.Exercise.Two

-- Note... this is unfininshed. I've just pinched some exercises from the
-- past.


------------------------------------------------------------------------------
--  (I) Permutations
------------------------------------------------------------------------------

-- Let us pack up Splittings in a helpful way.

_<[_]>_ : forall {X} -> List X -> List X -> List X -> Set
xs <[ xys ]> ys =
  xs <: xys >< \ th ->
  ys <: xys >< \ ph ->
  Splitting th ph

-- When is one list a permutation of another?

data _%_ {X : Set} : List X -> List X -> Set where

  -- [] is a permutation of []
  []   : [] % []

  -- if xs ~ ys, then (x ,- xs) is a permutation of any list made by
  -- shoving x somewhere into ys
  _,-_ : forall {x xs ys' ys} ->
           (x ,- []) <[ ys' ]> ys ->
           xs % ys ->
           (x ,- xs) % ys'


--??--3.1---------------------------------------------------------------------

-- Show that every list is a permutation of itself.

reflP : {X : Set}{xs : List X} -> xs % xs
reflP = {!!}

--??--------------------------------------------------------------------------


--??--3.2---------------------------------------------------------------------

-- Construct an "unbiased" insertion operator which lets you grow a
-- permutation by inserting a new element anywhere, left and right

insP : forall {X : Set}{z : X}{xs xs' ys ys'} ->
         (z ,- []) <[ xs' ]> xs ->
         (z ,- []) <[ ys' ]> ys ->
         xs % ys -> xs' % ys'
insP l r p = {!!}

-- Now show that, given a permutation, and any element on the left,
-- you can find out where it ended up on the right, and why the
-- remaining elements form a permutation.

findLonR : forall {X : Set}{z : X}{xs xs' ys'} ->
                  (z ,- []) <[ xs' ]> xs ->
                  xs' % ys' ->
                  {!!}
findLonR l p = {!!}

-- HINT: again, you may need >< to give a sensible return type.

--??--------------------------------------------------------------------------


--??--3.3---------------------------------------------------------------------

-- Show that permutation is transitive.

transP : {X : Set}{xs ys zs : List X} -> xs % ys -> ys % zs -> xs % zs
transP p q = {!!}

-- HINT: you will need to define some useful operations on splittings to
-- get this to work.

-- HINT: this may help you figure out what you need for findLonR

-- For a small bonus, show that permutations are the morphisms of a
-- Category.

-- Show that permutation is symmetric.

symP : {X : Set}{xs ys : List X} -> xs % ys -> ys % xs
symP p = {!!}

-- A category where all morphisms are invertible is called a "groupoid".

--??--------------------------------------------------------------------------


--??--3.4---------------------------------------------------------------------

-- Make permutations act on All.

permute : {X : Set}{xs ys : List X} -> xs % ys ->
          {Q : X -> Set} -> All Q xs -> All Q ys

permute p qs = {!!}

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
--  (II) Polymorphic Pasting and Cutting
------------------------------------------------------------------------------

module _
  {I : Set}              -- index over I (e.g. numbers)
  (C : I >8 I)           -- C is a way of cutting up numbers (e.g. Length)
  (F : Set -> I -> Set)  -- F is a some data structure indexed over I
                         --   packing up some notion of element
  where

  -- A Pasting is an algebra which combines a bunch of F-structures into one
  -- big F structure. That is
  --   input a cut
  --   input pieces which are all Fs
  --   output one big F

  Pasting : Set1
  Pasting = forall {X} -> [ C -Tree (F X) -:> F X ]

  -- A Cutting is not quite the opposite:
  --   input a cut
  --   input one big F
  --   output pieces which are all Fs

  Cutting : Set1
  Cutting = forall {X i}(c : Cut (C i)) -> F X i -> All (F X) (pieces (C i) c)


--??--3.5---------------------------------------------------------------------

-- Check that you can indeed do these things for Length with _-Vec_

vecPaste : Pasting Length _-Vec_
vecPaste fs = {!!}

vecCut : Cutting Length _-Vec_
vecCut c f = {!!}

-- It's just possible you have useful components to hand.


--??--------------------------------------------------------------------------

-- In a moment, we're going to crank this up to multiple dimensions.
-- We need help from some old friends, first.

record Applicative (F : Set -> Set) : Set1 where
  infixl 4 _<*>_
  field
    pure  : forall {X} -> X -> F X
    _<*>_ : forall {S T} -> F (S -> T) -> F S -> F T


--??--3.6---------------------------------------------------------------------

-- Show that vectors are Applicative.

module _ where

  open Applicative

  vecApp : forall n -> Applicative (_-Vec n)
  vecApp n = {!!}

--??--------------------------------------------------------------------------


--??--3.7---------------------------------------------------------------------

-- Define traversal for vectors.

module _ {F : Set -> Set}(AF : Applicative F) where

  vecTraverse : forall {S T}
             -> (S -> F T)
             -> forall {n} -> S -Vec n -> F (T -Vec n)
  vecTraverse g xs = {!!}

-- In a similar vein, check also that All yanks through vectors.

vecYankAll : forall {I}{P : I -> Set}{is n}
  -> (All P is) -Vec n
  -> All (\ i -> P i -Vec n) is
vecYankAll pss = {!!}

--??--------------------------------------------------------------------------


-- Now we may define matrices as vectors of vectors

_-M-_ : forall {I J : Set} ->
        (Set -> I -> Set) -> (Set -> J -> Set) ->
        Set -> I * J -> Set
(F -M- G) X (i , j) = F (G X j) i

_-Matrix_ : Set -> Nat * Nat -> Set
_-Matrix_ = _-Vec_ -M- _-Vec_


--??--3.8---------------------------------------------------------------------

-- Check that you can transpose matrices.

transpose : forall {X i j} -> X -Matrix (i , j) -> X -Matrix (j , i)
transpose = {!!}

-- HINT: Use vecTraverse. It's a one-liner.

--??--------------------------------------------------------------------------


--??--3.9---------------------------------------------------------------------

-- To do 3.10 and 3.11, you will need some "plumbing". Feel free to skip these
-- until you need them.

allFromList : forall {I J}{f : I -> J}{P : J -> Set}{is : List I}
  -> All P (list f is) -> All (f - P) is
allFromList ps = {!!}

allToList : forall {I J}{f : I -> J}{P : J -> Set}{is : List I}
  -> All (f - P) is -> All P (list f is)
allToList ps = {!!}

module _ {F : Set -> Set}(AF : Applicative F) where

  open Applicative AF

  allYankApp : forall {I}{P : I -> Set} ->
    [ All (P - F) -:> (All P - F) ]
  allYankApp fps = {!!}

--??--------------------------------------------------------------------------


-- We're now ready to build the machinery.
-- Each dimension corresponds to a layer of data structure.
-- But you can *transpose* layers of structure, so you can
-- act on any one of the layers, treating the other layers
-- uniformly.

module _  -- let us have two dimensions
  {I : Set}
  (C : I >8 I)
  (F : Set -> I -> Set)
  (AppF : forall i -> Applicative \ X -> F X i)
  {J : Set}
  (D : J >8 J)
  (G : Set -> J -> Set)
  where

  -- This trick lets you use the applicative operations
  -- inside this module but does not let them escape.
  module CHEAPMODULETRICK {i : I} where
    open Applicative (AppF i) public
  open CHEAPMODULETRICK


--??--3.10--------------------------------------------------------------------

-- You get pasting algebras for each of the C and D dimensions.
-- (Concatenation is a good example.)
-- Show that you can paste 2-dimensional stuff in either dimension.
-- (i.e., you can put stuff side-by-side or one-atop-another.)

  paste2D : Pasting C F -> Pasting D G ->
            Pasting (C |+| D) (\ {X (i , j) -> F (G X j) i })
  paste2D pc pd = {!!}

--??--------------------------------------------------------------------------


-- Now we assume we have some way to "traverse" the outer layer.

  module _
    (yankFAll : forall {J}{P : J -> Set}{i}{js}
          -> F (All P js) i
          -> All (\ j -> F (P j) i) js
    )
    where

--??--3.11--------------------------------------------------------------------

-- You get a way of cutting in each dimension (e.g., chopping up
-- vectors). Show that you can cut 2-dimenstional stuff in either
-- dimension.

    cut2D : Cutting C F -> Cutting D G ->
            Cutting (C |+| D) (F -M- G)
    cut2D uc ud c fgx = {!!}

--??--------------------------------------------------------------------------

-- What have you done? This!

rectPaste : Pasting (Length |+| Length) _-Matrix_
rectPaste = paste2D Length _-Vec_ vecApp Length _-Vec_ vecPaste vecPaste

rectCut : Cutting (Length |+| Length) _-Matrix_
rectCut = cut2D Length _-Vec_ vecApp Length _-Vec_ vecYankAll vecCut vecCut


------------------------------------------------------------------------------
--  (III) Recutting
------------------------------------------------------------------------------

-- Given a notion of cutting, cut some more!

module RECUTTER {I}(C : I >8 I) where

  -- a helpfer function for the definition which follows
  subCollect : forall is -> All (\ j -> One + Cut (C j)) is -> List I
  subCollect []        []              = []
  subCollect (i ,- is) (inl <> ,- jss) = i ,- subCollect is jss
  subCollect (i ,- is) (inr c  ,- jss) = pieces (C i) c +L subCollect is jss

  Sub : I >8 (I >< C - Cut)
  Cut    (Sub (i , c)) =         -- for each of the pieces you have...
    All (\ j -> One + Cut (C j)) -- ...leave it alone or cut it again
        (pieces (C i) c)           
  pieces (Sub (i , c)) jss = subCollect (pieces (C i) c) jss

  Recutter : Set
  Recutter = (i : I)(c c' : Cut (C i)) ->
             Cut (Sub (i , c))  >< \ d ->
             Cut (Sub (i , c')) >< \ d' ->
             pieces (Sub (i , c)) d % pieces (Sub (i , c')) d'

--            01234567890123456789
-- one cut    {-------------}{---}
-- recut      {-----}{------}
--                   {------}{---}
-- another    {-----}{-----------}

--??--3.12--------------------------------------------------------------------

-- Construct the following:

module _ where

  open RECUTTER Length

  LengthRecutter : Recutter
  LengthRecutter i c c' = {!!}

-- You will probably need to implement a super-informative version of
-- comparison and subtraction.

--??--------------------------------------------------------------------------



-- more to follow...but no more holes
