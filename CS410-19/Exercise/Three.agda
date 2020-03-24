module CS410-19.Exercise.Three where

open import Lib.Sigma

open import CS410-19.Exercise.One


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
