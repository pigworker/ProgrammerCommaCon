# Pullbacks of Thinnings

```agda
module Thin.Pullback where

open import Lib.Bwd
open import Lib.Sigma
open import Thin.Thin
open import Thin.Triangle
```

```agda
module _ {X : Set} where
 Square : {ga de : Bwd X} ->
          <(ga <=_) :* (_<= de)> -> <(ga <=_) :* (_<= de)> -> Set
 Square (th0 ^ ph0) (th1 ^ ph1) = 
   <([ th0 - ph0 ]~_) :* ([ th1 - ph1 ]~_)>

 data Pullback  :   {ga de : Bwd X}{a b : <(ga <=_) :* (_<= de)>}
                ->  Square a b -> Set where

   _-^_  : forall {ga de}{a b : <(ga <=_) :* (_<= de)>}{s : Square a b} ->
   
           let       v       ^ w       = s in Pullback s -> (x : X) ->
         ---------------------------------------------------------------
           Pullback (v -^ x  ^ w -^ x )

   _-^,_ : forall {ga de}{a b : <(ga <=_) :* (_<= de)>}{s : Square a b} ->
   
           let       v       ^ w       = s in Pullback s -> (x : X) ->
         ---------------------------------------------------------------
           Pullback (v -^ x  ^ w -^, x)
     
   _-,^_ : forall {ga de}{a b : <(ga <=_) :* (_<= de)>}{s : Square a b} ->
   
           let       v       ^ w       = s in Pullback s -> (x : X) ->
         ---------------------------------------------------------------
           Pullback (v -^, x ^ w -^ x )
           
   _-,_  : forall {ga de}{a b : <(ga <=_) :* (_<= de)>}{s : Square a b} ->
   
           let       v       ^ w       = s in Pullback s -> (x : X) ->
         ---------------------------------------------------------------
           Pullback (v -, x  ^ w -, x )
           
   []    :
         --------------------------------
           Pullback (  []    ^   []   )     
```

The salient point from the above definition is that `x` is in the pullback
if and only if it is in both thinnings to `de`. You can see this by looking
at the triangles: there is no constructor for the case where both are made
by `-^,` for that would mean that some `x` is *included* by both thinnings
to `de` but *excluded* by both thinnings from `ga`.

We may now express succinctly what it means for two thinnings with the
same target to be disjoint. Their intersection must be empty, so the
degenerate triangles from the empty scope (which certainly form a square)
must, in particular, form a *pullback*.

```agda
 Disjoint : forall {ga ze de}(th : ga <= ze)(ph : de <= ze) -> Set
 Disjoint th ph = Pullback (noth- th ^ noth- ph)
```

```agda
 pullback : forall {ga0 ga ga1}(th0 : ga0 <= ga)(th1 : ga1 <= ga) ->
   <(_<= ga0) :* (_<= ga1)> >< \ a -> let ph0 ^ ph1 = a in
   Square (ph0 ^ th0) (ph1 ^ th1) >< Pullback
 pullback (th0 -^ x) (th1 -^ .x) = let ! ! p = pullback th0 th1 in ! ! p -^ x
 pullback (th0 -^ x) (th1 -, .x) = let ! ! p = pullback th0 th1 in ! ! p -^, x
 pullback (th0 -, x) (th1 -^ .x) = let ! ! p = pullback th0 th1 in ! ! p -,^ x
 pullback (th0 -, x) (th1 -, .x) = let ! ! p = pullback th0 th1 in ! ! p -, x
 pullback [] [] = ! ! []
```
