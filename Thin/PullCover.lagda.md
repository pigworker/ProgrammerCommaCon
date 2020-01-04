# Covers and Pullbacks

```agda
module Thin.PullCover where

open import Lib.Equality
open import Lib.Splatoid
open import Lib.Bwd
open import Lib.Sigma
open import Lib.Sum
open import Thin.Thin
open import Thin.Cover
open import Thin.Pullback
open import Thin.Triangle
```

```agda
module _ {X : Set} where

 selCover : forall {ga de0 de1 de : Bwd X}(th : ga <= de)
   {ph0 : de0 <= de}{ph1 : de1 <= de} -> ph0 /u\ ph1 ->
   (<(_<= de0) :* (_<= ga)> * <(_<= de1) :* (_<= ga)>) >< \ d ->
   let th0 ^ ps0 , th1 ^ ps1 = d in ps0 /u\ ps1
 selCover (th -^ .x) (u -^, x) with selCover th u
 ... | (th0 ^ ps0 , th1 ^ ps1) , u' = (th0 ^ ps0 , th1 -^ x ^ ps1) , u'
 selCover (th -^ .x) (u -,^ x) with selCover th u
 ... | (th0 ^ ps0 , th1 ^ ps1) , u' = (th0 -^ x ^ ps0 , th1 ^ ps1) , u'
 selCover (th -^ .x) (u -, x) with selCover th u
 ... | (th0 ^ ps0 , th1 ^ ps1) , u' = (th0 -^ x ^ ps0 , th1 -^ x ^ ps1) , u'
 selCover (th -, .x) (u -^, x) with selCover th u
 ... | (th0 ^ ps0 , th1 ^ ps1) , u' = (th0 ^ ps0 -^ x , th1 -, x ^ ps1 -, x) , u' -^, x 
 selCover (th -, .x) (u -,^ x) with selCover th u
 ... | (th0 ^ ps0 , th1 ^ ps1) , u' = (th0 -, x ^ ps0 -, x , th1 ^ ps1 -^ x) , u' -,^ x
 selCover (th -, .x) (u -, x) with selCover th u
 ... | (th0 ^ ps0 , th1 ^ ps1) , u' = (th0 -, x ^ ps0 -, x , th1 -, x ^ ps1 -, x) , u' -, x
 selCover [] [] = ([] ^ [] , [] ^ []) , []
   

 pullCover : forall {ga de0 de1 de : Bwd X}(th : ga <= de)
   {ph0 : de0 <= de}{ph1 : de1 <= de} -> ph0 /u\ ph1 ->
   (<(_<= de0) :* (_<= ga)> * <(_<= de1) :* (_<= ga)>) >< \ d ->
   let th0 ^ ps0 , th1 ^ ps1 = d in
   (Square (th0 ^ ph0) (ps0 ^ th) >< Pullback) *
   ps0 /u\ ps1 *
   (Square (ps1 ^ th) (th1 ^ ph1) >< Pullback)
 pullCover (th -^ x) (u -^, .x) with pullCover th u
 ... | ! (! p0) , u' , (! p1) = ! (! p0 -^ x) , u' , (! (p1 -^, x))
 pullCover (th -^ x) (u -,^ .x) with pullCover th u
 ... | ! (! p0) , u' , (! p1) = ! (! p0 -,^ x) , u' , (! p1 -^ x)
 pullCover (th -^ x) (u -, .x) with pullCover th u
 ... | ! (! p0) , u' , (! p1) = ! (! p0 -,^ x) , u' , (! (p1 -^, x))
 pullCover (th -, x) (u -^, .x) with pullCover th u
 ... | ! (! p0) , u' , (! p1) = ! (! (p0 -^, x)) , u' -^, x , (! p1 -, x)
 pullCover (th -, x) (u -,^ .x) with pullCover th u
 ... | ! (! p0) , u' , (! p1) = ! (! p0 -, x) , u' -,^ x , (! p1 -,^ x)
 pullCover (th -, x) (u -, .x) with pullCover th u
 ... | ! (! p0) , u' , (! p1) = ! (! p0 -, x) , u' -, x , (! p1 -, x)
 pullCover [] [] = ! (! []) , [] , (! [])
   
```

```agda
 oneCover :  forall {ga0 ga ga1 : Bwd X}{th0 : ga0 <= ga}{th1 : ga1 <= ga}
             {x : X} (y : x <- ga) -> th0 /u\ th1
         ->  < [_- th0 ]~ y > + < [_- th1 ]~ y >
 oneCover y u with pullCover y u
 oneCover y u | ! _ , [] -^, x , (v ^ w , _) with splat splatTri (! v) (! io- y)
 ... | r~ = inr (! w)
 oneCover y u | ! (v ^ w , _) , [] -,^ x , _ with splat splatTri (! w) (! io- y)
 ... | r~ = inl (! v)
 oneCover y u | ! (v ^ w , _) , [] -, x  , _ with splat splatTri (! w) (! io- y)
 ... | r~ = inl (! v)
```
