# Thinning Composition Triangles

```agda
module Thin.Triangle where

open import Lib.Bwd
open import Lib.Sigma
open import Thin.Thin
```

```agda
module _ {X : Set} where

 data [_-_]~_ : forall  {ga de ze : Bwd X} ->
                        ga <= de -> de <= ze -> ga <= ze -> Set where
   _-^_  : forall {ga de ze}{th : ga <= de}{ph : de <= ze}{ps : ga <= ze} ->
           [ th - ph ]~ ps -> forall x -> [ th - ph -^ x ]~ ps -^ x
   _-^,_ : forall {ga de ze}{th : ga <= de}{ph : de <= ze}{ps : ga <= ze} ->
           [ th - ph ]~ ps -> forall x -> [ th -^ x - ph -, x ]~ ps -^ x
   _-,_  : forall {ga de ze}{th : ga <= de}{ph : de <= ze}{ps : ga <= ze} ->
           [ th - ph ]~ ps -> forall x -> [ th -, x - ph -, x ]~ ps -, x
   []    : [ [] - [] ]~ []

 infix 15 [_-_]~_
 infixl 20 _-^,_
```

```agda
 tri : forall {ga de ze}(th : ga <= de)(ph : de <= ze) -> <([ th - ph ]~_)>
 tri th (ph -^ x) = let ! v = tri th ph in ! v -^ x
 tri (th -^ .x) (ph -, x) = let ! v = tri th ph in ! v -^, x
 tri (th -, .x) (ph -, x) = let ! v = tri th ph in ! v -, x
 tri [] [] = ! []

 _-<=_ : forall {ga de ze}(th : ga <= de)(ph : de <= ze) -> ga <= ze
 th -<= ph = fst (tri th ph)
```

```agda
 noth- : forall {ga de}(th : ga <= de) -> [ noth - th ]~ noth
 noth- (th -^ x) = noth- th -^ x
 noth- (th -, x) = noth- th -^, x
 noth- [] = []
```

```agda
 io- : forall {ga de}(th : ga <= de) -> [ io - th ]~ th
 io- (th -^ x) = io- th -^ x
 io- (th -, x) = io- th -, x
 io- [] = []

 infixl 20 _-io
 _-io : forall {ga de}(th : ga <= de) -> [ th - io ]~ th
 (th -^ x) -io = th -io -^, x
 (th -, x) -io = th -io -, x
 [] -io = []
```
