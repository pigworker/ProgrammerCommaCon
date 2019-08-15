# Thinning Composition Triangles

```agda
module Thin.Triangle where

open import Lib.Equality
open import Lib.Splatoid
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


```agda
 splatTri : forall {ga de ze}{th : ga <= de}{ph : de <= ze} -> Splatoid
 Splat (splatTri {th = th} {ph = ph}) = <([ th - ph ]~_)>
 splat splatTri (! v0 -^ x)  (! v1 -^ .x)
   with splat splatTri (! v0) (! v1)
 ... | r~ = r~
 splat splatTri (! v0 -^, x) (! v1 -^, .x)
   with splat splatTri (! v0) (! v1)
 ... | r~ = r~
 splat splatTri (! v0 -, x)  (! v1 -, .x) 
   with splat splatTri (! v0) (! v1)
 ... | r~ = r~
 splat splatTri (! [])       (! [])        = r~
```

```agda
 assoc03 : forall {ga0 ga1 ga2 ga3}
   {th01 : ga0 <= ga1}{th23 : ga2 <= ga3}
   {th02 : ga0 <= ga2}{th13 : ga1 <= ga3} ->
   <([ th01 -_]~ th02 ) :* ([_- th23 ]~ th13)>   -- th12 is shared
   ->
   <([ th01 - th13 ]~_) :* ([ th02 - th23 ]~_)>  -- th03 is generated
 assoc03 (v        ^ w -^ x)  =
   let v' ^ w' = assoc03 (v ^ w) in v' -^ x  ^ w' -^ x
 assoc03 (v -^ .x  ^ w -^, x) =
   let v' ^ w' = assoc03 (v ^ w) in v' -^ x  ^ w' -^, x
 assoc03 (v -^, .x ^ w -, x)  =
   let v' ^ w' = assoc03 (v ^ w) in v' -^, x ^ w' -^, x
 assoc03 (v -, .x  ^ w -, x)  =
   let v' ^ w' = assoc03 (v ^ w) in v' -, x  ^ w' -, x
 assoc03 ([]       ^ [])      =    []        ^ []

 assoc02 : forall {ga0 ga1 ga2 ga3}
   {th01 : ga0 <= ga1}{th23 : ga2 <= ga3}
   {th03 : ga0 <= ga3}{th12 : ga1 <= ga2} ->
   <([ th01 -_]~ th03 ) :* ([ th12 - th23 ]~_)>  -- th13 is shared
   ->
   <([ th01 - th12 ]~_) :* ([_- th23 ]~ th03)>   -- th02 is generated
 assoc02 {th01 = th01} {th12 = th12} (v013 ^ v123) with tri th01 th12
 ... | ! v012 with assoc03 (v012 ^ v123)
 ... | v013' ^ v023 with splat splatTri (! v013) (! v013')
 ... | r~ = v012 ^ v023

 assoc13 : forall {ga0 ga1 ga2 ga3}
   {th01 : ga0 <= ga1}{th23 : ga2 <= ga3}
   {th03 : ga0 <= ga3}{th12 : ga1 <= ga2} ->
   <([ th01 - th12 ]~_) :* ([_- th23 ]~ th03)>   -- th02 is shared
   ->
   <([ th01 -_]~ th03 ) :* ([ th12 - th23 ]~_)>  -- th13 is generated
 assoc13 {th23 = th23} {th12 = th12} (v012 ^ v023) with tri th12 th23
 ... | ! v123 with assoc03 (v012 ^ v123)
 ... | v013 ^ v023' with splat splatTri (! v023) (! v023')
 ... | r~ = v013 ^ v123
```

```agda
 io-~ : forall {ga de}(th : ga <= de) -> io -<= th ~ th
 io-~ th with tri io th | io- th
 ... | _ , v | w with splat splatTri (! v) (! w)
 ... | r~ = r~
 
 _~-io : forall {ga de}(th : ga <= de) -> th -<= io ~ th
 _~-io th with tri th io | th -io
 ... | _ , v | w with splat splatTri (! v) (! w)
 ... | r~ = r~
```

