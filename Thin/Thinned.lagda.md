# Thinned Things

```agda
module Thin.Thinned where

open import Lib.Sigma
open import Lib.Pi
open import Lib.Bwd
open import Thin.Thin
open import Thin.Triangle
```

```agda
module _ {X : Set} where

 _:^_ : (Bwd X -> Set) -> (Bwd X -> Set)
 T :^ de = < T :* (_<= de) >

 support : forall {T ga} -> T :^ ga -> Bwd X
 support = fst

 thing : forall {T ga}(t : T :^ ga) -> T (support t)
 thing = snd - fst

 thinning : forall {T ga}(t : T :^ ga) -> support t <= ga
 thinning = snd - snd

 Kripke : (Bwd X -> Set) -> (Bwd X -> Set)
 Kripke T ga = [ (ga <=_) -:> T ]

 _:-_ : {T : Bwd X -> Set} -> [ (T :^_) -:> Kripke (T :^_) ]
 (t ^ th) :- ph = t ^ (th -<= ph)

 _$:_ : {S T : Bwd X -> Set} -> [ S -:> T ] -> [ (S :^_) -:> (T :^_) ]
 f $: (s ^ th) = f s ^ th
```

```agda
 Relevant : ((X -> Set) -> Bwd X -> Set) -> Set1
 Relevant F = forall {P} -> [ F P -:> Env P ]
```
