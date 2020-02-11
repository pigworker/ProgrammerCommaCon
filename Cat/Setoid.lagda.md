Setoids
=======

```agda
module Cat.Setoid where

open import Agda.Primitive

open import Lib.Equality
open import Lib.Sigma
```

```agda
record Up {l}(X : Set l) : Set (lsuc l) where -- should have own file
  constructor up
  field
    down : X
open Up public
```

```agda
record Setoid l : Set (lsuc l) where
  field
    Carrier : Set l
    Eq : Carrier -> Carrier -> Set l -- why is this not Splatoid?
    reflEq  : {x : Carrier} -> Eq x x
    symEq   : {x y : Carrier} -> Eq x y -> Eq y x
    transEq : {x y z : Carrier} -> Eq x y -> Eq y z -> Eq x z
```

```agda
module _ where
  open Setoid
  
  Intensional : forall {l}(X : Set l) -> Setoid l
  Carrier (Intensional X) = X
  Eq (Intensional X) = _~_
  reflEq  (Intensional X) = r~
  symEq   (Intensional X) = _~o
  transEq (Intensional X) = _-~-_
```

```agda
  _-Setoid>_ : forall {l} -> Setoid l -> Setoid l -> Setoid l
  Carrier (S -Setoid> T) = (Carrier S -> Carrier T) >< \ f ->
                           forall {s s'} -> Eq S s s' -> Eq T (f s) (f s') 
  Eq (S -Setoid> T) (f , _) (f' , _) = forall {s s'} -> Eq S s s' -> Eq T (f s) (f' s') 
  reflEq  (S -Setoid> T) {f , ok} = ok
  symEq   (S -Setoid> T) ff' ss'  = symEq T (ff' (symEq S ss'))
  transEq (S -Setoid> T) fg gh xz = transEq T (fg (reflEq S)) (gh xz)
```

```agda
  UpS : forall {l} -> Setoid l -> Setoid (lsuc l)
  Carrier (UpS X)          = Up (Carrier X)
  Eq (UpS X) (up x) (up y) = Up (Eq X x y)
  reflEq (UpS X)                  = up (reflEq X)
  symEq (UpS X) (up xy)           = up (symEq X xy)
  transEq (UpS X) (up xy) (up yz) = up (transEq X xy yz)
```
