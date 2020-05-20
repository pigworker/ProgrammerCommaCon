# Backward Lists

```agda
module Lib.Bwd where

open import Lib.Pi
open import Lib.Equality
```

```agda
data Bwd (X : Set) : Set where
  []   : Bwd X
  _-,_ : Bwd X -> X -> Bwd X

_-+_ : forall {X} -> Bwd X -> Bwd X -> Bwd X
xz -+ [] = xz
xz -+ (yz -, y) = xz -+ yz -, y

infixl 20 _-,_ _-+_ _-%_

assoc-+-+ : forall {X}(xz yz zz : Bwd X)
  -> (xz -+ (yz -+ zz)) ~ (xz -+ yz -+ zz)
assoc-+-+ xz yz [] = r~
assoc-+-+ xz yz (zz -, z) = _-, z $~ assoc-+-+ xz yz zz

_-%_ : forall {X} -> Bwd X -> Bwd X -> Bwd X
xz -% [] = xz
xz -% (yz -, y) = xz -, y -% yz

bwdRev : forall {X} -> Bwd X -> Bwd X
bwdRev xz = [] -% xz

assoc-%-+ : forall {X}(xz zz yz : Bwd X)
         -> (xz -% (zz -+ yz)) ~ (xz -% yz -% zz)
assoc-%-+ xz yz [] = r~
assoc-%-+ xz yz (zz -, x) = assoc-%-+ (xz -, x) yz zz
```


Environments are "All" for backward lists.

```agda
module _ {X : Set} where

 data Env (P : X -> Set) : Bwd X -> Set where
   []   : Env P []
   _-,_ : forall {xz x} -> Env P xz -> P x -> Env P (xz -, x)

 purE : forall {P} -> [ P ] -> [ Env P ]
 purE p {[]} = []
 purE p {xz -, x} = purE p {xz} -, p {x}

 infixl 20 _$E_
 _$E_ : forall {P Q} -> [ Env (P -:> Q) -:> Env P -:> Env Q ]
 [] $E [] = []
 (fz -, f) $E (pz -, p) = fz $E pz -, f p

 env : forall {P Q} -> [ P -:> Q ] -> [ Env P -:> Env Q ]
 env f pz = purE f $E pz

 top : forall {P xz x} -> Env P (xz -, x) -> P x
 top (pz -, p) = p
```
