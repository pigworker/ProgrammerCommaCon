# Thinnings

```agda
module Thin.Thin where

open import Lib.Bwd
```

```agda
module _ {X : Set} where
 
 data _<=_ : Bwd X -> Bwd X -> Set where
   _-^_ : forall {ga de} -> ga <= de -> forall x -> ga      <= de -, x
   _-,_ : forall {ga de} -> ga <= de -> forall x -> ga -, x <= de -, x
   []   :                                           []      <= []

 infixl 20 _-^_
 infix  15 _<=_

 _<-_ : X -> Bwd X -> Set
 x <- ga = [] -, x <= ga
```

```agda
 io : forall {ga} -> ga <= ga
 io {[]} = []
 io {ga -, x} = io {ga} -, x

 noth : forall {ga} -> [] <= ga
 noth {[]} = []
 noth {ga -, x} = noth {ga} -^ x
```

```agda
 envPos : forall {ga} -> Env (_<- ga) ga
 envPos {[]} = []
 envPos {ga -, x} = env (_-^ x) envPos -, (noth -, x)
```
