# Thinnings

```agda
module Thin.Thin where

open import Lib.Bwd
open import Lib.Sum
open import Lib.Sigma
open import Lib.Equality
open import Lib.Datoid
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
 nothU : forall {ga}(th ph : [] <= ga) -> th ~ ph
 nothU (th -^ x) (ph -^ .x) with nothU th ph
 ... | r~ = r~
 nothU [] [] = r~
```


```agda
 envPos : forall {ga} -> Env (_<- ga) ga
 envPos {[]} = []
 envPos {ga -, x} = env (_-^ x) envPos -, (noth -, x)
```

```agda
 Dat<= : Bwd X -> Datoid
 Data (Dat<= de) = <(_<= de)>
 eq? (Dat<= ._) (! th -^ x) (! ph -^ .x) with eq? (Dat<= _) (! th) (! ph)
 eq? (Dat<= .(_ -, x)) (! th -^ x) (! ph -^ .x) | inl n = inl \ { r~ -> n r~ }
 eq? (Dat<= .(_ -, x)) (! th -^ x) (! .th -^ .x) | inr r~ = inr r~
 eq? (Dat<= ._) (! th -^ x) (! ph -, .x) = inl \ ()
 eq? (Dat<= ._) (! th -, x) (! ph -^ .x) = inl \ ()
 eq? (Dat<= ._) (! th -, x) (! ph -, .x) with eq? (Dat<= _) (! th) (! ph)
 eq? (Dat<= ._) (! th -, x) (! ph -, .x) | inl n = inl \ { r~ -> n r~ }
 eq? (Dat<= ._) (! th -, x) (! .th -, .x) | inr r~ =
   inr r~
 eq? (Dat<= .[]) (! []) (! []) = inr r~
```
