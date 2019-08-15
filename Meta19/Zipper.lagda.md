# The Zipper

```agda
module Meta19.Zipper where
open import Lib.Zero
open import Lib.One
open import Lib.Equality
open import Lib.Sum
open import Lib.Sigma
open import Lib.Bwd
open import Lib.Datoid
open import Lib.Splatoid
open import Thin.Thin
open import Thin.Parti
open import Meta19.DeBruijn
```

```agda
Log LogGo : forall {B I} -> Args B I -> Bwd B -> Args B I -> Bwd B -> Datoid
Log   T         ga H de = LogGo T ga H de +D+ DatSplat (SplatEq (ga , T) (de , H))
LogGo (# i)     ga H de = DatZero
LogGo One'      ga H de = DatZero
LogGo (S *' T)  ga H de = Log S ga H de +D+ Log T ga H de
LogGo (b |-' T) ga H de = Log T (ga -, b) H de 
```

```agda
stub :   forall {B I}{ga de : Bwd B}(T : Args B I){H : Args B I} ->
         Data (Log T ga H de) -> Args B I
stubGo : forall {B I}{ga de : Bwd B}(T : Args B I){H : Args B I} ->
         Data (LogGo T ga H de) -> Args B I
stub T (inl x) = stubGo T x
stub T (inr x) = One'
stubGo (S *' T) (inl x) = stub S x *' T
stubGo (S *' T) (inr x) = S *' stub T x
stubGo (b |-' T) x      = b |-' stub T x
```

```agda
plug :  forall {B I}{X : I -> Bwd B -> Set}
        {ga de : Bwd B}(T : Args B I){H : Args B I}
     -> (x : Data (Log T ga H de)) -> Tuple X (stub T x) ga -> Tuple X H de
     -> Tuple X T ga
plugGo :  forall {B I}{X : I -> Bwd B -> Set}
          {ga de : Bwd B}(T : Args B I){H : Args B I}
       -> (x : Data (LogGo T ga H de)) -> Tuple X (stubGo T x) ga -> Tuple X H de
       -> Tuple X T ga
plug   T         (inl x)   t'       h = plugGo T x t' h
plug   T         (inr r~)  <>       h = h
plugGo (S *' T)  (inl x)   (s' , t) h = plug S x s' h , t
plugGo (S *' T)  (inr x)   (s , t') h = s , plug T x t' h
plugGo (b |-' T) x         t'       h = plug T x t' h
```

```agda
module _ (D : TermDesign) where
 open TermDesign D

 Jacobian : TermSort -> Scope -> TermSort -> Scope -> Set
 Jacobian i ga j de =
   Data (Constructor i) >< \ c -> Data (Log (ConArgs c) ga (# j) de) >< \ x ->
   SubTm D (stub (ConArgs c) x) ga

 plugTerm : forall {i ga j de} -> Jacobian i ga j de -> Term D j de -> Term D i ga
 plugTerm (c , x , t') h = c $ plug (ConArgs c) x t' h

 data Zipper (i : TermSort)(ga : Scope) : TermSort -> Scope -> Set where
   []   : Zipper i ga i ga
   _-,_ : forall {j de k ze} ->
          Zipper i ga j de -> Jacobian j de k ze -> Zipper i ga j ze
```
