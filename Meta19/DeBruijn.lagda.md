# A Universe of DeBruijn Syntaxes

This is, to be frank, a bait-and-switch operation...

```agda
module Meta19.DeBruijn where

open import Lib.Zero
open import Lib.One
open import Lib.Sigma
open import Lib.Equality
open import Lib.Pi
open import Lib.Sum
open import Lib.Bwd
open import Lib.Datoid
open import Thin.Thin
```

```agda
data Args (B I : Set) : Set where
  #    : I -> Args B I
  One' : Args B I
  _*'_ : Args B I -> Args B I -> Args B I
  _|-'_ : B -> Args B I -> Args B I

Tuple : {B I : Set} -> (I -> Bwd B -> Set) -> Args B I -> Bwd B -> Set
Tuple X (# i)     ga = X i ga
Tuple X One'      ga = One
Tuple X (S *' T)  ga = Tuple X S ga * Tuple X T ga
Tuple X (b |-' T) ga = Tuple X T (ga -, b)
```

```agda
record TermDesign : Set1 where
  field
    BindSort : Set
    TermSort : Set
    bindTerm : BindSort -> TermSort
    Constructor : TermSort -> Datoid
    ConArgs : {i : TermSort} -> Data (Constructor i) -> Args BindSort TermSort
```

```agda
module _ (D : TermDesign) where

 open TermDesign D

 data Term (i : TermSort)(ga : Bwd BindSort) : Set where
   var : forall {b} ->  b <- ga  -> bindTerm b ~ i -> Term i ga
   _$_ : (c : Data (Constructor i)) -> Tuple Term (ConArgs c) ga -> Term i ga

 DatTerm : (T : Args BindSort TermSort)(ga : Bwd BindSort) -> Datoid
 Data (DatTerm T ga) = Tuple Term T ga
 eq? (DatTerm (# i) ga) (var x r~) (var y q) with eq? (Dat<= _) (! x) (! y)
 eq? (DatTerm (# _) ga) (var x r~) (var y q)   | inl n = inl \ { r~ -> n r~ }
 eq? (DatTerm (# _) ga) (var x r~) (var .x r~) | inr r~ = inr r~
 eq? (DatTerm (# i) ga) (var _ _) (_ $ _) = inl \ ()
 eq? (DatTerm (# i) ga) (c $ _) (var _ _) = inl \ ()
 eq? (DatTerm (# i) ga) (c $ x) (d $ y) with eq? (Constructor i) c d
 eq? (DatTerm (# i) ga) (c $ x) (d $ y)   | inl n = inl \ { r~ -> n r~ }
 eq? (DatTerm (# i) ga) (c $ x) (.c $ y)  | inr r~ with eq? (DatTerm (ConArgs c) ga) x y
 eq? (DatTerm (# i) ga) (c $ x) (.c $ y)  | inr r~ | inl n = inl \ { r~ -> n r~ }
 eq? (DatTerm (# i) ga) (c $ x) (.c $ .x) | inr r~ | inr r~ = inr r~
 eq? (DatTerm One' ga) <> <> = inr r~
 eq? (DatTerm (S *' T) ga) (s0 , t0) (s1 , t1) with eq? (DatTerm S ga) s0 s1
 eq? (DatTerm (S *' T) ga) (s0 , t0) (s1 , t1)   | inl n = inl \ { r~ -> n r~ }
 eq? (DatTerm (S *' T) ga) (s0 , t0) (.s0 , t1)  | inr r~ with eq? (DatTerm T ga) t0 t1
 eq? (DatTerm (S *' T) ga) (s0 , t0) (.s0 , t1)  | inr r~ | inl n = inl \ { r~ -> n r~ }
 eq? (DatTerm (S *' T) ga) (s0 , t0) (.s0 , .t0) | inr r~ | inr r~ = inr r~
 eq? (DatTerm (b |-' T) ga) t0 t1 = eq? (DatTerm T (ga -, b)) t0 t1

open TermDesign
```

```agda
DesignTy : TermDesign
BindSort    DesignTy = Zero
TermSort    DesignTy = One
bindTerm    DesignTy ()
Constructor DesignTy <> = DatTwo
ConArgs     DesignTy ff = One'
ConArgs     DesignTy tt = # <> *' # <>

Ty : Set
Ty = Term DesignTy <> []

-- base : Ty
pattern base = ff $ <>

-- _-Ty>_ : Ty -> Ty -> Ty
pattern _-Ty>_ S T = tt $ (S , T)

DesignTm : TermDesign
BindSort    DesignTm = Ty
TermSort    DesignTm = Ty
bindTerm    DesignTm T = T
Constructor DesignTm = {!!}
ConArgs     DesignTm = {!!}
```
