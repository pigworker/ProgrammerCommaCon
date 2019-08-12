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
```

```agda
DesignTy : TermDesign
TermDesign.BindSort DesignTy = Zero
TermDesign.TermSort DesignTy = One
TermDesign.bindTerm DesignTy ()
TermDesign.Constructor DesignTy <> = DatTwo
TermDesign.ConArgs DesignTy ff = One'
TermDesign.ConArgs DesignTy tt = # <> *' # <>

Ty : Set
Ty = Term DesignTy <> []

-- base : Ty
pattern base = ff $ <>

-- _-Ty>_ : Ty -> Ty -> Ty
pattern _-Ty>_ S T = tt $ (S , T)
```
