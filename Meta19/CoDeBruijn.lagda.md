# A Universe of Co de Bruijn Syntaxes

Instead of keeping information about variable *non-*usage at the *leaves* of our
syntax trees, let us keep it as close as possible to the *root*.

This will involve a more sophisticated invariant, but we have the firepower.


```agda
module Meta19.CoDeBruijn where
open import Lib.One
open import Lib.Sum
open import Lib.Sigma
open import Lib.Pi
open import Lib.Equality
open import Lib.Bwd
open import Lib.Splatoid
open import Lib.Datoid
open import Thin.Thin
open import Thin.Cover
open import Thin.Bind
open import Thin.Thinned
open import Thin.Triangle
open import Thin.Pullback
open import Thin.PullCover
open import Thin.Parti
open import Thin.Select

open import Meta19.DeBruijn
```


## The Construction

`Args` stays the same.

```reminder
data Args (B I : Set) : Set where
  #     : I -> Args B I                     -- ... a subterm of a given sort;
  One'  : Args B I                          -- ... nothing;
  _*'_  : Args B I -> Args B I -> Args B I  -- ... a pair;
  _|-'_ : B -> Args B I -> Args B I         -- ... something in the scope of a binder.
```

`TermDesign` stays the same, so our examples survive.

```reminder
record TermDesign : Set1 where
  field
    TermSort    : Set   -- what sorts of terms exist?
    BindSort    : Set   -- what sorts of binders exist?
    bindTerm    : BindSort -> TermSort  -- what sort of terms does
                                        --   each sort of binder bind?
    Constructor : TermSort -> Datoid  -- constructors for each sort
    ConArgs     : {i : TermSort} -> Data (Constructor i)
                                 -> Args BindSort TermSort
                                 -- arguments for each constructor
  SubTmSort : Set   -- a definition, not a field
  SubTmSort = Args BindSort TermSort
  Scope : Set
  Scope = Bwd BindSort
```

See below for the type of terms. Or rather `Trrm`s, being the relevance-aware
terms. Read `Bwd B` as the type of a term's *support* (the things it actually
needs) rather than its *scope* (the things it's allowed to use). It's in
the interpretation of argument structures that we do the work.

```agda
Tight : {B I : Set} ->        (I -> Bwd B -> Set)
                    -> (Args B I -> Bwd B -> Set)
Tight X (# i)     = X i
Tight X One'      = (_~ [])
Tight X (S *' T)  = Tight X S /*\ Tight X T
Tight X (b |-' T) = b |- Tight X T
```


```agda
{-(-}
module _ (D : TermDesign) where

 open TermDesign D

 data Trrm (i : TermSort)(ga : Bwd BindSort) : Set where
   var : Only (\ b -> bindTerm b ~ i) ga -> Trrm i ga
   _$_ : (c : Data (Constructor i)) -> Tight Trrm (ConArgs c) ga -> Trrm i ga
 infix 1 _$_  -- very low priority, deliberately weaker than pairing

 CdB : TermSort -> Scope -> Set
 CdB i ga = Trrm i :^ ga

 SubCdB : SubTmSort -> Scope -> Set
 SubCdB T ga = Tight Trrm T :^ ga

{-)-}
```
