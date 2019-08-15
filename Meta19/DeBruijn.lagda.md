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
open import Lib.Splatoid
open import Lib.Datoid
open import Thin.Thin
open import Thin.Triangle
```

## The Multisorted Universe

0. Read this section from bottom to top. I've numbered the paragraphs in presentation
order. Scroll down...

3. We write a datatype of *scoped* tuple descriptions. The parameters `B` and `I` will
be instantiated with `BindSort` and `TermSort`, respectively. You can read each
constructor as *asking for* ...

```agda
data Args (B I : Set) : Set where
  #     : I -> Args B I                     -- ... a subterm of a given sort;
  One'  : Args B I                          -- ... nothing;
  _*'_  : Args B I -> Args B I -> Args B I  -- ... a pair;
  _|-'_ : B -> Args B I -> Args B I         -- ... something in the scope of a binder.
```

4. Now that we have coded up the argument tuple structures, we must interpret it.
If we know what scope-indexed type family interprets each term sort, we can say
what scope-indexed type family interprets each tuple structure.

```agda
Tuple : {B I : Set} ->        (I -> Bwd B -> Set)
                    -> (Args B I -> Bwd B -> Set)
Tuple X (# i)     ga = X i ga
Tuple X One'      ga = One
Tuple X (S *' T)  ga = Tuple X S ga * Tuple X T ga
Tuple X (b |-' T) ga = Tuple X T (ga -, b)
```

2. A `TermDesign` controls what is represented in a syntax. We're
building multisorted syntaxes, so we need to say what the sorts are.
Perhaps only some of the sorts admit variables, so we separate a
notion of *binding sort*, which tells us how to *bind* a variable,
together with a `bindTerm` function which maps binding sorts to the
term sort you get when you *use* a variable.

For each term sort, we give the `Datoid` (a `Set` with decidable
equality) of its constructors. Note that if `D : Datoid`, then
`Data D : Set` is the type of its elements.

Then, for each constructor of each sort, we specify the tuple of
arguments it expects.

```agda
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

1. The type of terms is parametrized by a `TermDesign`, the details of
which we'll explore in a moment.

The type is indexed
* by a `TermSort`, `i`, which is the sort of term to be constructed
  (the nonterminal symbol in the grammar, if you like), and
* by a *scope*: a backward list recording the history of the binders we
  have gone under.

There are two constructors: `var` for variables and `_$_` for everything
else. Part of the plan is to ensure that variables get treated uniformly for
all our syntaxes.
* The `var` constructor selects *one* binder from the scope, then checks
  that the selected binder binds a variable in a suitable sort. We may add a
  pattern synonym to hide the latter.
* The `_$_` operator takes
  (on the left) a constructor appropriate to the `TermSort` being targeted and
  (on the right) a tuple of arguments appropriate to the constructor.

```agda
module _ (D : TermDesign) where

 open TermDesign D

 data Term (i : TermSort)(ga : Bwd BindSort) : Set where
   var : forall {b} ->  b <- ga  -> bindTerm b ~ i -> Term i ga
   _$_ : (c : Data (Constructor i)) -> Tuple Term (ConArgs c) ga -> Term i ga
 infix 1 _$_  -- very low priority, deliberately weaker than pairing

 pattern va x = var x r~
```

5. Here's a move which will very shortly be useful, when it comes to talking
about *parts* of terms, which we will need to do if we are to define operations
on terms. We exploit the `#` embedding from `TermSort` to `SubTmSort` to treat
the latter as classifying the subterms we will encounter.

```agda
 SubTm : SubTmSort -> Bwd BindSort -> Set
 SubTm T ga = Tuple Term T ga
```

## Decidable Equality

We may equip *all* our syntaxes with an equality decision procedure. That is,
we make every sort of *sub*term a `Datoid`. The *sub* is important: the
equality test must proceed by mutual recursion over the *sub*term sorts.

```agda
 DatTerm : (T : SubTmSort)(ga : Scope) -> Datoid
 Data (DatTerm T ga) = SubTm T ga
 ```

Consider the actual *term* sorts:

```agda
 -- constructors and variables are distinct
 eq? (DatTerm (# i) ga) (var _ _) (_ $ _) = inl \ ()
 eq? (DatTerm (# i) ga) (c $ _) (var _ _) = inl \ ()

 -- for two variables, compare thinnings: we cope with the fact that
 -- `x` and `y` might have different `BindSort`s by existential hiding
 eq? (DatTerm (# i) ga) (var x p) (var y q) with eq? (Dat<= _) (! x) (! y)
 eq? (DatTerm (# _) ga) (var x p) (var y q)    | inl n = inl \ { r~ -> n r~ }
 eq? (DatTerm (# _) ga) (var x r~) (var .x r~) | inr r~ = inr r~

-- for constructors, compare constructors, and if they match, compare arguments
 eq? (DatTerm (# i) ga) (c $ x) (d $ y) with eq? (Constructor i) c d
 eq? (DatTerm (# i) ga) (c $ x) (d $ y)   | inl n = inl \ { r~ -> n r~ }
 eq? (DatTerm (# i) ga) (c $ x) (.c $ y)  | inr r~ with eq? (DatTerm (ConArgs c) ga) x y
 eq? (DatTerm (# i) ga) (c $ x) (.c $ y)  | inr r~ | inl n = inl \ { r~ -> n r~ }
 eq? (DatTerm (# i) ga) (c $ x) (.c $ .x) | inr r~ | inr r~ = inr r~
```

Consider empty tuples: they are equal.

```agda
 eq? (DatTerm One' ga) <> <> = inr r~
```

Consider pairs: test them componentwise.

```agda
 eq? (DatTerm (S *' T) ga) (s0 , t0) (s1 , t1) with eq? (DatTerm S ga) s0 s1
 eq? (DatTerm (S *' T) ga) (s0 , t0) (s1 , t1)   | inl n = inl \ { r~ -> n r~ }
 eq? (DatTerm (S *' T) ga) (s0 , t0) (.s0 , t1)  | inr r~ with eq? (DatTerm T ga) t0 t1
 eq? (DatTerm (S *' T) ga) (s0 , t0) (.s0 , t1)  | inr r~ | inl n = inl \ { r~ -> n r~ }
 eq? (DatTerm (S *' T) ga) (s0 , t0) (.s0 , .t0) | inr r~ | inr r~ = inr r~
```

Consider binders: just bring the binder into scope!

```agda
 eq? (DatTerm (b |-' T) ga) t0 t1 = eq? (DatTerm T (ga -, b)) t0 t1
```


## Example: Untyped Lambda Calculus

Before we begin, let us locally open the `TermDesign` module, which
brings its field names into scope as *projection functions*.

```agda
module ULAM where
 open TermDesign
```

Let us construct the syntax of untyped lambda-terms. We get variables for free, so
we need only explain how *applications* and *abstractions* are formed.

```agda
 DesignULam : TermDesign
 TermSort    DesignULam = One
 BindSort    DesignULam = One
 bindTerm    DesignULam <> = <>
 Constructor DesignULam <> = DatTwo
 ConArgs     DesignULam ff = # <> *' # <>   -- application has two subterms
 ConArgs     DesignULam tt = <> |-' # <>    -- lambda has one subterm under a binder

 ULam : Bwd One -> Set
 ULam ga = Term DesignULam <> ga
```

Sensible people build readable constructors as typed *definitions*, then comment out
the types and make them pattern synonyms.

```agda
-- appU : forall {ga} -> ULam ga -> ULam ga -> ULam ga
 pattern _$U_ f s = ff $ f , s
 infixl 6 _$U_  -- "application associates to the left,
               --  rather as we all did in the sixties"
               --     Roger Hindley

-- lamU : forall {ga} -> ULam (ga -, <>) -> ULam ga
 pattern \\U_ t = tt $ t
 infixr 5 \\U_
```

Let us build the Church numeral for 2.
```agda
{-+}
 church2U : forall {ga} -> ULam ga
 church2U = ?
{+-}
```

```stashed
 church2U : forall {ga} -> ULam ga
 church2U = \\U \\U va (noth -, <> -^ <>) $U
                         (va (noth -, <> -^ <>) $U va (noth -, <>))
```

Note to non-Cylons: the signal in a variable is the `,` and the `^`s.
They show you *spatially* to which binder they point, left-to-right.


## Example: Simply Typed Lambda Calculus

```agda
module STLAM where
 open TermDesign
```

First, we build the simple types. These have one sort and no binders.
There is a base constructor and an arrow constructor.

```agda
 DesignTy : TermDesign
 TermSort    DesignTy = One
 BindSort    DesignTy = Zero
 bindTerm    DesignTy ()
 Constructor DesignTy <> = DatTwo
 ConArgs     DesignTy ff = One'
 ConArgs     DesignTy tt = # <> *' # <>

 Ty : Set
 Ty = Term DesignTy <> []

 DatTy : Datoid
 Data DatTy = Ty
 eq?  DatTy = eq? (DatTerm DesignTy (# <>) [])

-- base : Ty
 pattern base = ff $ <>

-- _-Ty>_ : Ty -> Ty -> Ty
 pattern _-Ty>_ S T = tt $ (S , T)
```

It will be useful to write the type of evidence for arrowhood.

```agda
 IsArrow : Ty -> Splatoid
 IsArrow base        = SplatZero
 IsArrow (S -Ty> T)  = SplatOne
```

(A `Splatoid`, or &lsquo;mere proposition&rsquo;, a set with at most one
elements. Every `Splatoid` is trivially a `Datoid`.)

Now, we're ready to build terms.

```agda
 DesignTm : TermDesign
 TermSort    DesignTm = Ty     -- *types* are the sorts of terms
 BindSort    DesignTm = Ty     -- abstraction is permitted at any type
 bindTerm    DesignTm T = T
 Constructor DesignTm T
   =    DatTy                  -- application needs to carry the argument type
   +D+  DatSplat (IsArrow T)   -- lambda insists on an arrow type
 ConArgs DesignTm {T}        (inl S)  = # (S -Ty> T) *' # S
 ConArgs DesignTm {S -Ty> T} (inr <>) = S |-' # T
```

We can have package neatly.

```agda
 infix 4 _:-_
 _:-_ : Bwd Ty -> Ty -> Set
 Ga :- T = Term DesignTm T Ga

 infixl 6 _$T_
 _$T_ : forall {Ga S T} -> Ga :- S -Ty> T -> Ga :- S -> Ga :- T
 f $T s = inl _ $ f , s

 infixr 5 \\T_
 \\T_ : forall {Ga S T} -> Ga -, S :- T -> Ga :- S -Ty> T
 \\T t = inr <> $ t
```

Let's have Church Two again.

```agda
{-+}
 church2 : forall {Ga T} -> Ga :- ((T -Ty> T) -Ty> (T -Ty> T))
 church2 = ?
{+-}
```

```stashed
 church2 = \\T \\T va (noth -, _ -^ _) $T
                    (va (noth -, _ -^ _) $T va (noth -, _))
```


## Substitution (First Attempt)

Fix a `TermDesign`.

```agda
module SUBST-FAIL (D : TermDesign) where
 open TermDesign D

 postulate IWant : (This : Set) -> This  -- for pretending to solve a problem.
```

A substitution is a *sort-respecting* map from variables in one scope
to terms over another.

```agda
 Subst : Scope -> Scope -> Set
 Subst ga de = forall {b} ->  b <- ga  -> Term D (bindTerm b) de
```

Let's try to push a substitution through all the subterm sorts.

```agda
{-+}
 subst : forall {ga de} T -> SubTm D T ga -> Subst ga de -> SubTm D T de
 subst T t sg = {!!}
{+-}
```


```stashed
 subst          (# i)     (va x)  sg = sg x
 subst          (# i)     (c $ t) sg = c $ subst (ConArgs c) t sg
 subst          One'      <>      sg = <>
 subst          (S *' T)  (s , t) sg = subst S s sg , subst T t sg
 subst {ga}{de} (b |-' T) t       sg = subst T t \
   { (x -, b) -> va (noth -, b)
   ; (x -^ b) -> IWant (Term D _ de -> Term D _ (de -, b)) (sg x)
   }                -- I need to do a de Bruijn shift!
```


## Thin All The Things

Let's do that in new module that we want to keep.

```agda
module _ (D : TermDesign) where
 open TermDesign D

 postulate IWant : (This : Set) -> This  -- for pretending to solve a problem.
```

We represented variables in `ga` by thinnings into `ga`. So, by
construction, thinnings act on terms by composition. It is remarkably
useful that scope extension is a functor on thinnings, because we
need exactly that functor when we go under a binder.

```agda
{-+}
 thin : forall {ga de} T -> SubTm D T ga -> ga <= de -> SubTm D T de
 thin T t th = ?
{+-}
```

```stashed
 thin : forall {ga de} T -> SubTm D T ga -> ga <= de -> SubTm D T de
 thin (# i)     (va x)  th = va (x -<= th)
 thin (# i)     (c $ t) th = c $ thin (ConArgs c) t th
 thin One'      <>      th = <>
 thin (S *' T)  (s , t) th = thin S s th , thin T t th
 thin (b |-' T) t       th = thin T t (th -, b)
```

Now we have the missing ingredient!


## Substitution (Second Attempt)

```agda
{-+}
 Subst : Scope -> Scope -> Set
 Subst ga de = forall {b} ->  b <- ga  -> Term D (bindTerm b) de

 subst : forall {ga de} T -> SubTm D T ga -> Subst ga de -> SubTm D T de
 subst (# i) (va x)     sg = sg x
 subst (# i) (c $ t)    sg = c $ subst (ConArgs c) t sg
 subst One'      <>     sg = <>
 subst (S *' T) (s , t) sg = subst S s sg , subst T t sg
 subst (b |-' T) t sg = subst T t \
   { (x -, b) -> va (noth -, b)
   ; (x -^ b) -> thin (# _) (sg x) (io -^ b)
   }
{+-}
```


## Discussion

The implementations of `thin` and `subst` are very similar. It is, of
course, possible to abstract out their common structure.

What we can't escape from so easily is that we have to traverse whole
terms to observe that the newly bound variable is used nowhere. That is
because the information about variable *non*-usage is stored in the
leaves of the tree. Might we do better?
