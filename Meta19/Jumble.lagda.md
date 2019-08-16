# A Universe of Co de Bruijn Syntaxes

Instead of keeping information about variable *non-*usage at the *leaves* of our
syntax trees, let us keep it as close as possible to the *root*.

This will involve a more sophisticated invariant, but we have the firepower.


```agda
module Meta19.Jumble where
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

 module SUBST where

  Naive : Scope -> Scope -> Set
  Naive ga de = forall {b} ->  b <- ga  -> CdB (bindTerm b) de

  weaken : forall {ga de} -> Naive ga de -> forall b -> Naive (ga -, b) (de -, b)
  weaken sg b (x -, .b) = var (only r~) ^ noth -, b
  weaken sg b (x -^ .b) = sg x :- (io -^ b)

  naive : forall {ga de} T -> Tight Trrm T :^ ga -> Naive ga de -> Tight Trrm T :^ de
  worker : forall {ga de} T -> Tight Trrm T ga -> Naive ga de -> SubCdB T de
   
  naive T (t ^ th) sg = worker T t ((_-<= th) - sg)
  
  worker (# _) (var (only r~)) sg = sg ([] -, _)
  worker (# i) (c $ t) sg = (c $_) $: worker (ConArgs c) t sg
  worker One' r~ sg = r~ ^ noth
  worker (S *' T) (rp s t u) sg = naive S s sg /,\ naive T t sg
  worker (b |-' T) (kk t) sg = kk $: worker T t sg
  worker (b |-' T) (ll t) sg = \\ worker T t (weaken sg b)


  data Substitute : forall T {ga de} ->
       SubCdB T ga -> Naive ga de -> SubCdB T de -> Set
    where

    var : forall {b ga de}(x : b <- ga) -> {sg : Naive ga de} ->
          Substitute (# (bindTerm b)) (var (only r~) ^ x) sg (sg x)

    _$_ : forall {i ga de}(c : Data (Constructor i)){sg : Naive ga de}
          {t : SubCdB (ConArgs c) ga}{t' : SubCdB (ConArgs c) de}
       -> Substitute (ConArgs c) t sg t'
       -> Substitute (# i) ((c $_) $: t) sg ((c $_) $: t')

    <>  : forall {ga de}{sg : Naive ga de}
       -> Substitute One' (r~ ^ noth) sg (r~ ^ noth)

    pr  : forall {S T ga de}{sg : Naive ga de}
            {s  : SubCdB S ga}{t  : SubCdB T ga}{st  : SubCdB (S *' T) ga}
            {s' : SubCdB S de}{t' : SubCdB T de}{st' : SubCdB (S *' T) de}
         -> Pair s t st
         -> Substitute S s sg s'
         -> Substitute T t sg t'
         -> Pair s' t' st'
         -> Substitute (S *' T) st sg st'
      
    kk  : forall {b T ga de}{sg : Naive ga de}
          {t :  SubCdB T ga}{t' : SubCdB T de} 
       -> Substitute T t sg t'
       -> Substitute (b |-' T) (kk $: t) sg (kk $: t')

    ll  : forall {b T ga0 ga de0 de}{sg : Naive ga de}
          {t :  Tight Trrm T (ga0 -, b)}{th : ga0 <= ga}
          {t' : Tight Trrm T (de0 -, b)}{ph : de0 <= de}
       -> Substitute T (t ^ th -, b) (weaken sg b) (t' ^ ph -, b)
       -> Substitute (b |-' T) (ll t ^ th) sg (ll t' ^ ph)


  module _ {ga0 ga de0 de}(th : ga0 <= ga)(sg : Naive ga de)(ph : de0 <= de)
   where
   Relev : Set
   Relev = forall {b}(x : b <- ga0) x' -> [ x - th ]~ x' ->
     <([_- ph ]~ thinning (sg x'))>

  sbRelv : forall {T ga0 ga de0 de}{th : ga0 <= ga}{sg : Naive ga de}{ph : de0 <= de}
                  {t : Tight Trrm T ga0}{t' : Tight Trrm T de0} ->
             Substitute T (t ^ th) sg (t' ^ ph) -> Relev th sg ph
  sbRelv (var x) ([] -, _) _ xv with splat splatTri (! xv) (! io- x)
  ... | r~ = ! io- _
  sbRelv (c $ sb) _ _ xv = sbRelv sb _ _ xv
  sbRelv {sg = sg} (pr (pair _ _ (! vl , u , vr))
                       sbl sbr
                       (pair _ _ (! wl , _ , wr)))
                   x x' xv
    with oneCover x u
  sbRelv {sg = sg} (pr (pair _ _ (! vl , u , vr))
                       sbl sbr
                       (pair _ _ (! wl , ! wr))) x x' xv
    | inl (! xl) with assoc03 (xl ^ vl)
  ... | xl' ^ xv' with splat splatTri (! xv) (! xv')
  ... | r~  with sg x' | sbRelv sbl _ _ xl'
  ... | _ ^ th | ! w with assoc02 (w ^ wl)
  ... | w0 ^ w1 = ! w1
  sbRelv {sg = sg} (pr (pair _ _ (! vl , u , vr))
                       sbl sbr
                       (pair _ _ (! wl , ! wr))) x x' xv
    | inr (! xr) with assoc03 (xr ^ vr)
  ... | xr' ^ xv' with splat splatTri (! xv) (! xv')
  ... | r~  with sg x' | sbRelv sbr _ _ xr'
  ... | _ ^ th | ! w with assoc02 (w ^ wr)
  ... | w0 ^ w1 = ! w1
  sbRelv (kk sb) _ _ xv = sbRelv sb _ _ xv
  sbRelv {sg = sg} (ll sb) x x' xv with sg x' | sbRelv sb _ _ (xv -^, _)
  ... | _ ^ th | ! z -^, _ rewrite th ~-io = ! z

  naiveS  : forall {ga de} T
            (t : Tight Trrm T :^ ga)(sg : Naive ga de) ->
            < Substitute T t sg >
  workerS : forall {ga0 ga de} T
            (t : Tight Trrm T ga0)(th : ga0 <= ga)(sg : Naive ga de) ->
            < Substitute T (t ^ th) sg >
  naiveS  T (t ^ th) sg = workerS T t th sg
  workerS (# i) (var (only r~)) th sg = ! var th
  workerS (# i) (c $ t) th sg with workerS (ConArgs c) t th sg
  ... | ! t' = ! (c $ t')
  fst (workerS One' r~ th sg) = _
  snd (workerS One' r~ th sg) rewrite noth~ th noth = <>
  workerS (S *' T) (rp (s ^ th0) (t ^ th1) u) th sg with tri th0 th | tri th1 th
  ... | ph0 , v0 | ph1 , v1 with workerS S s ph0 sg | workerS T t ph1 sg
  ... | ! s' | ! t' = ! pr (pair s t (! v0 , u , v1)) s' t' (snd (mkPair _ _))
  workerS (b |-' T) (kk t) th sg with workerS T t th sg
  ... | ! t' = ! kk t'
  workerS (b |-' T) (ll t) th sg with workerS T t (th -, b) (weaken sg b)
  workerS (b |-' T) (ll t) th sg | _ ^ (ph -, .b) , t' = ! ll t'
  workerS (b |-' T) (ll t) th sg | _ ^ ph -^ .b , t' with sbRelv t' _ _ (noth- th -, b)
  workerS (b |-' T) (ll t) th sg | _ ^ ph -^ .b , t' | ! ()
   

  record SplitSub (ga de : Scope) : Set where
    field
      passive active : Scope
      parti          : passive <-[ ga ]-> active
      passiveThin    : passive <= de
      activeSb       : Env (\ b -> CdB (bindTerm b) de) active

    hit : forall {b} -> b <- ga -> CdB (bindTerm b) de
    hit x with oneCover x (lrcov parti)
    hit x | inl (y , v) = var (only r~) ^ (y -<= passiveThin)
    hit x | inr (y , v) with y <? activeSb
    ... | [] -, t = t

  open SplitSub public

  _<?s_ : forall {ze ga de}(th : ze <= ga)(sg : SplitSub ga de) -> SplitSub ze de
  th <?s record { passive = pa ; active = ac ;
                  parti = ti ; passiveThin = ph ; activeSb = tz }
    with selParti th ti
  ... | (pa' , ac') , ti' , (ph' , th') , b
    = record
        { passive     = pa'
        ; active      = ac'
        ; parti       = ti'
        ; passiveThin = ph' -<= ph
        ; activeSb    = th' <? tz
        }

  wkSplitSub : forall {ga de}(sg : SplitSub ga de) b -> SplitSub (ga -, b) (de -, b)
  wkSplitSub record
      { passive      = pa
      ; active       = ac
      ; parti        = record { lrcov = u ; lrdis = d }
      ; passiveThin  = ph
      ; activeSb     = tz
      } b =
    record
      { passive      = pa -, b
      ; active       = ac
      ; parti        = record { lrcov = u -,^ b ; lrdis = d -,^ b }
      ; passiveThin  = ph -, b
      ; activeSb     = env ((_:- (io -^ b))) tz
      }

  IsSnoc : Scope -> Splatoid
  IsSnoc [] = SplatZero
  IsSnoc (_ -, _) = SplatOne

  splitSub  : forall {ga de} T -> Tight Trrm T :^ ga -> SplitSub ga de -> Tight Trrm T :^ de
  splitWork : forall {ga de} T -> Tight Trrm T ga ->
                (sb : SplitSub ga de){_ : Splat (IsSnoc (active sb))} -> SubCdB T de
   
  splitSub T (t ^ th) sb with th <?s sb
  ... | sb'@record { active = _ -, _ }
    = splitWork T t sb'
  ... | record { active = [] ; parti = record { lrcov = u } ; passiveThin = ph }
    with isAllLeft u
  ... | r~ , r~ = t ^ ph
  splitWork (# _) (var (only r~))
    record { parti = record { lrcov = [] -^, x } ; activeSb = [] -, t } = t
  splitWork (# _) (var (only r~)) record { parti = record { lrcov = [] -,^ x } } {()}
  splitWork (# i) (c $ t) sb {p} = (c $_) $: splitWork (ConArgs c) t sb {p}
  splitWork One' r~ record { parti = record { lrcov = [] } } {}
  splitWork (S *' T)  (rp s t _) sb = splitSub S s sb /,\ splitSub T t sb
  splitWork (b |-' T) (kk t) sb {p} = kk $: splitWork T t sb {p}
  splitWork (b |-' T) (ll t) sb {p} = \\ splitWork T t (wkSplitSub sb b) {p}


{-)-}
```
