# Scopes and Thinnings

```agda
module SPLV.Thursday where

open import Lib.Bwd -- look at this
open import Lib.One
open import Lib.Equality
open import Lib.Splatoid
open import Lib.Datoid
open import Lib.Sigma
```

```agda
data TDesc (B : Set)(I : Set) : Set where
  #_ : I -> TDesc B I
  One' : TDesc B I
  _*'_ : TDesc B I -> TDesc B I -> TDesc B I
  _|-'_ : B -> TDesc B I -> TDesc B I

{-(-}
infixr 5 _*'_
infix  6 #_
{-)-}

open import Lib.Pi -- come back to this before tuple

{-(-}
module _ {B I : Set} where

 Tuple  :   (I -> Bwd B -> Set)
        ->  (TDesc B I -> Bwd B -> Set)
 Tuple P (# i) ga = P i ga
 Tuple P One' ga = One
 Tuple P (S *' T) ga = Tuple P S ga * Tuple P T ga
 Tuple P (b |-' T) ga = Tuple P T (ga -, b)
{-)-}

```

```agda
record TermDesign : Set1 where
  field
    BindingSort   : Set
    TermSort      : Set
    bind2Term     : BindingSort -> TermSort
    Constructor   : TermSort -> Datoid
    ConArguments  : forall {i} -> Data (Constructor i)
                               -> TDesc BindingSort TermSort
```

A `TermDesign` generates a type of trees, as follows.


```agda
module _ {X : Set} where
 
 data _<=_ : {-source-}Bwd X -> {-target-}Bwd X -> Set where
   _-^_ : forall {ga de} -> ga <= de -> forall x -> ga      <= de -, x
   _-,_ : forall {ga de} -> ga <= de -> forall x -> ga -, x <= de -, x
   []   :                                           []      <= []

 infixl 20 _-^_
 infix  15 _<=_

 _<-_ :  X -> {-target-}Bwd X -> Set
 x <- ga = [] -, x <= ga
```


```agda
{-(-}
module _ (D : TermDesign) where

 open TermDesign D

 data Term (i : TermSort)(ga : Bwd BindingSort) : Set where
   var : forall {b} -> b <- ga -> bind2Term b ~ i -> Term i ga
   _$_ : (c : Data (Constructor i))
      -> Tuple Term (ConArguments c) ga
      -> Term i ga

 infix 1 _$_
{-)-}

 sbst : forall {ga de : Bwd BindingSort} ->
       (forall {b} -> b <- ga -> Term (bind2Term b) de) ->
       forall {T} -> Tuple Term T ga -> Tuple Term T de
 sbst sb {# i} (var j r~) = sb j
 sbst sb {# i} (c $ x) = c $ sbst sb {ConArguments c} x
 sbst sb {One'} <> = <>
 sbst sb {S *' T} (s , t) = sbst sb {S} s , sbst sb {T} t
 sbst sb {b |-' T} t = sbst (\ { (j -^ x) -> {!sb j!}
                               ; (j -, x) -> var ({!!} -, _) r~ }) {T} t
```

We've seen a universe of first-order datatypes which had very little structure.
Not no structure. They did at least support equality decision.

But, as programming language researchers, it might be useful to construct
datatypes with a little more structure: that of syntax. Syntax has variables
and binding constructs, and supports, in particular the operation of
*substitution*.


## Scope and Support

Let us say that the *scope* of a term is the set(?) of free variables *available*
for use therein. Meanwhile, let us say that the *support* of a term is the set(?)
of free variables that it actually *uses* (or, more generally, that are in some
way pertinent to it). As one can only use variables which are available for use,
the support of a term always embeds in its scope.

(Scope, by the way, is an entirely *ideological* notion. Terms you bump into in
the street don't obviously have an inherent scope.)

I'm going to represent sets of variables as backward lists whose elements are
drawn from some type `X`. `X` represents what is known statically about the
variable from its binding site. It's a backward list because the most recently
bound variable is on the right (time goes left to right). `X` might be very boring
(just that the variable exists at all), or it might tell us a great deal (e.g.,
the type of the variable).

When does one scope embed in another? Enter, the *thinnings*.


(In my unicode-free style, I write Greek letters as two-letter abbreviations
(&omega; is om, &omicron; is on).)

(Pedantically, I distinguish *scopes* (which need only tell us which variables exist,
and get lowercase &gamma; and &delta;) from *contexts* (which should document
everything that is known about variables, and get uppercase &Gamma; and &Delta;).)

The `-^` (*caret* means &lsquo;it is missing&rsquo;) tells us that the most recent
variable in the target does not come from the source; the `-,` tells us that it
does. That is, a thinning is a vector of bits indexed by its length (target) and its
population count (source). A thinning is also a combinatorial choice. A thinning is
also an order-preserving embedding.

(Draw Pascal's triangle.)

Note that `ga <= de` is not, in general, a `Splatoid`. It's a kind of
&lsquo;proof-relevant ordering&rsquo;. That fact gives us a healthy example of a
category.

What's our next move?

```agda
{-+}
 io : forall {ga} -> ga <= ga
 io {ga} = {!!}
{+-}
```

```agda
{-+}
 infixl 20 _-<=_
 _-<=_ : forall {ga de ze} -> ga <= de -> de <= ze -> ga <= ze
 th       -<= (ph -^ x) = th -<= ph -^ x
 th -^ .x -<= (ph -, x) = th -<= ph -^ x
 th -, .x -<= (ph -, x) = th -<= ph -, x
 []       -<= []        = []
{+-}
```

A little bit of craft. What if we were in the middle of a proof and
facing this situation...?

```agda
{-+}
 module SITUATION (Foo : Set) where
  situation : forall {ga de ze x}
    (th : ga -, x <= de)(ph : de <= ze -, x)(ps : ga <= ze) ->
    th -<= ph ~ ps -, x ->
    Foo
  situation th ph ps q = {!!}
{+-}
```

(Agda has got a lot cleverer about removing impossible cases. She's a jump
ahead here, but the fact remains that we are reasoning about the usage of
a function by fiddling around with its inputs.)

```agda
{-+}
 module WORSESITUATION (Foo : Set) where
  worseSituation : forall {ga de0 de1 ze}
    (th0 : ga <= de0)(ph0 : de0 <= ze) ->
    (th1 : ga <= de1)(ph1 : de1 <= ze) ->
    th0 -<= ph0 ~ th1 -<= ph1 ->
    Foo
  worseSituation th0 ph0 th1 ph1 q = {!q!}
{+-}
```

```agda
{-+}
 infix 15 [_-_]~_
 infixl 20 _-^,_

 data [_-_]~_ :  -> Set
   where
{+-}
```

```copypasta
 forall {ga de ze}{th : ga <= de}{ph : de <= ze}{ps : ga <= ze} ->
                      -> forall x ->
```

(Go and look at Lib.Sigma.)

```agda
{-+}
 tri : forall {ga de ze}(th : ga <= de)(ph : de <= ze) -> <([ th - ph ]~_)>
 tri th         (ph -^ x) = let ! v = tri th ph in ! v -^ x
 tri (th -^ .x) (ph -, x) = let ! v = tri th ph in ! v -^, x
 tri (th -, .x) (ph -, x) = let ! v = tri th ph in ! v -, x
 tri []         []        =                        ! []

 _-<=_ : forall {ga de ze}(th : ga <= de)(ph : de <= ze) -> ga <= ze
 th -<= ph = fst (tri th ph)
{+-}
```

Now copy-paste the situations and use *with*.


How can we get back to equations?

```agda
{-+}
 splatTri : forall {ga de ze}{th : ga <= de}{ph : de <= ze} -> Splatoid
 Splat (splatTri {th = th} {ph = ph}) = <([ th - ph ]~_)>
 splat splatTri (! v0) (! v1) = ?
{+-}
```

Identity laws.

```agda
{-+}
 io- : forall {ga de}(th : ga <= de) -> [ io - th ]~ th
 io- (th -^ x) = io- th -^ x
 io- (th -, x) = io- th -, x
 io- []        = []

 infixl 20 _-io
 _-io : forall {ga de}(th : ga <= de) -> [ th - io ]~ th
 (th -^ x) -io = th -io -^, x
 (th -, x) -io = th -io -, x
 [] -io        = []
{+-}
```

Associativity cooked three ways. (Draw the diagrams!)

```agda
{-+}
 assoc03 : forall {ga0 ga1 ga2 ga3}
   {th01 : ga0 <= ga1}{th23 : ga2 <= ga3}
   {th02 : ga0 <= ga2}{th13 : ga1 <= ga3} ->
   <([ th01 -_]~ th02 ) :* ([_- th23 ]~ th13)>   -- th12 is shared
   ->
   <([ th01 - th13 ]~_) :* ([ th02 - th23 ]~_)>  -- th03 is generated
 assoc03 (v ^ w) = ?

 assoc02 : forall {ga0 ga1 ga2 ga3}
   {th01 : ga0 <= ga1}{th23 : ga2 <= ga3}
   {th03 : ga0 <= ga2}{th12 : ga1 <= ga3} ->
   <([ th01 -_]~ th03 ) :* ([ th12 - th23 ]~_)>  -- th13 is shared
   ->
   <([ th01 - th12 ]~_) :* ([_- th23 ]~ th03)>   -- th02 is generated
 assoc02 (v ^ w) = ?

 assoc13 : forall {ga0 ga1 ga2 ga3}
   {th01 : ga0 <= ga1}{th23 : ga2 <= ga3}
   {th03 : ga0 <= ga2}{th12 : ga1 <= ga3} ->
   <([ th01 - th12 ]~_) :* ([_- th23 ]~ th03)>   -- th02 is shared
   ->
   <([ th01 -_]~ th03 ) :* ([ th12 - th23 ]~_)>  -- th13 is generated
 assoc13 (v ^ w) = ?

{+-}
```

