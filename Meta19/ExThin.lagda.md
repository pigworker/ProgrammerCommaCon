# Exercises on Thinnings

(You can cheat by reading the library.)

```agda
module Meta19.ExThin where
open import Lib.Equality
open import Lib.Bwd
open import Lib.Sigma
open import Lib.Pi
```

Here are thinnings, copied from the library.

```agda
module _ {X : Set} where
 
 data _<=_ : Bwd X -> Bwd X -> Set where
   _-^_ : forall {ga de} -> ga <= de -> forall x -> ga      <= de -, x
   _-,_ : forall {ga de} -> ga <= de -> forall x -> ga -, x <= de -, x
   []   :                                           []      <= []

 infixl 20 _-^_
 infix  15 _<=_
```

Observe that we're in a module which fixes `X`, so everything is indented by one character.

Now, build some basic machinery.


## 1 Identity and Composition

1.1. Construct the identity thinning.

```agda
 io : {ga : Bwd X} -> ga <= ga
 io {ga} = {!!}
```

1.2. Implement composition of thinnings as a function.

```agda
 _-thin_ : forall {ga de ze}(th : ga <= de)(ph : de <= ze) -> ga <= ze
 th -thin ph = {!!}
```

1.3. Inductively define the graph of composition and define its generating function.
The datatype of the graph should have one constructor for each line of the function,
taking a recursive argument for each recursive call.

```agda
 data ThinCo : forall {ga de ze}(th : ga <= de)(ph : de <= ze) -> ga <= ze -> Set where

 thinCo : forall {ga de ze}(th : ga <= de)(ph : de <= ze) -> < ThinCo th ph >
 thinCo th ph = {!!}
```

We may now replace `-thin` by the more useful...

```agda
 _-<=_ : forall {ga de ze}(th : ga <= de)(ph : de <= ze) -> ga <= ze
 th -<= ph = fst (thinCo th ph)
```

1.4. Show that the composition relation is functional (not a surprise!).

```agda
 thinFun : forall {ga de ze}{th : ga <= de}{ph : de <= ze}{ps0 ps1 : ga <= ze} ->
           (v0 : ThinCo th ph ps0)(v1 : ThinCo th ph ps1) ->
           (ps0 ~ ps1) >< \ { r~ -> v0 ~ v1 }
 thinFun v0 v1 = {!!}
```

1.5. Construct degenerate composition triangles involving the identity.

```agda
 io- : forall {ga de}(th : ga <= de) -> ThinCo io th th
 io- th = {!!}

 _-io : forall {ga de}(th : ga <= de) -> ThinCo io th th
 th -io = {!!}
```

1.6. The triangular approach to associativity comes in three flavours. If we have
four scopes, `ga0 ga1 ga2 ga3`, we might have three thinnings relating one to the
next, `th01 th12 th23`. That makes possible another three composite thinnings,
`th02 th13 th03`, and *four* composition triangles, `v012 v013 v023 v123`.
Associativity amounts to the observation that whenever we know any two of the
composites (and the two triangles which witness those compositions), we can obtain
the third (and the two triangles in which it is involved).

Prove the following by induction on composition triangles.

```agda
 assoc03 : forall {ga0 ga1 ga2 ga3}
   {th01 : ga0 <= ga1}{th23 : ga2 <= ga3}
   {th02 : ga0 <= ga2}{th13 : ga1 <= ga3} ->
   <(\ th12 -> ThinCo th01 th12 th02 ) :* (\ th12 -> ThinCo th12 th23 th13)>
   ->
   < ThinCo th01 th13 :* ThinCo th02 th23 >  -- th03 is generated
 assoc03 (v012 ^ v123) = {!!}
```

Now derive the other two results, without using induction on triangles.

```agda
 assoc02 : forall {ga0 ga1 ga2 ga3}
   {th01 : ga0 <= ga1}{th23 : ga2 <= ga3}
   {th03 : ga0 <= ga3}{th12 : ga1 <= ga2} ->
   <(\ th13 -> ThinCo th01 th13 th03) :* ThinCo th12 th23 >  -- th13 is shared
   ->
   < ThinCo th01 th12 :* (\ th02 -> ThinCo th02 th23 th03)>   -- th02 is generated
 assoc02 (v013 ^ v123) = {!!}

 assoc13 : forall {ga0 ga1 ga2 ga3}
   {th01 : ga0 <= ga1}{th23 : ga2 <= ga3}
   {th03 : ga0 <= ga3}{th12 : ga1 <= ga2} ->
   < ThinCo th01 th12 :* (\ th02 -> ThinCo th02 th23 th03)>   -- th02 is shared
   ->
   <(\ th13 -> ThinCo th01 th13 th03) :* ThinCo th12 th23 >  -- th13 is generated
 assoc13 (v012 ^ v023) = {!!}
```


## Some Thinning-Specific Properties

2.1. Show that thinnings are *antisymmetric*.

```agda
 antisym : forall {ga de}(th : ga <= de)(ph : de <= ga) ->
   (ga ~ de) >< \ { r~ -> th ~ io * ph ~ io }
 antisym th ph = {!!}
```

2.2. Show that thinnings are *monic* (injective).

```agda
 monic : forall {ga de ze}{th0 th1 : ga <= de}{ph : de <= ze}{ps : ga <= ze} ->
         (v0 : ThinCo th0 ph ps)(v1 : ThinCo th1 ph ps) ->
         (th0 ~ th1) >< \ { r~ -> v0 ~ v1 }
 monic v0 v1 = {!!}
```

2.3. Show that there is a thinning from the empty scope to any other.

```agda
 noth : forall {ga} -> [] <= ga
 noth {ga} = {!!}
```

2.4. Show that thinnings from the empty scope are unique.

```agda
 noth~ : forall {ga}(th ph : [] <= ga) -> th ~ ph
 noth~ th ph = {!!}
```

2.5. Construct the degenerate triangle

```agda
 noth- : forall {ga de}(th : ga <= de) -> ThinCo noth th noth
 noth- th = {!!}
```


## 3 Coverings

We may define concretely what it means for two thinnings with the
same target scope to *cover* that scope.

```agda
 data _/u\_ : forall {ga ze de : Bwd X}
              (th : ga <= ze)(ph : de <= ze) -> Set where
   _-^,_ : forall {ga ze de}{th : ga <= ze}{ph : de <= ze} ->
           th /u\ ph -> forall x -> th -^ x /u\ ph -, x
   _-,^_ : forall {ga ze de}{th : ga <= ze}{ph : de <= ze} ->
           th /u\ ph -> forall x -> th -, x /u\ ph -^ x
   _-,_  : forall {ga ze de}{th : ga <= ze}{ph : de <= ze} ->
           th /u\ ph -> forall x -> th -, x /u\ ph -, x
   []    : [] /u\ []

 infix 15 _/u\_
 infixr 20 _-,^_
```

Observe the lack of a case for `th -^ x` with `ph -^ x`.

3.1. Show that for any pair of thinnings which target the same scope,
we can compute the subscope of the target which they cover.

```agda
 Coproduct : forall {ga ze de : Bwd X}(th : ga <= ze)(ph : de <= ze) -> Set
 Coproduct {ga}{ze}{de} th ph =
   (_ >< \ ze' -> ga <= ze' * ze' <= ze * de <= ze')
          >< \ { (_ , th' , ps , ph') ->
          ThinCo th' ps th * th' /u\ ph' * ThinCo ph' ps ph }
   -- draw a picture of this

 _/+\_ : forall {ga ze de : Bwd X}(th : ga <= ze)(ph : de <= ze) -> Coproduct th ph
 th /+\ ph = {!!}
```

3.2. Show the universal property of the coproduct.

```agda
 copU : forall {ga ze de : Bwd X}{th : ga <= ze}{ph : de <= ze} ->
        {ze0 : Bwd X}{th0 : ga <= ze0}{ph0 : de <= ze0}{ps0 : ze0 <= ze} ->
        ThinCo th0 ps0 th -> ThinCo ph0 ps0 ph ->
        (c : Coproduct th ph) -> let (_ , th' , ps' , ph') , v , w = c
        in <(\ ps -> ThinCo th' ps th0) :*
            (\ ps -> ThinCo ps ps0 ps') :*
            (\ ps -> ThinCo ph' ps ph0)>
 copU v0 w0 (_ , v' , u , w') = {!!}
```

3.3. Show the uniqueness of the coproduct. (Hint: use the universal property.)

```agda
 cop~ : forall {ga ze de : Bwd X}{th : ga <= ze}{ph : de <= ze} ->
        (c0 c1 : Coproduct th ph) -> c0 ~ c1
 cop~ c0 c1 = {!!}
```

3.4 Construct the following degenerate covering.

```agda
 allRightCover : forall {ga} -> noth /u\ io {ga}
 allRightCover {ga} = {!!}
```

3.5 Show that if nothing's on the left, everything's on the right,
preferably by means of the universal property of the coproduct.

```agda
 isAllRight : forall {ga de}(th : ga <= de) -> noth /u\ th ->
   (ga ~ de) >< \ { r~ -> th ~ io }
 isAllRight th = {!!}
```

3.6 Show that you can swap a cover.

```agda
 swapCover : forall {ga ze de}{th : ga <= ze}{ph : de <= ze} ->
             th /u\ ph -> ph /u\ th
 swapCover u = {!!}
```

3.7 Show that you can regroup covers.

```agda
 regroupCover : forall {ga1 ga3 ga2 ga7 ga4}
   {th13 : ga1 <= ga3}{th23 : ga2 <= ga3}
   {th37 : ga3 <= ga7}{th47 : ga4 <= ga7} ->
   th13 /u\ th23 -> th37 /u\ th47 ->
   (_ >< \ ga6 -> ga1 <= ga7 * ga2 <= ga6 * ga4 <= ga6 * ga6 <= ga7) >< \ x ->
   let ga6 , th17 , th26 , th46 , th67 = x in
   th17 /u\ th67 * th26 /u\ th46 *
   ThinCo th13 th37 th17 * < ThinCo th23 th37 :* ThinCo th26 th67 >
 regroupCover u12 u34 = {!!}
```
