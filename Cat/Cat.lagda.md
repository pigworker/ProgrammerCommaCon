Categories with a Setoid of Arrows
==================================

```agda
module Cat.Cat where

open import Agda.Primitive

open import Lib.Pi
open import Lib.Equality
open import Lib.Sigma
open import Cat.Smol
open import Cat.Setoid

```

The idea is to cope with `~` not always meaning what we want it to mean
by saying what it is that we do mean, in this case by equality of arrows.

```agda
module _ where
  open Setoid
  
  record Cat {l}{Obj : Set l}(_=>_ : Obj -> Obj -> Setoid l) : Set l where
    field
  
      identity : forall {T}
              -> Carrier (T => T)

      compose  : forall {R S T}
              -> Carrier (R => S) -> Carrier (S => T) -> Carrier (R => T)

      -- It's very easy to forget that we pay a price for using setoids:
      -- we must document why *our* "equality" is respected.
      compose-respect : forall {R S T} ->
        {f0 f1 : Carrier (R => S)} -> Eq (R => S) f0 f1 ->
        {g0 g1 : Carrier (S => T)} -> Eq (S => T) g0 g1 ->
        Eq (R => T) (compose f0 g0) (compose f1 g1)


      -- could combine compose and compose-respect as a setoid arrow

      compose-identity-arrow : forall {S T}(f : Carrier (S => T))
                      -> Eq (S => T) (compose identity f) f

      compose-arrow-identity : forall {S T}(f : Carrier (S => T))
                      -> Eq (S => T) (compose f identity) f

      compose-compose : forall {R S T U}
                        (f : Carrier (R => S))(g : Carrier (S => T))(h : Carrier (T => U))
                     -> Eq (R => U) (compose (compose f g) h) (compose f (compose g h))
```


Category of Setoids
-------------------

Setoids form a category.

```agda
module _ where
  open Cat

  SetoidCat : forall l ->
           Cat {lsuc l}{Setoid l} \ S T -> UpS (S -Setoid> T)
  identity (SetoidCat l) = up (id , id)
  compose (SetoidCat l) (up (f , fq)) (up (g , gq)) = up ((f - g) , (fq - gq))
  compose-respect (SetoidCat l) (up f01) (up g01) = up (f01 - g01)
  compose-identity-arrow (SetoidCat l) (up (f , fq)) = up fq
  compose-arrow-identity (SetoidCat l) (up (f , fq)) = up fq
  compose-compose (SetoidCat l) (up (f , fq)) (up (g , gq)) (up (h , hq)) =
    up (fq - gq - hq)
```

In particular, we directly obtain that we can reason about functions
up to *pointwise* equality.

```agda
  fn : forall {l}{S T : Set l}
    -> (S -> T)
    -> Setoid.Carrier (UpS (Intensional S -Setoid> Intensional T))
  fn f = up (f , (\ q -> f $~ q)) -- up (f , (f $~_))
```




The Category of Categories
--------------------------

We're now going to build the category of categories, step by step.


### Categories as Objects

We can bundle objects, arrows, the operations and the proofs into one
structure. That's slightly less convenient for access, but that's not
the motivation. Once we have the whole kit packed up as some sort of
`Set` (large, inevitably), it's the right shape to be used as a
notion of `Object` itself.

```agda
record SomeCat l : Set (lsuc l) where
  constructor someCat
  field
    {Object} : Set l
    {Arrow}  : Object -> Object -> Setoid l
    IsCat  : Cat Arrow

open SomeCat public

SETOID : forall l -> SomeCat (lsuc l)
SETOID l = someCat (SetoidCat l)
```

### Functors as Arrows

We work in two stages. First, construct the raw data of what makes a functor.
Second, turn that into a setoid.

```agda
module _ {l}(Source Target : SomeCat l)
  where

  module _ where
    open Cat
    open Setoid

    record _-Cat>_ : Set l where
      CS = IsCat Source
      CT = IsCat Target
      field
        Map : Object Source -> Object Target
        -- We demand a setoid arrow, i.e., one which respects equivalence.
        mapSetoid : {S T : Object Source} ->
          Carrier (Arrow Source S T -Setoid> Arrow Target (Map S) (Map T))

      -- We supply map and its respect property separately, for convenience.
      map : {S T : Object Source} ->
              Carrier (Arrow Source S T) ->
              Carrier (Arrow Target (Map S) (Map T))
      map f = fst mapSetoid f 
      map-respect : {S T : Object Source} ->
        {f g : Carrier (Arrow Source S T)} ->
        Eq (Arrow Source S T) f g ->
        Eq (Arrow Target (Map S) (Map T)) (map f) (map g)
      map-respect fq = snd mapSetoid fq

      field
        map-identity : {T : Object Source} ->
          Eq (Arrow Target (Map T) (Map T)) (map (identity CS)) (identity CT)
        map-compose : {R S T : Object Source}
          (f : Carrier (Arrow Source R S))(g : Carrier (Arrow Source S T)) ->
          Eq (Arrow Target (Map R) (Map T)) (map (compose CS f g)) (compose CT (map f) (map g))

  open _-Cat>_ public
```

Step two is a bit hairy. It's not the sort of thing I expect beginners
to get used to doing. It takes a lot of very carefully coordinated use
of `with`.

```agda
  module _ where
    open Setoid
    
    _=Cat>_ : Setoid l
    Carrier _=Cat>_ = _-Cat>_
    Eq _=Cat>_ F G = 
      ((X : Object Source) -> Map F X ~ Map G X) >< \ Q ->
      {S T : Object Source}{f g : Carrier (Arrow Source S T)} ->
       Eq (Arrow Source S T) f g ->
       Eq (Arrow Target (Map G S) (Map G T))
         (map F f :[ Carrier $~ (Arrow Target $~ Q S ~$~ Q T) >)
         (map G g)
    reflEq _=Cat>_ {F} = (\ _ -> r~) , map-respect F
    fst (symEq _=Cat>_ {F} {G} (FG , fg)) X = FG X ~o
    snd (symEq _=Cat>_ {F} {G} (FG , fg)) {S} {T} {f} {g} q
      with Map F S | Map F T | FG S | FG T | map F f | map F g
        | fg (symEq (Arrow Source S T) q)
    ... | _ | _ | r~ | r~ | Ff | Fg | q'
      = symEq (Arrow Target (Map G S) (Map G T)) q'
    fst (transEq _=Cat>_ {F} {G} {H} (FG , fg) (GH , gh)) X =
      FG X -~- GH X
    snd (transEq _=Cat>_ {F} {G} {H} (FG , fg) (GH , gh)) {S}{T}{f}{g} q
      with Map F S | Map F T | FG S | FG T | map F f | fg (reflEq (Arrow Source S T) {f})
    ... | _ | _ | r~ | r~ | Ff | q0
      with Map G S | Map G T | GH S | GH T | map G f | map G g | gh q
    ... | _ | _ | r~ | r~ | Gf | Gg | q1 =
      transEq (Arrow Target (Map H S) (Map H T)) q0 q1
```

### Identity and Composition for Functors

```agda
module _ {l} where
  open Cat
  open Setoid
  
  Id : forall {C : SomeCat l} -> C -Cat> C
  Map Id = id
  mapSetoid Id = id , id
  map-identity (Id {C}) {T} = reflEq (Arrow C T T)  
  map-compose (Id {C}) {R}{S}{T} f g = reflEq (Arrow C R T)

  -- composition in the category of categories is -Cat-
  -- functors, not categories are being composed
  _-Cat-_ : forall {C D E : SomeCat l} -> C -Cat> D -> D -Cat> E -> C -Cat> E
  Map (F -Cat- G) = Map F - Map G
  mapSetoid (F -Cat- G) = (map F - map G) , (map-respect F - map-respect G)
  {- which is actually the composition we get from the category of setoids,
     but the following is harder to invoke
     down (compose (SetoidCat l)
              {Arrow C S T}
              {Arrow D (Map F S) (Map F T)}
              {Arrow E (Map G (Map F S)) (Map G (Map F T))}
              (up (mapSetoid F)) (up (mapSetoid G {Map F S}{Map F T})))
  -}
  map-identity (_-Cat-_ {C} {D} {E} F G) {T} = 
    transEq (Arrow E ((Map F - Map G) T) ((Map F - Map G) T))
      (map-respect G (map-identity F))
      (map-identity G)
  map-compose (_-Cat-_ {C} {D} {E} F G) {R} {S} {T} f g = 
    transEq (Arrow E (Map G (Map F R)) (Map G (Map F T)))
      (map-respect G (map-compose F f g))
      (map-compose G (map F f) (map F g))
```

### Category of Categories

```agda
module _ where

  open Cat
  open _-Cat>_
  -- open Setoid
  
  CAT : forall l -> Cat {lsuc l}{SomeCat l} \ C D -> UpS (C =Cat> D)
  identity (CAT l) = up Id
  compose (CAT l) (up F) (up G) = up (F -Cat- G)
  fst (down (compose-respect (CAT L) {f0 = up F0}{up F1}
             (up (F01 , f01)) (up (G01 , g01)))) X
    with Map F0 X | F01 X
  ... | _ | r~ = G01 (Map F1 X)
  snd (down (compose-respect (CAT L) {f0 = up F0}
             (up (F01 , f01)) (up (G01 , g01)))) {S}{T} {f}{g} fg
    with Map F0 S | Map F0 T | F01 S | F01 T | map F0 f | map F0 g | f01 fg
  ... | F0S | F0T | r~ | r~ | F0f | F0g | qf = g01 qf
  compose-identity-arrow (CAT l) {C}{D} (up F) = up ((\ _ -> r~) ,
    \ fg -> map-respect F fg)
  compose-arrow-identity (CAT l) {C}{D} (up F) = up ((\ _ -> r~) ,
    \ fg -> map-respect F fg)
  compose-compose (CAT l) {B}{C}{D}{E} (up F) (up G) (up H) = up ((\ _ -> r~) ,
    \ fg ->
    map-respect H (map-respect G (map-respect F fg)) )
