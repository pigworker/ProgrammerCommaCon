Categories with a Setoid of Arrows
==================================

```agda
module CS410-19.Lec.Four where

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
        map : {S T : Object Source} ->
              Carrier (Arrow Source S T) ->
              Carrier (Arrow Target (Map S) (Map T))
              
        -- It's very easy to forget that we pay a price for using setoids:
        -- we must document why *our* "equality" is respected.
        map-respect : {S T : Object Source} ->
              {f g : Carrier (Arrow Source S T)} ->
              Eq (Arrow Source S T) f g ->
              Eq (Arrow Target (Map S) (Map T)) (map f) (map g)
              
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
    Eq _=Cat>_ F G =  -- is this equivalence too tight?
      ((X : Object Source) -> Map F X ~ Map G X) >< \ Q ->
      {S T : Object Source}(f : Carrier (Arrow Source S T)) -> 
        Eq (Arrow Target (Map G S) (Map G T)) (map F f :[ Carrier $~ (Arrow Target $~ Q S ~$~ Q T) >) (map G f)
    fst (reflEq _=Cat>_) X = r~
    snd (reflEq _=Cat>_ {F}) {S} {T} f = reflEq (Arrow Target (Map F S) (Map F T))
    fst (symEq _=Cat>_ (Q , q)) X = Q X ~o
    snd (symEq _=Cat>_ {F} {G} (Q , q)) {S} {T} f
      with Map F S | Map F T | Map G S | Map G T | map F f | map G f | Q S | Q T | q f
    snd (symEq _=Cat>_ {F} {G} (Q , q)) {S} {T} f | FS | FT | .FS | .FT | Ff | Gf | r~ | r~ | qf =
      symEq (Arrow Target FS FT) qf
    fst (transEq _=Cat>_ {F} {G} {H} (FG , fg) (GH , gh)) X = FG X -~- GH X
    snd (transEq _=Cat>_ {F} {G} {H} (FG , fg) (GH , gh)) {S} {T} f
      with Map F S | Map G S | Map H S | FG S | GH S
         | Map F T | Map G T | Map H T | FG T | GH T
         | map F f | map G f | map H f
         | fg f | gh f
    ... | FS | GS | HS | r~ | r~ | FT | GT | HT | r~ | r~ | Ff | Gf | Hf | fgf | ghf =
      transEq (Arrow Target FS FT) fgf ghf
```

### Identity and Composition for Functors

```agda
module _ where
  open Cat
  open Setoid
  
  Id : forall {l}{C : SomeCat l} -> C -Cat> C
  Map Id = id
  map Id = id
  map-respect Id = id
  map-identity (Id {l}{C}) {T} = reflEq (Arrow C T T)  
  map-compose (Id {l}{C}) {R}{S}{T} f g = reflEq (Arrow C R T)

  -- composition in the category of categories is -Cat-
  -- functors, not categories are being composed
  _-Cat-_ : forall {l}{C D E : SomeCat l} -> C -Cat> D -> D -Cat> E -> C -Cat> E
  Map (F -Cat- G) = Map F - Map G
  map (F -Cat- G) = map F - map G
  map-respect (F -Cat- G) = map-respect F - map-respect G
  map-identity (_-Cat-_ {l} {C} {D} {E} F G) {T} = 
    transEq (Arrow E ((Map F - Map G) T) ((Map F - Map G) T))
      (map-respect G (map-identity F))
      (map-identity G)
  map-compose (_-Cat-_ {l} {C} {D} {E} F G) {R} {S} {T} f g = 
    transEq (Arrow E (Map G (Map F R)) (Map G (Map F T)))
      (map-respect G (map-compose F f g))
      (map-compose G (map F f) (map F g))
```

### Category of Categories

(For `compose-respect`, gory is right.)

```agda
module _ where

  open Cat
  open _-Cat>_
  -- open Setoid
  
  CAT : forall l -> Cat {lsuc l}{SomeCat l} \ C D -> UpS (C =Cat> D)
  identity (CAT l) = up Id
  compose (CAT l) (up F) (up G) = up (F -Cat- G)
  fst (down (compose-respect (CAT l) {f0 = F0} {F1} (up (F01 , f01)) {G0} {G1} (up (G01 , g01)))) X
    rewrite F01 X =
    G01 _
  snd (down (compose-respect (CAT l) {T = E}{f0 = up F0} {up F1} (up (F01 , f01)) {up G0} {up G1} (up (G01 , g01)))) {S}{T} f
    with Map F0 S | F01 S | map F0 f | f01 f
  ... | F0S | r~ | F0f | qf
    with Map F0 T | F01 T
  ... | F0T | r~
    with Map G0 (Map F1 S) | G01 (Map F1 S) | map G0 F0f | g01 F0f
  ... | G0FS | r~ | GF0f | qg
    with Map G0 (Map F1 T) | G01 (Map F1 T)
  ... | G0FT | r~ = 
    let open Setoid (Arrow E (Map G1 (Map F1 S)) (Map G1 (Map F1 T))) in
    GF0f =[ qg >=
    map G1 F0f =[ map-respect G1 qf >=
    map G1 (map F1 f) [DONE]
  compose-identity-arrow (CAT l) {C}{D} (up F) =
    up ((\ X -> r~)
    , \ {S}{T} f -> Setoid.reflEq (Arrow D (Map F S) (Map F T)))
  compose-arrow-identity (CAT l) {C}{D} (up F) =
    up ((\ X -> r~)
    , \ {S}{T} f -> Setoid.reflEq (Arrow D (Map F S) (Map F T)))
  compose-compose (CAT l) {B}{C}{D}{E} (up F) (up G) (up H) =
    up ((\ X -> r~)
    , \ {S}{T} f ->
      Setoid.reflEq (Arrow E (Map H (Map G (Map F S))) (Map H (Map G (Map F T)))))

{-
  fst (down (compose-respect (CAT l) {f0 = up F0} {up F1} (up (F01 , f01)) {up G0} {up G1} (up (G01 , g01)))) X
    with Map F0 X | Map F1 X | F01 X
  ... | F0X | F0X | r~
    with Map G0 F0X | Map G1 F0X | G01 F0X
  ... | G0F0X | G0F0X | r~ = r~
  snd (down (compose-respect (CAT l) {T = E}{f0 = up F0} {up F1} (up (F01 , f01)) {up G0} {up G1} (up (G01 , g01)))) {S}{T} f
    with Map F0 S | F01 S | map F0 f | f01 f
  ... | F0S | r~ | F0f | qf
    with Map F0 T | F01 T
  ... | F0T | r~
    with Map G0 (Map F1 S) | G01 (Map F1 S) | map G0 F0f | g01 F0f
  ... | G0FS | r~ | GF0f | qg
    with Map G0 (Map F1 T) | G01 (Map F1 T)
  ... | G0FT | r~ = 
    let open Setoid (Arrow E (Map G1 (Map F1 S)) (Map G1 (Map F1 T))) in
    GF0f =[ qg >=
    map G1 F0f =[ map-respect G1 qf >=
    map G1 (map F1 f) [DONE]
-}
```


Natural Transformations
-----------------------

Functors can also be the objects of a category.

```agda
module _ {l}(Source Target : SomeCat l)
  where

  open Cat (IsCat Target)

  module _ where
    open Setoid
    
    record _-Fun>_ (F G : Source -Cat> Target) : Set l where
      field
        transform  : {X : Object Source} -> Carrier (Arrow Target (Map F X) (Map G X))
        naturality : {S T : Object Source}(h : Carrier (Arrow Source S T)) -> 
                     Eq (Arrow Target (Map F S) (Map G T))
                       (compose (transform {S}) (map G h))
                       (compose (map F h) (transform {T}))
    open _-Fun>_ public

  idN : forall {F} -> F -Fun> F
  transform (idN {F}) = identity
  naturality (idN {F}) {S}{T} h =
    let open Setoid (Arrow Target (Map F S) (Map F T)) in
    (compose identity (map F h))
      =[ compose-identity-arrow _ >=
    map F h
      =< compose-arrow-identity _ ]=
    (compose (map F h) identity)
      [DONE]

  _-Fun-_ : forall {F}{G}{H} -> F -Fun> G -> G -Fun> H -> F -Fun> H
  transform (k -Fun- m) = compose (transform k) (transform m)
  naturality (_-Fun-_ {F} {G} {H} k m) {S} {T} h = 
    let open Setoid (Arrow Target (Map F S) (Map H T)) in
    (compose (compose (transform k) (transform m)) (map H h))
      =[ compose-compose _ _ _ >=
    (compose (transform k) (compose (transform m) (map H h)))
      =[ compose-respect (Setoid.reflEq (Arrow Target (Map F S) (Map G S))) (naturality m h) >=
    (compose (transform k) (compose (map G h) (transform m)))
      =< compose-compose _ _ _ ]=
    (compose (compose (transform k) (map G h)) (transform m))
      =[ compose-respect (naturality k h) (Setoid.reflEq (Arrow Target (Map G T) (Map H T))) >=
    (compose (compose (map F h) (transform k)) (transform m))
      =[ compose-compose _ _ _ >=
    (compose (map F h) (transform (k -Fun- m)))
      [DONE]

```



























