```agda
module Univ.Sort where

open import Agda.Primitive
open import Lib.Zero
open import Lib.One
open import Lib.Equality
open import Lib.Splatoid
open import Lib.Sum
open import Lib.Sigma
open import Lib.Pi
open import Lib.Bwd
open import Thin.Thin
open import Thin.Cover
open import Thin.Pullback
open import Thin.Parti
```

```agda
data Ki : Set1 where
  co : Ki
  da : Set -> Ki

data OU : Ki -> Set1 where
  RE         : {I : Set}(i : I) -> OU (da I)
  LE         : {k : Ki} -> OU k
  _>K<_ _||_ : {k : Ki} -> OU k -> OU k -> OU k
  SG         : {k : Ki}(S : Set) -> (S -> OU k) -> OU k
  MU         : {I : Set}(F : I -> OU (da I)) -> I -> OU co
  _-o_  _&&_ : OU co -> OU co -> OU co
infixr 4 _-o_
```

```agda
module SORT
  (Key : Set)
  (Le : Key -> Key -> Splatoid)
  (owoto : (x y : Key) -> Splat (Le x y) + Splat (Le y x))
 where

 data Bound : Set where
   bot : Bound
   val : Key -> Bound
   top : Bound

 LeB : Bound * Bound -> Splatoid
 LeB (bot   ,     y) = SplatOne
 LeB (val x , val y) = Le x y
 LeB (x     ,   top) = SplatOne
 LeB (x     ,     y) = SplatZero -- otherwise

 record Mutoid : Set1 where
   field
     Muta : Set
     Muto : Bwd Key -> Muta -> Set
   Mutu : Bwd Key -> Set
   Mutu kz = < Muto kz >
 open Mutoid public

 LeM : Bound * Bound -> Mutoid
 Muta (LeM lu) = Splat (LeB lu)
 Muto (LeM lu) kz _ = kz ~ []

 _*K*_ : (Bound * Bound -> Mutoid) -> (Bound * Bound -> Mutoid) -> (Bound * Bound -> Mutoid)
 Muta ((S *K* T) (l , u)) = Key >< \ m -> Muta (S (l , val m)) * Muta (T (val m , u))
 Muto ((S *K* T) (l , u)) kz (m , s , t) = 
   (Bwd Key * Bwd Key * Bwd Key) >< \ (iz , ijz , jz) ->
   ([] -, m) <-[ kz ]-> ijz * Muto (S (l , val m)) iz s * iz <-[ ijz ]-> jz * Muto (T (val m , u)) jz t

 _:><_ : (S : Set)(T : S -> Mutoid) -> Mutoid
 Muta (S :>< T) = S >< \ s -> Muta (T s)
 Muto (S :>< T) kz (s , t) = Muto (T s) kz t

 _*M*_ : Mutoid -> Mutoid -> Mutoid
 Muta (S *M* T) = Muta S * Muta T
 Muto (S *M* T) kz (s , t) = (Bwd Key * Bwd Key) >< \ (iz , jz) ->
   Muto S iz s * iz <-[ kz ]-> jz * Muto T jz t

 _-Mo_ : Mutoid -> Mutoid -> Mutoid
 Muta (S -Mo T) = Muta S -> Muta T
 Muto (S -Mo T) iz f = forall {kz jz} -> iz <-[ kz ]-> jz ->
   (s : Muta S)(sj : Muto S jz s) -> Muto T kz (f s)

 abstM :  forall (S T : Mutoid){iz}
       -> ((s : Muta S) -> Muta T >< \ t -> 
            forall {jz kz} -> iz <-[ kz ]-> jz -> Muto S jz s -> Muto T kz t)
       -> Mutu (S -Mo T) iz
 fst (abstM S T f) s = fst (f s)
 snd (abstM S T f) kij s sj = snd (f s) kij sj

 _&M&_ : Mutoid -> Mutoid -> Mutoid
 Muta (S &M& T) = Muta S * Muta T
 Muto (S &M& T) kz (s , t) = Muto S kz s * Muto T kz t

 Da : forall {I} -> (I -> Bound * Bound -> Mutoid) ->
                    OU (da I) -> Bound * Bound -> Mutoid
 Da R (RE i)    = R i
 Da R LE        = LeM
 Da R (S >K< T) = Da R S *K* Da R T
 Da R (SG S T)  lu = S :>< \ s -> Da R (T s) lu
 Da R (S || T)  lu = Da R S lu *M* Da R T lu

 module _ {I : Set}(F : I -> OU (da I)) where
 
  data Ordered (i : I)(lu : Bound * Bound) : Set
  data Ordered$ (i : I)(lu : Bound * Bound)(kz : Bwd Key) : Ordered i lu -> Set

  OM : I -> Bound * Bound -> Mutoid
  Muta (OM i lu) = Ordered i lu
  Muto (OM i lu) = Ordered$ i lu

  data Ordered i lu where
    node : Muta (Da OM (F i) lu) -> Ordered i lu

  data Ordered$ i lu kz where
    node : forall {t} -> Muto (Da OM (F i) lu) kz t -> Ordered$ i lu kz (node t)

 Co : OU co -> Bound * Bound -> Mutoid
 Co LE = LeM
 Co (S >K< T) = Co S *K* Co T
 Co (S || T) lu = Co S lu *M* Co T lu
 Co (SG S T) lu = S :>< \ s -> Co (T s) lu
 Co (MU F i) = OM F i
 Co (S -o T) lu = Co S lu -Mo Co T lu
 Co (S && T) lu = Co S lu &M& Co T lu

{-

 Sb : {I : Set}(F : I -> OU co) -> OU (da I) -> OU co
 Sb F (RE i) = F i
 Sb F LE = LE
 Sb F (S >K< T) = Sb F S >K< Sb F T
 Sb F (S || T)  = Sb F S || Sb F T
 Sb F (SG S T)  = SG S \ s -> Sb F (T s)

 daco : forall {I : Set}(F : I -> OU (da I))(T : OU (da I)) ->
   [ Da (Ordered F) T -:> Co (Sb (MU F) T) ]
 daco F (RE i)    t            = t
 daco F LE        t            = t
 daco F (S >K< T) (m , s , t)  = m , daco F S s , daco F T t
 daco F (S || T)  (s , t)      = daco F S s , daco F T t
 daco F (SG S T)  (s , t)      = s , daco F (T s) t

 coda : forall {I : Set}(F : I -> OU (da I))(T : OU (da I)) ->
   [ Co (Sb (MU F) T) -:> Da (Ordered F) T ]
 coda F (RE i)    t            = t
 coda F LE        t            = t
 coda F (S >K< T) (m , s , t)  = m , coda F S s , coda F T t
 coda F (S || T)  (s , t)      = coda F S s , coda F T t
 coda F (SG S T)  (s , t)      = s , coda F (T s) t

 module _ {I : Set}(F : I -> OU (da I))(X : I -> OU co)
          (alg : {i : I} -> [ Co (Sb (\ i -> MU F i && X i) (F i) -o X i) ])
  where
  para : {i : I} -> [ Co (MU F i -o X i) ]
  paradaco : (T : OU (da I)) -> [ Da (Ordered F) T -:> Co (Sb (\ i -> MU F i && X i) T) ]
  para {i} (node t) = alg (paradaco (F i) t)
  paradaco (RE i) t = t , para t
  paradaco LE lu = lu
  paradaco (S >K< T) (m , s , t) = m , paradaco S s , paradaco T t
  paradaco (S || T) (s , t) = paradaco S s , paradaco T t
  paradaco (SG S T) (s , t) = s , paradaco (T s) t

 Da$ : forall {I}(R : I -> Bound * Bound -> Set)
        (R$ : Bwd Key -> (i : I) -> forall {lu} -> R i lu -> Set)
        (kz : Bwd Key)(T : OU (da I)){lu}(t : Da R T lu) -> Set
 Da$ R R$ kz (RE i) t = R$ kz i t
 Da$ R R$ kz LE t = kz ~ []
 Da$ R R$ kz (S >K< T) (m , s , t) = 
   (Bwd Key * Bwd Key * Bwd Key) >< \ (iz , ijz , jz) ->
   ([] -, m) <-[ kz ]-> ijz *
   Da$ R R$ iz S s * iz <-[ ijz ]-> jz * Da$ R R$ jz T t
 Da$ R R$ kz (S || T) (s , t) = 
   (Bwd Key * Bwd Key) >< \ (iz , jz) -> 
   Da$ R R$ iz S s * iz <-[ kz ]-> jz *  Da$ R R$ jz T t
 Da$ R R$ kz (SG S T) (s , t) = Da$ R R$ kz (T s) t

 data Ordered$ {I : Set}{F : I -> OU (da I)}(kz : Bwd Key)(i : I){lu : Bound * Bound} : Ordered F i lu -> Set where
   node : forall {t} -> Da$ (Ordered F) Ordered$ kz (F i) t -> Ordered$ kz i (node t)
 
 _$[_:>_] : forall (kz : Bwd Key)(T : OU co){lu} -> Co T lu -> Set
 kz $[ LE :> t ] = kz ~ []
 kz $[ S >K< T :> (m , s , t) ] = 
   (Bwd Key * Bwd Key * Bwd Key) >< \ (iz , ijz , jz) ->
   ([] -, m) <-[ kz ]-> ijz *
   iz $[ S :> s ] * iz <-[ ijz ]-> jz * jz $[ T :> t ]
 kz $[ S || T :> (s , t) ] = 
   (Bwd Key * Bwd Key) >< \ (iz , jz) -> 
   iz $[ S :> s ] * iz <-[ kz ]-> jz * jz $[ T :> t ]
 kz $[ SG S T :> (s , t) ] = kz $[ T s :> t ]
 kz $[ MU F i :> t ] = Ordered$ kz i t
 iz $[ S -o T :> f ] = 
   (s : Co S _) ->
   {jz kz : Bwd Key} ->
   jz $[ S :> s ] ->
   iz <-[ kz ]-> jz ->
   kz $[ T :> f s ]
 kz $[ S && T :> (s , t) ] = kz $[ S :> s ] * kz $[ T :> t ]
 
 daco$ : forall {I : Set}(F : I -> OU (da I))(T : OU (da I)){kz lu}(t : Da (Ordered F) T lu) ->
   Da$ (Ordered F) Ordered$ kz T t -> kz $[ Sb (MU F) T :> daco F T t ]
 daco$ F (RE i) t tk = tk
 daco$ F LE t tk = tk
 daco$ F (S >K< T) (m , s , t) (! mij , si , ij , tj) = ! mij , daco$ F S s si , ij , daco$ F T t tj
 daco$ F (S || T) (s , t) (! si , ij , tj) = ! daco$ F S s si , ij , daco$ F T t tj
 daco$ F (SG S T) (s , t) tk = daco$ F (T s) t tk

 record Muta (kz : Bwd Key)(P : OU co) lu : Set where
   constructor _%:_
   field
     muta  : Co P lu
     muta$ : kz $[ P :> muta ]
 open Muta

 iden : {P : OU co} -> [ Muta [] (P -o P) ]
 muta (iden {P}) p = p
 muta$ (iden {P}) p pj kj with r~ , r~ <- isAllRight (lrcov kj) = pj

 module _ {I : Set}{F : I -> OU (da I)}{X : I -> OU co}
          (alg : {i : I} -> [ Muta [] (Sb (\ i -> MU F i && X i) (F i) -o X i) ]) where
 
  recycle : {i : I} -> [ Muta [] (MU F i -o X i) ]
  paradaco$ : forall (T : OU (da I)){kz lu}(t : Da (Ordered F) T lu) ->
    Da$ (Ordered F) Ordered$ kz T t ->
    kz $[ Sb (\ i -> MU F i && X i) T :> paradaco F X (muta alg) T t ]
  muta recycle = para F X (muta alg)
  muta$ recycle (node t) (node tk) kj =
    muta$ alg (paradaco F X (muta alg) (F _) t) (paradaco$ (F _) t tk) kj
  paradaco$ (RE i) t tk = tk , muta$ recycle t tk allRightParti
  paradaco$ LE t tk = tk
  paradaco$ (S >K< T) (m , s , t) (! mij , si , ij , tj) = ! mij , paradaco$ S s si , ij , paradaco$ T t tj
  paradaco$ (S || T)  (s , t) (! si , ij , tj) = ! paradaco$ S s si , ij , paradaco$ T t tj
  paradaco$ (SG S T)  (s , t) tk = paradaco$ (T s) t tk

 module _ {P : OU co}{I : Set}{F : I -> OU (da I)} where

  coda$ :  forall (T : OU (da I)){kz lu}
           (t : Co (Sb (MU F) T) lu)
        -> kz $[ Sb (MU F) T :> t ]
        -> Da$ (Ordered F) Ordered$ kz T (coda F T t)
  coda$ (RE i) t tk = tk
  coda$ LE t tk = tk
  coda$ (S >K< T) (m , s , t) (! mij , si , ij , tj) = ! mij , coda$ S s si , ij , coda$ T t tj 
  coda$ (S || T) (s , t) (! si , ij , tj) = ! coda$ S s si , ij , coda$ T t tj
  coda$ (SG S T) (s , t) tk = coda$ (T s) t tk

  cstr :   {kz : Bwd Key}{i : I}
       ->  [ Muta kz (P -o Sb (MU F) (F i))
       -:>   Muta kz (P -o MU F i) ]
  muta  (cstr {i = i} f) p = node (coda F (F i) (muta f p))
  muta$ (cstr {i = i} f) p pj kj = node (coda$ (F i) _ (muta$ f p pj kj))
```

```agda
 case :  forall {kz S T P lu}
      -> ((s : S) -> Muta kz (T s -o P) lu)
      -> Muta kz (SG S T -o P) lu
 muta  (case f) (s , t) = muta  (f s) t
 muta$ (case f) (s , t) = muta$ (f s) t

 slct :  forall {kz S T P}
      -> (s : S) -> [ Muta kz (P -o T s)
      -:> Muta kz (P -o SG S T) ]
 muta  (slct s f) p = s , muta f p
 muta$ (slct s f) = muta$ f
```

```agda
 appl : forall {S T iz lu}
      -> Muta iz (S -o T) lu
      -> forall {jz kz} -> Muta jz S lu -> iz <-[ kz ]-> jz -> Muta kz T lu
 muta  (appl f s kij) = muta f (muta s)
 muta$ (appl f s kij) = muta$ f (muta s) (muta$ s) kij
```

```agda
 module ISORT where

  UListF : One -> OU (da One)
  UListF <> = SG Two (((LE >K< LE) || RE <>) <2> LE)

  OListF : One -> OU (da One)
  OListF <> = SG Two ((LE >K< RE <>) <2> LE)

  insert : [ Muta [] (MU OListF <> -o (LE >K< LE) -o MU OListF <>) ]
  insert = recycle (case ({!!} <2> {!!}))

  isort : [ Muta [] (MU UListF <> -o MU OListF <>) ]
  isort = recycle (case
         ( {!!}
       <2> cstr (slct tt iden)
         ))
-}
```
