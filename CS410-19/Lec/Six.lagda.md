Contingent Interaction for a Turbulent World
============================================

```agda
module CS410-19.Lec.Six where

open import Lib.Zero
open import Lib.One
open import Lib.Two
open import Lib.Sum
open import Lib.Pi
open import Lib.Sigma
open import Lib.Equality
open import Lib.Nat
```

```agda
record _?>_ (I O : Set) : Set1 where
  constructor _<?_/_
  field
    Question  : O -> Set
    Answer    : (o : O) -> Question o -> Set
    @0 status : (o : O)(q : Question o) ->
                Answer o q -> I
  --^^ WTF?

  @0 _-Chat_ : (I -> Set) -> (O -> Set)
  _-Chat_ G o = Question o >< \ q ->
                (a : Answer o q) ->
                G (status o q a)
open _?>_ public                
```

```agda
[0_] : forall {I : Set}(P : I -> Set) -> Set
[0 P ] = {@0 i : _} -> P i
```

```agda
_-chat_ : forall {I O : Set}(F : I ?> O)
          {P Q : I -> Set} ->
          [0 P -:> Q ] ->
          [0 F -Chat P -:> F -Chat Q ]
(F -chat f) (q , k) = {!!}
```

```nagda
module _ (S : Set) where

  data StateQ : Set where
    get : StateQ
    put : S -> StateQ

  State : S ?> S
  State = ?
```

```nagda
module _ {I : Set}(F : I ?> I) where

  data Client (G : I -> Set)(i : I) : Set where
    return : G i -> Client G i
    ask : (F -Chat Client G) i -> Client G i

  _=<<_ : forall {P Q : I -> Set} ->
    [0 P -:> Client Q ] ->
    [0 Client P -:> Client Q ]
  k =<< c = ?
```

```nagda
makeItThree : [0 Client (State Nat) (3 ~_) ]
makeItThree = ?
```
