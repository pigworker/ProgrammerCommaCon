```agda
module CS410-19.Lec.Five where

open import Lib.Pi
open import Lib.One
open import Lib.Sigma
```

```agda
record Interaction : Set1 where
  constructor _<?_
  field
    Question  : Set
    Answer    : Question -> Set

open Interaction public
```

```agda
[[_]]I : Interaction -> Set -> Set
[[ Q <? A ]]I X = Q >< \ q  -- first, choose a question
               -> A q       -- wait for answer
               -> X         -- return an X

mapI : forall (QA : Interaction){X Y} ->
       (X -> Y) -> [[ QA ]]I X -> [[ QA ]]I Y
mapI QA f (q , k) = q , k - f
```

```agda
data StateQ (S : Set) : Set where
  get : StateQ S
  put : S -> StateQ S

State : Set -> Interaction
Question (State S) = StateQ S
Answer (State S) get = S
Answer (State S) (put s) = One
```

```agda
data Process (QA : Interaction)(X : Set) : Set where
  return : X -> Process QA X
  ask : [[ QA ]]I (Process QA X) -> Process QA X
```

```agda
runState : forall {S X} -> S -> Process (State S) X -> X
runState s (return x) = x
runState s (ask (get , k)) = runState s (k s)
runState s (ask (put s' , k)) = runState s' (k <>)
```

```agda
_-Interaction>_ : (Hi Lo : Interaction) -> Set
(Q <? A) -Interaction> Google = (q : Q) -> [[ Google ]]I (A q)



xlate : forall {QA Google} -> QA -Interaction> Google ->
        forall {X} -> [[ QA ]]I X -> [[ Google ]]I X
xlate d (q , k) with d q
... | qg , kg = qg , (kg - k)
```
