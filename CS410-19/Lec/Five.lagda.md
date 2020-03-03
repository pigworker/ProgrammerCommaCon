Structuring Interaction for Beginners
=====================================

```agda
module CS410-19.Lec.Five where

open import Lib.Zero
open import Lib.One
open import Lib.Two
open import Lib.Sum
open import Lib.Pi
open import Lib.Sigma
```


Basic Interaction
-----------------

We say which "questions" are meaningful. For each question, we
specify what would constitute a meaningful answer.

```agda
record Interaction : Set1 where
  constructor _<?_
  field
    Question  : Set
    Answer    : Question -> Set

open Interaction public
```

We obtain, in some suitable sense, a functor. Given a "goal"
X, we construct the set of strategies for achieving the goal
by exactly one interaction.

```agda
[[_]]I : Interaction -> Set -> Set
[[ Q <? A ]]I X = Q >< \ q  -- first, choose a question
               -> A q       -- wait for answer
               -> X         -- return an X

mapI : forall (QA : Interaction){X Y} ->
       (X -> Y) -> [[ QA ]]I X -> [[ QA ]]I Y
mapI QA f (q , k) = q , k - f
```

Example: State
--------------

If you think of commands as passive-aggressive questions,
you can define command-response systems in this way.

 * `get`   means "what is the state?"
 * `put s` means "could you please update the state to s?"

```agda
data StateQ (S : Set) : Set where
  get : StateQ S
  put : S -> StateQ S

State : Set -> Interaction
Question (State S) = StateQ S
Answer   (State S) get     = S    -- reply with the state
Answer   (State S) (put s) = One  -- reply "aye aye!"
```


Iterating Interaction
---------------------

```agda
data Process (QA : Interaction)(X : Set) : Set where
  return : X -> Process QA X
  ask    : [[ QA ]]I (Process QA X) -> Process QA X
```

(Could it possibly be a monad?)

A `Process QA X` is a strategy for achieving goal `X` by
zero or more interactions in accordance with `QA`. Either
you achieve the goal at once, with `return` or you `ask`
a question with the goal not of achieving `X` itself, but
of at least knowing how to proceed further towards it.


Interpreting a `State S` Process
--------------------------------

One thing we can do with processes is run them. For example,
we can run a `State S` process, given the current state.

```agda
runState : forall {S X} -> S -> Process (State S) X -> X
runState s (return x)         = x
runState s (ask (get , k))    = runState s (k s)
runState s (ask (put s' , k)) = runState s' (k <>)
```


Interaction Arrows
------------------

An interaction arrow is a translator between a "high-level"
interaction system (e.g., receiving questions and delivering
answers in natural language) and a "low-level" interaction
system, e.g. how to use google to get the answer. We explain
how to be a high-level answerer when we're a low-level
questioner.

```agda
_-Interaction>_ : (Hi Lo : Interaction) -> Set
(Q <? A) -Interaction> Google
  =  (q : Q)               -- given a question
  -> [[ Google ]]I (A q)   -- I have a strategy to google the answer
```

That is, an interaction arrow gives a *natural transformation*
from high-level strategies to low-level strategies.

```agda
xlate : forall {QA Google} -> QA -Interaction> Google
     -> forall {X} -> [[ QA ]]I X -> [[ Google ]]I X
xlate d (q , k) with d q
... | qg , kg = qg , (kg - k)
```

Helpfully, *all* natural transformations between interaction
strategies arise this way!

```agda
xlate' : forall {QA Google}
      -> (forall {X} -> [[ QA ]]I X -> [[ Google ]]I X)
      -> QA -Interaction> Google
xlate' f q = f (q , id)
```

```agda
kI : Set -> Interaction
Question (kI R) = R
Answer   (kI R) r = Zero
```

```agda
idI : Interaction
Question idI = One
Answer   idI <> = One

to-idI : forall {X} -> X -> [[ idI ]]I X
to-idI x = <> , (\ _ -> x)

from-idI : forall {X} -> [[ idI ]]I X -> X
from-idI (<> , k) = k <>
```

```agda
op : Interaction -> Interaction
op (Q <? A) = ((q : Q) -> A q) <? (\ _ -> Q)
```

```agda
_+I_ : Interaction -> Interaction -> Interaction
Question ((Q0 <? A0) +I (Q1 <? A1)) = Q0 + Q1
Answer ((Q0 <? A0) +I (Q1 <? A1)) (inl q0) = A0 q0
Answer ((Q0 <? A0) +I (Q1 <? A1)) (inr q1) = A1 q1

_&I_ : Interaction -> Interaction -> Interaction
Question ((Q0 <? A0) &I (Q1 <? A1)) = Q0 * Q1
Answer ((Q0 <? A0) &I (Q1 <? A1)) (q0 , q1) = A0 q0 + A1 q1

-- choice
choice : forall {QA0 QA1 X Y}
      -> [[ QA0    +I    QA1 ]]I X
      -> [[ op QA0 &I op QA1 ]]I Y
      -> X * Y
choice (inl q0 , k) ((f0 , f1) , s1) = k (f0 q0) , s1 (inl q0)
choice (inr q1 , k) ((f0 , f1) , s1) = k (f1 q1) , s1 (inr q1)
```

```agda
record Server (QA : Interaction)(D : Set) : Set where
  coinductive
  field
    display : D
    react   : [[ op QA ]]I (Server QA D)
open Server public
```

```agda
data Bwd (D : Set) : Set where
  []   : Bwd D
  _-,_ : Bwd D -> D -> Bwd D
  
chat : forall {QA X D}
    -> Process QA X       -- P asks the questions
    -> Bwd D              -- S's ancient history of displays
    -> Server QA D        -- S displays and reacts
    -> X                  -- P's output
     * Bwd D              -- S's recent history of displays
     * Server QA D        -- S, still alive

chat (return x) dz s = x , dz , s
chat (ask (q , k)) dz s with react s
... | answer , evolve = chat (k (answer q)) (dz -, display s) (evolve q)
```

```agda
_-I-_ : Interaction -> Interaction -> Interaction
Question (QA0 -I- (Q1 <? A1)) = [[ QA0 ]]I Q1
Answer   (QA0 -I- (Q1 <? A1)) (q , k)
  = Answer QA0 q >< \ a ->
    A1 (k a)

to-coI : forall {QA0 QA1 X}
      -> [[ QA0 ]]I ([[ QA1 ]]I X)
      -> [[ QA0 -I- QA1 ]]I X
fst (fst (to-coI (q0 , k0))) = q0
snd (fst (to-coI (q0 , k0))) a0 with k0 a0
... | q1 , k1 = q1
snd (to-coI (q0 , k0)) (a0 , a1) with k0 a0
... | q1 , k1 = k1 a1

from-coI : forall {QA0 QA1 X}
      -> [[ QA0 -I- QA1 ]]I X
      -> [[ QA0 ]]I ([[ QA1 ]]I X)
fst (from-coI ((q0 , k0) , k)) = q0
fst (snd (from-coI ((q0 , k0) , k)) a0) = k0 a0
snd (snd (from-coI ((q0 , k0) , k)) a0) a1 = k (a0 , a1)
```

```agda
ScriptI : Interaction -> Interaction
Question (ScriptI QA) = Process QA One
Answer (ScriptI QA) (return <>) = One
Answer (ScriptI QA) (ask (q , k)) =
  Answer QA q >< \ a ->
  Answer (ScriptI QA) (k a)
```
