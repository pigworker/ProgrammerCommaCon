Structuring Interaction for Beginners
=====================================

```agda
module CS410-19.Lec.Five where

open import Lib.Pi
open import Lib.One
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
xlate' f q = {!!}
```
