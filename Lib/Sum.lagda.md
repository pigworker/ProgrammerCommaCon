# Sum

```agda
module Lib.Sum where

open import Lib.Zero
open import Lib.One
open import Lib.Pi
```

I could introduce sums as dependent pairs over bits, but that has a
tendency to hide structure.

Instead, I'll do it the other way around. See below.

```agda
module _ {l} where

 data _+_ (S T : Set l) : Set l where
   inl : S -> S + T
   inr : T -> S + T
```

## Eliminator

```agda
 module _ {S T : Set l}{m}{P : S + T -> Set m} where

  _<?>_ : (S >> inl - P) -> (T >> inr - P) -> S + T >> P
  (l <?> r) (inl s) = l s
  (l <?> r) (inr t) = r t
```

## Boolean Values

```agda
Two = One + One

pattern ff = inl <>
pattern tt = inr <>

module _ {l}{P : Two -> Set l} where

  _<2>_ : P ff -> P tt -> (b : Two) -> P b
  f <2> t = ko f <?> ko t

So : Two -> Set
So = Zero <2> One

not : Two -> Two
not = tt <2> ff

if_then_else_ : forall {l}{X : Set l} ->
  (b : Two)(t : {_ : So b} -> X)(e : {_ : So (not b)} -> X) -> X
if tt then t else e = t
if ff then t else e = e
```

## Decisions

Often more useful than the Booleans are the Decisions.

```agda
Dec : forall {l} -> Set l -> Set l
Dec X = (X -> Zero) + X
```

Decisions tell us *what* is true or untrue, and *why*.


## Index Lifting

_:+_ : forall {I : Set}(S T : I -> Set) -> I -> Set
(S :+ T) i = S i + T i
