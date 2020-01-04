# Sum

```agda
module Lib.Sum where

open import Lib.Zero
open import Lib.One
open import Lib.Two
open import Lib.Pi
open import Lib.Sigma
```

I could introduce binary sum types (Haskell's `Either`)
via a `data` declaration, but instead, let us see them
for what they are: dependent pairs over bits.

```agda
module _ {l} where

 _+_ : (S T : Set l) -> Set l
 S + T = Two >< (S <2> T)

 pattern inl s = ff , s
 pattern inr t = tt , t
```

## Eliminator

```agda
 module _ {S T : Set l}{m}{P : S + T -> Set m} where

  _<?>_ : (S >> inl - P) -> (T >> inr - P) -> S + T >> P
  (l <?> r) (inl s) = l s
  (l <?> r) (inr t) = r t
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
