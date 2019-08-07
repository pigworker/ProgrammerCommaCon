# Reflexive-Transitive Closure

```agda
module Lib.Star where

data Star {X : Set}(R : X -> X -> Set)(x : X) : X -> Set where
  []   : Star R x x
  _,-_ : forall {y z} -> R x y -> Star R y z -> Star R x z
```
