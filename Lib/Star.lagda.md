# Reflexive-Transitive Closure

```agda
module Lib.Star where

module _ {X : Set}(R : X -> X -> Set) where

  data Star (x : X) : X -> Set where
    []   : Star x x
    _,-_ : forall {@0 y z} -> R x y -> Star y z -> Star x z

  data Rats (x : X) : X -> Set where
    []   : Rats x x
    _-,_ : forall {@0 y z} -> Rats x y -> R y z -> Rats x z
```
