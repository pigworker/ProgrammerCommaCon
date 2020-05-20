# Reflexive-Transitive Closure

```agda
module Lib.Star where

module _ {X : Set}(R : X -> X -> Set) where

  data Star (x : X) : X -> Set where
    []   : Star x x
    _,-_ : forall {y z} -> R x y -> Star y z -> Star x z

  data Rats (x : X) : X -> Set where
    []   : Rats x x
    _-,_ : forall {y z} -> Rats x y -> R y z -> Rats x z
```

```agda
module _ {X : Set}{R : X -> X -> Set} where

  _<>*>_ : forall {x y z} -> Rats R x y -> Star R y z -> Star R x z
  [] <>*> rs = rs
  (rz -, r) <>*> rs = rz <>*> (r ,- rs)

  _>>*>_ : forall {x y z} -> Star R x y -> Star R y z -> Star R x z
  [] >>*> ss = ss
  (r ,- rs) >>*> ss = r ,- (rs >>*> ss)
```
