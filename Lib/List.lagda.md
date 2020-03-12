```agda
module Lib.List where
```

```agda
data List (X : Set) : Set where
  []    : List X
  _,-_  : X -> List X -> List X

infixr 10 _,-_ _+L_

{-# COMPILE GHC List = data [] ([] | (:)) #-}
```

```agda
_+L_ : {X : Set} -> List X -> List X -> List X
[]        +L ys = ys
(x ,- xs) +L ys = x ,- (xs +L ys)
```
