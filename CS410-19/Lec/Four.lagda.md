```agda
module CS410-19.Lec.Four where

open import Agda.Primitive

open import Lib.Pi
open import Lib.Equality
open import Lib.Sigma
open import Cat.Smol
open import Cat.Setoid

open Setoid
```

```agda
record Cat {l}{Obj : Set l}(_=>_ : Obj -> Obj -> Setoid l) : Set (lsuc l) where
  field
  
    identity : forall {T}
            -> Carrier (T => T)

    compose  : forall {R S T}
            -> Carrier (R => S) -> Carrier (S => T) -> Carrier (R => T)

    compose-identity-arrow : forall {S T}(f : Carrier (S => T))
                    -> Eq (S => T) (compose identity f) f

    compose-arrow-identity : forall {S T}(f : Carrier (S => T))
                    -> Eq (S => T) (compose f identity) f

    compose-compose : forall {R S T U}
                   (f : Carrier (R => S))(g : Carrier (S => T))(h : Carrier (T => U))
                   -> Eq (R => U) (compose (compose f g) h) (compose f (compose g h))
```

```agda
module _ where
  open Cat

  Pointwise : Cat {lsuc lzero}{Set} \ S T -> UpS (Intensional S -Setoid> Intensional T)
  Pointwise = ?
```
