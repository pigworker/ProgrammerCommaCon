# Natural Numbers

```agda
module Lib.Nat where

open import Lib.Sum
open import Lib.Equality
open import Lib.Datoid
```

```agda
data Nat : Set where
  ze : Nat
  su : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}
```

```agda
NatD : Datoid
Data NatD = Nat
eq? NatD ze     ze               = inr r~
eq? NatD ze     (su y)           = inl \ ()
eq? NatD (su x) ze               = inl \ ()
eq? NatD (su x) (su y)  with eq? NatD x y
eq? NatD (su x) (su y)  | inl n  = inl \ { r~ -> n r~ }
eq? NatD (su x) (su .x) | inr r~ = inr r~
```

There are many ways to define addition for natural numbers,
extensionally the same, but intensionally rather different.
The following definition effectively regards natural numbers
as boring lists and addition as concatenation.

```agda
_+N_ : Nat -> Nat -> Nat
ze   +N y = y
su x +N y = su (x +N y)
```

One could, of course, flip the arguments to obtain another
version. More exotically, one can define abacus-like addition:

```agda
abacusPlus : Nat -> Nat -> Nat
abacusPlus ze     y = y
abacusPlus (su x) y = abacusPlus x (su y)
```

On lists, that's reverse-and-append.

Still more peculiar is the following, which amounts to a kind
of list *merge*:

```agda
symmetricPlus : Nat -> Nat -> Nat
symmetricPlus ze     y      = y
symmetricPlus x      ze     = x
symmetricPlus (su x) (su y) = su (su (symmetricPlus x y))
```

I like to distribute the following subtly doctored quotation
from Leopold Kronecker:

> God made the natural numbers to confuse us; all else is the
> work of man.

