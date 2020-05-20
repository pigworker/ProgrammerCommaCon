# Thinnings are a Monoidal Category

```agda
module Thin.Monoid where
```

```agda
open import Lib.Bwd
open import Thin.Thin
```

```agda
module _ {X : Set} where
```

```agda
  io[] : _<=_ {X} [] []
  io[] = io

  _<+_ : {az bz yz zz : Bwd X} -> az <= yz -> bz <= zz -> (az -+ bz) <= (yz -+ zz)
  th <+ (ph -^ x) = (th <+ ph) -^ x
  th <+ (ph -, x) = (th <+ ph) -, x
  th <+ []        = th
```

