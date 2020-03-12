Polynomials Make Functors
=========================

```agda
module CS410-19.Lec.Seven where

open import Lib.Zero
open import Lib.One
open import Lib.Two
open import Lib.Sum
open import Lib.Sigma
open import Lib.Pi
open import Lib.Equality
```

Business nothing to do with this topic:

* plans for going virtual
* PhD position

What's this topic actually about?

Functors made from 0, 1, +, * and a variable.

```agda
data Poly : Set where
  `X : Poly
  `zero `one : Poly
  _`+_ _`*_ : Poly -> Poly -> Poly
```

```agda
[[_]]0 : Poly -> Set -> Set
[[ `X     ]]0 X = X
[[ `zero  ]]0 X = Zero
[[ `one   ]]0 X = One
[[ P `+ Q ]]0 X = [[ P ]]0 X + [[ Q ]]0 X
[[ P `* Q ]]0 X = [[ P ]]0 X * [[ Q ]]0 X
```

```agda
leafOrNode : Poly
leafOrNode = `one `+ (`X `* `X)
```

```agda
[[_]]1 : (P : Poly) ->
  {S T : Set} -> (S -> T) -> [[ P ]]0 S -> [[ P ]]0 T
[[ `X ]]1 f s = f s
[[ `one ]]1 f <> = <>
[[ P `+ Q ]]1 f (inl sp) = inl ([[ P ]]1 f sp)
[[ P `+ Q ]]1 f (inr sq) = inr ([[ Q ]]1 f sq)
[[ P `* Q ]]1 f (sp , sq) = [[ P ]]1 f sp , [[ Q ]]1 f sq
```

```agda
data Data (P : Poly) : Set where
  con : [[ P ]]0 (Data P) -> Data P
```

```agda
Tree : Set
Tree = Data leafOrNode

-- leaf : Tree
pattern leaf = con (inl <>)

-- node : Tree -> Tree -> Tree
pattern node l r = con (inr (l , r))
```

Decidable Equality for Polynomial Datatypes
-------------------------------------------

We define `polyEq?` on some *recursive* datatype `Data R`. The
helper function `polyEqHelp?` captures what we do when we've
started looking under one `con`, but haven't found our way down to
the next `con`: we are inspecting some polynomial `P` which is
a *substructure* of `R`, but not necessarily `R` itself. The data
at the leaves still live in `Data R`, not `Data P`.

```agda
polyEq? : (R : Poly)(x y : Data R) -> Dec (x ~ y)
polyEqHelp? :
  (P : Poly){R : Poly}(xp yp : [[ P ]]0 (Data R)) -> Dec (xp ~ yp)
```

So, `polyEq?` strips `con`s and calls `polyEqHelp?` for `R`. The
latter calls the former back on arrival at some recursive data.

```agda
polyEq? R (con xp) (con yp) with polyEqHelp? R xp yp
polyEq? R (con xp) (con yp) | inl naw = inl \ { r~ -> naw r~ }
polyEq? R (con xp) (con .xp) | inr r~ = inr r~

polyEqHelp? `X {R} x y = polyEq? R x y
```

For the rest, we follow the structure of the data. Notice that it
is the `+` structure that makes it possible for data to be different.

```agda
polyEqHelp? `one <> <> = inr r~

polyEqHelp? (P `+ Q) (inl xp) (inl yp) with polyEqHelp? P xp yp
polyEqHelp? (P `+ Q) (inl xp) (inl yp) | inl naw = inl \ { r~ -> naw r~ }
polyEqHelp? (P `+ Q) (inl xp) (inl .xp) | inr r~ = inr r~
polyEqHelp? (P `+ Q) (inl xp) (inr yq) = inl \ ()
polyEqHelp? (P `+ Q) (inr xq) (inl yp) = inl \ ()
polyEqHelp? (P `+ Q) (inr xq) (inr yq) with polyEqHelp? Q xq yq
polyEqHelp? (P `+ Q) (inr xq) (inr yq) | inl naw = inl \ { r~ -> naw r~ }
polyEqHelp? (P `+ Q) (inr xq) (inr .xq) | inr r~ = inr r~

polyEqHelp? (P `* Q) (xp , xq) (yp , yq)
  with polyEqHelp? P xp yp | polyEqHelp? Q xq yq
polyEqHelp? (P `* Q) (xp , xq) (yp , yq)
  | inl naw | _ = inl \ { r~ -> naw r~ }
polyEqHelp? (P `* Q) (xp , xq) (yp , yq)
  | inr c | inl naw = inl \ { r~ -> naw r~ }
polyEqHelp? (P `* Q) (xp , xq) (.xp , .xq)
  | inr r~ | inr r~ = inr r~
```
