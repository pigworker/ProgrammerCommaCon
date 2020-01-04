# Two

```agda
module Lib.Two where

open import Lib.Zero
open import Lib.One
```

In the spirit of naming types after the number of values in them, `Two` is the type with two values. In other programming languages, this type is called `Bool`, after the nonexistent German logician, Georg Bool, and in honour of that, I like to think of the two values as the truth values, which I spell in the old fashioned terse manner.

```agda
data Two : Set where ff tt : Two
```

Truth values are almost entirely useless unless we know *what* is true. The `if...then...else...` construct, as routinely delivered in programming languages, admits the program transformation of exchanging the expressions in the `then...` and `else...` branches without type error. E.g., in Haskell,

```haskell
if null xs then tail xs else xs
```

What is particularly egregious is that the whole point of testing the condition is to decide between two courses of action, one of which is almost certainly wrong for the circumstances, and yet, testing the condition *makes no difference* to the typechecker's model of the circumstances. That's why software doesn't work. OK, there's more to it than that, but the misinterpreted bit is your fundamental error, right there.


## Dependent Elimination for `Two`

Here's the conditional expression reimagined for the dependently typed world, where the problem `P` that we are solving may depend on some bit `b`, and the branches are *value-specific* special cases, not interchangeble in general.

```agda
module _ {l}{P : Two -> Set l} where

  _<2>_ : P ff -> P tt -> (b : Two) -> P b
  (f <2> t) ff = f
  (f <2> t) tt = t
```

Observe that it displays one of my trademark bad habits, being a binary infix operator with (at least) three inputs. It is intended to be used as a binary infix operator where a *function* is expected, and under those circumstances, the particular `P` can be inferred.

For example, negation looks like this:

```agda
not : Two -> Two
not = tt <2> ff
```

Also, I have made `P` level-polymorphic so that I can use bits to choose between types as well as values. Specifically, I can define the property of a bit being true as follows:

```agda
So : Two -> Set
So = Zero <2> One
```


## `if` reconstructed

Let us upgrade the conventional conditional with more information in the branches. The very least we can do is to remember in each branch what was discovered in the test.

```agda
if_then_else_ : forall {l}{X : Set l} ->
  (b : Two)(t : {_ : So b} -> X)(e : {_ : So (not b)} -> X) -> X
if tt then t else e = t
if ff then t else e = e

-- if_then_else_ = (\ t e -> e) <2> (\ t e -> t)
```


## the `grep Bool` test

We're used to testing functions returning `Bool` values, but in dependently typed programming, they're a bad smell. You can perform a rudimentary health check on a library by running `grep Bool` on it: the less you see, the better.

> A Boolean is a bit uninformative.

We employ bits to make significant distinctions, but if we do not document which distinction if being made, we get no help towards programming correctly. The `So` approach achieves the bare minimum of remembering what program we ran to get the bit. However, it is often more helpful to characterise at a higher level just what it is that the test outcome allows you to do. We're no longer working in George Boole's testable world: we need *evidence*.
