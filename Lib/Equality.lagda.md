# Equality

```agda
module Lib.Equality where
```

We fix a set `X` at some level `l` in the hierarchy.

```agda
module _ {l}{X : Set l} where
```

Subordinately, we then declare a binary relation as an inductive
datatype.

```agda
 infix 10 _~_
 
 data _~_ (x : X) : X -> Set l where
   r~ : x ~ x
```

When you declare a `data` type in Agda, the type formation rule, here
`_~_ (x : X) : X -> Set l`, has a `:` somewhere.  To the left of `:`
come *parameters* like `(x : X)` and also *Protestant indices*. These
scope over the whole declaration. But, right of `:`, it is permitted
to abstract a `Set` over some *Catholic* indices. That is what the `X
->` is doing. The constructors must yield values in the declared type
with the parameters in situ as declared: there *must* be an `x` left
of `~`. However, we are free to instantiate the Catholic indices with
any values (of the correct type) that we choose, and here we choose
to give a second copy of `x`.

The consequence of this choice is that values of `x ~ y` may be
constructed only when Agda judges `x` and `y` to be equal. Meanwhile,
when we receive an inhabitant of such an equality type, that gives
*evidence* that `x` is equal to `y` and may be *replaced* by it.
That is the miracle of transubstantiation.


## Equivalence Closure

```agda
 infix 40 _-~-_
 infix 41 _~o

 _~o : forall {x y} -> x ~ y -> y ~ x                 -- symmetry
 r~ ~o = r~

 _-~-_ : forall {x y z} -> x ~ y -> y ~ z -> x ~ z    -- transitivity
 r~ -~- q = q
```

Here, we see the miracle at work. In the definition of symmetry, pattern
matching on the input yields the case `r~`, but it also causes `x` and
`y` to be unified, meaning that `r~` is a well typed output. For transitivity,
the same unification means that `y ~ z`, the type of `q`, becomes the same
as `x ~ z`, the type we need.

For short inline proofs, composing equational assumptions, it's ok to use
these operations which foreground the proof objects. Symmetry has higher
priority, so it can be used without parens in transitivity.


## Equality Derivations

```agda
 infixr 30 _~[_>_ _<_]~_
 infixr 31 _[QED]

 _~[_>_ : forall x {y z} -> x ~ y -> y ~ z -> x ~ z
 x ~[ q0 > q1 = q0 -~- q1

 _<_]~_ : forall x {y z} -> y ~ x -> y ~ z -> x ~ z
 x < q0 ]~ q1 = q0 ~o -~- q1

 _[QED] : forall x -> x ~ x
 x [QED] = r~
```

Longer, more involved proofs require clearer awareness of the terms being
related by the proofs. I write proofs like

```example
      thing0         ~[ proof01 >
      thing1          < proof02 ]~
      thing2          [QED]
```

to give a proof of thing0 ~ thing2, showing the stages of my reasoning.

The ternary operators are both sugar for transitivity, with the latter
including symmetry, too. They are designed to expose *what* is shown
equal at each step, as well as *why*.


## Credit

(Once again, I must credit Peter Hancock for the use of sectarian
labels to distinguish varieties of index.)
