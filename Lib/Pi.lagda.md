# Pi

```agda
module Lib.Pi where

open import Agda.Primitive public renaming (_⊔_ to lmax)  -- damn unicode!

```

The dependent function type (or &lsquo;Pi-type&rsquo;) is built in to
Agda, written `(x : S) -> T` where `x` may occur freely in `T`. We may
write `S -> T` for the non-dependent special case. It's called &Pi;,
because that is the symbol for *product*, generalising products of
*two* things to products of `S` things: we have a `T` for each thing
in `S`. Indeed, some people call these things &lsquo;dependent
products&rsquo;, but I don't, because people get confused with
dependent *pair* types, which are also products, in some sense.


## Abbreviations

It's sometimes useful to eschew Agda's (x : S) -> T x notation for
something more combinatory, especially when T is a function which
analyses its arg in nontrivial ways. It's also useful, partially
applied, in higher-order settings.


```agda
infixr 2 _>>_ _!>_

_>>_ _!>_ : forall {k l} -> (S : Set k)(T : S -> Set l) -> Set (lmax k l)
S >> T = (s : S) -> T s
S !> T = {s : S} -> T s
```


## Identity Functions

Usually, the polymorphic identity function, `id` can take its type
implicitly.

```agda
id : forall {l}{X : Set l} -> X -> X
id x = x
```

However, the following variant takes its type explicitly, effectively
giving us the means to write a type annotation

```agda
infix 1 _:`_

_:`_ : forall {l}(X : Set l) -> X -> X
X :` x = x
```

## Classic Combinators

```agda
module _ {i}{A : Set i}{j} where

 ko : {B : Set j}(a : A)(b : B) -> A
 ko a _ = a

 module _ {B : A -> Set j} where

  infixr 2 _$o_

  _$o_ : (a : A) -> (A >> B) -> B a
  a $o f = f a

  module _ {k}{C : (a : A) -> B a -> Set k} where

   infixl 3 _$$_   -- the S combinator

   _$$_ : ((a : A) -> B a >> C a) ->
          (s : A >> B) -> (a : A) -> C a (s a)
   (f $$ s) a = f a (s a)
```

## Diagrammatic Composition

```agda
module _ {i j k}{A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k} where

  infixr 4 _-_
  
  _-_ : (f : (a : A) -> B a)
        (g : {a : A} -> B a >> C a) ->
        A >> C $$ f
  (f - g) a = g (f a)
```

I like diagrammatic composition because...I like diagrams!

Now, the rhs is really g {a} (f a), so that really is S, but it
specialises to composition in the nondependent case.


## Index-Lifting

```agda
infixr 5 _-:>_
_-:>_ : forall {k l}{I : Set k}(S T : I -> Set l) -> I -> Set l
(S -:> T) i = S i -> T i

[_] : forall {k l}{I : Set k}(T : I -> Set l) -> Set (lmax k l)
[ T ] = forall {i} -> T i
```

