# Sigma

```agda
module Lib.Sigma where

open import Agda.Primitive public renaming (_⊔_ to lmax)  -- damn unicode!

open import Lib.Pi
```

Dependent pair types are known in the jargon as &Sigma;-types. They
are types of pairs where the type of the second component may depend
on the value of the first.


```agda
module _ {k l} where

 infixr 2 _><_ _*_
 infixr 2 _,_ -- should be low, but probably not that low

 record _><_ (S : Set k)(T : S -> Set l) : Set (lmax k l) where
   constructor _,_
   field
     fst : S
     snd : T fst

 open _><_ public

 _*_ : Set k -> Set l -> Set (lmax k l)
 S * T = S >< ko T
```

They are &lsquo;dependent sums&rsquo;, hence &Sigma;-types, in that they
generalise binary sums to branch over `S`. But they also look a lot like
products, so I tend to go with &lsquo;dependent pair type&rsquo; as more
explicit.


## Index-Lifting

```agda
infixr 4 _:*_
_:*_ : forall {k l}{I : Set k}(S T : I -> Set l) -> I -> Set l
(S :* T) i = S i * T i

infix 2 <_>
<_> : forall {l}{I : Set l}(T : I -> Set l) -> Set l
< T > = _ >< T

infixl 1 _<$>_
_<$>_ : forall {l}{X : Set l}{S T : X -> Set l} ->
        [ S -:> T ] -> < S > -> < T >
f <$> (x , s) = x , f s
```


## Witness Protection

```agda
infixr 2 !_

pattern !_ t = _ , t
```

The job for `!` is to hide inferable existential witnesses.

We should, of course, have `{x : S} >< T x` for that job, which we
treat as if it's `T _`. We'd need the corresponding `{s} , t` as manual
override, to give or expose the witness explicitly. But I fantasize.

I very often work with triples of a witness and two proofs in some
`< S :* T >` type, and again, I don't want to talk about the witness.

```agda
infix 5 _^_

pattern _^_ t th = ! t , th
```

