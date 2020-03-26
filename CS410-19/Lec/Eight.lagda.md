The Universe(s) of Datatype Descriptions
========================================

```agda
module CS410-19.Lec.Eight where

open import Agda.Primitive -- we'll need universe levels

open import Lib.Zero
open import Lib.One
open import Lib.Two
open import Lib.Equality
open import Lib.Bwd
open import Lib.Sigma
open import Lib.Sum
open import Lib.Pi
open import Lib.Nat
open import Cat.Setoid
```

```agda
module _ {l}(I : Set l) where

  data Desc : Set (lsuc l) where  -- `Desc`ription of datatypes
    `V           : I -> Desc
    `0 `1        : Desc
    _`*_         : Desc -> Desc -> Desc
    _`><_ _`>>_  : (S : Set l)(T : S -> Desc) -> Desc
```


Action on objects:

```agda
[[_]]0 : forall {l}{I : Set l}(D : Desc I) -> (I -> Set l) -> Set l
[[ `V i    ]]0 X = X i
[[ `0      ]]0 X = Zero
[[ `1      ]]0 X = One
[[ D `* E  ]]0 X = [[ D ]]0 X * [[ E ]]0 X
[[ S `>< T ]]0 X = S >< \ s -> [[ T s ]]0 X
[[ S `>> T ]]0 X = (s : S) -> [[ T s ]]0 X
```

Action on arrows:

```agda
[[_]]1 : forall {l}{I : Set l}(D : Desc I){X Y : I -> Set l}
      -> [ X -:> Y ] -> [[ D ]]0 X -> [[ D ]]0 Y
[[ `V i    ]]1 f x  = f x
[[ `1      ]]1 f <> = <>
[[ D `* E  ]]1 f (xd , xe) = ([[ D ]]1 f xd) , ([[ E ]]1 f xe)
[[ S `>< T ]]1 f (s , xt)  = s , [[ T s ]]1 f xt
[[ S `>> T ]]1 f g s = [[ T s ]]1 f (g s)
```

How do we deploy `Desc`?

```agda
module _ {l}
         {IN IL : Set l}             -- what indexes nodes? what indexes leaves?
         (F : IN -> Desc (IL + IN))  -- what is the node structure for each index?
  where
  
  data Data (X : IL -> Set l)  -- what is stored at leaves?
            (i : IN)           -- what is the index of the top node?
    : Set l
    where
    con : [[ F i ]]0 (X <?> Data X) -> Data X i
```

A much needed example: vectors.

```agda
VecDesc : Nat -> Desc (One + Nat)
VecDesc ze     = `1
VecDesc (su n) = `V (inl <>) `* `V (inr n)

_-Vec_ : Set -> Nat -> Set
X -Vec n = Data VecDesc (\ _ -> X) n

-- vnil : forall {X} -> X -Vec ze
pattern vnil = con <>

-- vcons : forall {X n} -> X -> X -Vec n -> X -Vec (su n)
pattern vcons x xs = con (x , xs)
```

Simple Types and Simply Typed Terms
-----------------------------------

Types: base or arrow.

```agda
TyDesc : One {lzero} -> Desc {lzero} (Zero + One)
TyDesc <> = Two `>< (`1 <2> (`V (inr <>) `* `V (inr <>)))

Ty : Set
Ty = Data TyDesc (\ ()) <>

-- base : Ty
pattern base = con (ff , <>)

-- _>>>_ : Ty -> Ty -> Ty
pattern _>>>_ S T = con (tt , S , T)

IsFun : Ty -> Set
IsFun base      = Zero
IsFun (S >>> T) = One

Value : Ty -> Set
Value base      = Nat
Value (S >>> T) = Value S -> Value T
```

Variables in a context:

```agda
VarDesc : (Bwd Ty * Ty) -> Desc (Zero + (Bwd Ty * Ty))
VarDesc ([]     , T) = `0
VarDesc (G -, S , T) = (One + (S ~ T)) `>< ((\ _ -> `V (inr (G , T))) <?> \ _ -> `1)

Var : (Bwd Ty * Ty) -> Set
Var = Data VarDesc (\ ())

-- topv : forall {G T} -> Var (G -, T , T)
pattern topv = con (inr r~ , <>)

-- popv : forall {G S T} -> Var (G , T) -> Var (G -, S , T)
pattern popv x = con (inl <> , x)

lookup : forall {G T} -> Env Value G -> Var (G , T) -> Value T
lookup [] (con ())
lookup (g -, v) topv     = v
lookup (g -, v) (popv x) = lookup g x
```

Terms:

```agda
TermHelp : Bwd Ty -> forall T ->
           Two + IsFun T ->
           Desc ((Bwd Ty * Ty) + (Bwd Ty * Ty))
TermHelp G T (inl ff)  = `V (inl (G , T))  -- variable
TermHelp G T (inl tt)  = Ty `>< \ S -> `V (inr (G , (S >>> T))) `* `V (inr (G , S))  -- application
TermHelp G (S >>> T) (inr <>) = `V (inr ((G -, S) , T))  -- lambda

TermDesc : (Bwd Ty * Ty) -> Desc ((Bwd Ty * Ty) + (Bwd Ty * Ty))
TermDesc (G , T) = (Two + IsFun T) `>< TermHelp G T

Term : (Bwd Ty * Ty) -> Set
Term = Data TermDesc Var

-- vart : forall {G T} -> Var (G , T) -> Term (G , T)
pattern vart x = con (inl ff , x)

-- appt : forall {G S T} -> Term (G , S >>> T) -> Term (G , S) -> Term (G , T)
pattern appt f s = con (inl tt , _ , f , s)

-- lamt : forall {G S T} -> Term (G -, S  ,  T) -> Term (G  ,  S >>> T)
pattern lamt t = con (inr <> , t)

eval : forall {G T} -> Term (G , T) -> Env Value G -> Value T
eval (vart x)   g = lookup g x
eval (appt f s) g = eval f g (eval s g)
eval {_}{S >>> T} (lamt t) g s = eval t (g -, s)
```

Desc in Desc?

```agda
data DTag {l} : Set l where dV d0 d1 d* d>< d>> : DTag

module _ {l}(I : Set l) where

 DescDesc : One {lsuc l} -> Desc {lsuc l} (One + One)
 DescDesc <> = DTag `>< \
   { dV -> `V (inl <>)
   ; d0 -> `1
   ; d1 -> `1
   ; d* -> `V (inr <>) `* `V (inr <>)
   ; d>< -> Set l `>< \ S -> Up S `>> \ _ -> `V (inr <>)
   ; d>> -> Set l `>< \ S -> Up S `>> \ _ -> `V (inr <>)
   }

 Desc' : Set (lsuc l)
 Desc' = Data DescDesc (\ _ -> Up I) <>
```
