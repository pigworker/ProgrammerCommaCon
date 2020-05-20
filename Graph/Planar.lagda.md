# Planar Graphs

We consider labelled graphs, where

```agda
module Graph.Planar (V E : Set) where
```

`V` labels the vertices and `E` labels the edges. Note that labels are
not necessarily unique. The labels are not the things themselves. The
vertices and edges are the _places which can be labelled_, i.e., they
are _positions_ within a container.

```agda
open import Lib.One
open import Lib.Sum
open import Lib.Equality
open import Lib.Sigma
open import Lib.Bwd
open import Lib.Star
open import Lib.Rel
open import Thin.Thin
open import Thin.Monoid
```

This file attempts to give an inductive definition of structures which
are *by construction* nonempty, finite, connected, planar graphs (with
multiple edges and self loops permitted).


## Sectors

A *sector* is a region near a vertex, in between two edges. That is, a
vertex of degree d has d sectors, provided each vertex has at least one
edge, a property I shall ensure by putting you in the picture and giving
you an edge by which to hold onto one vertex.

    you---e---(v)X

Each subsequent incident edge separates off another sector, e.g., this
self loop.

    you---e---(v)X
             X/X\
             /   \
             \_e_/

A sector is a place you can put a "you are here" sign.

```agda
module SECTOR (X : Set) where
```

I'm going to store an element of `X` in each sector. You will always be able
to project out the value stored in the sector where you are (and that will
yield the counit of a comonad).

As we construct the graph, we should remember those edges which we
have started but not yet finished. Planarity is induced by representing
this "connection debt" as a _stack_.

Every time we add an edge, our stack makes a transition. Most edges are
followed by another sector.

```agda
  data Edge : Bwd E -> Bwd E -> Set
  
  Turn : Bwd E -> Bwd E -> Set
  Turn ez fz = Edge ez fz  -- the next edge
             * X           -- the sector just the other side of it
```

Now, my plan is to construct a spanning tree, starting from a root node
which is connected by a "skyhook" edge to your hand. The skyhook ensures
that _all_ vertices have degree at least 1.

                 you
                  |
                  e
                 X|
                 (v)X
                / X \
               e     e
              /       \
            ...       ...

You're not necessarily "outside" the graph. Actually, there isn't an outside.
You're on a sphere.

A *spanning tree* is indexed by its initial and final stacks of connection
debt.

```agda
  record Spanner (dz ez : Bwd E) : Set
```

A *planar graph* is a spanning tree which starts and finishes debt-free.

```agda
  Planar = Spanner [] []
```

So, what's in a spanning tree?

```agda
  record Spanner dz ez where
    inductive
    constructor spanner
    field
      skyhook : E  -- arrive from parent along this edge
      vertex  : V  -- label this vertex
      sector  : X  -- sector between inEdge and rest of edges
      orbit   : Star Turn dz ez  -- rest of the edges and sectors
  open Spanner public
```

A node of a spanning tree has its skyhook edge, a vertex label, and a sector
immediately anticlockwise of the skyhook. There is then an orbit of further
edges and sectors.

But what is an edge?

```agda  
  data Edge where
```

As we work our way anticlockwise around a vertex, we will start some new edges,
increasing our connection debt,

```agda
    push : forall {ez} e -> Edge ez (ez -, e)
```

...and end some old ones, decreasing our connection debt,...

```agda
    pop  : forall {ez} e -> Edge (ez -, e) ez
```

...but if we want to connect to any other vertices, then sooner or later but
not both, we must visit it and grow its part of the spanning tree. The edge
we follow to reach it becomes its skyhook.

```
    span : forall {dz ez} -> Spanner dz ez -> Edge dz ez
```

If there is more than one edge to a vertex V from the vertex U (where you are)
you

1. *push* some UV edges without following them

2. *follow* one edge to vertex V

3. *pop* the UV edges you chose not to follow from U

4. *push* the VU edges you hadn't reached yet

5. get back to where you came in and *return* from V to U

6. *pop* the VU edges you started when you were exploring V

You get one representation of the graph for every spanning tree you can construct
from the sector where you are.


## Shunters

```agda
  record Shunty (R : Bwd E -> Bwd E -> Set) : Set where
    field
      shunt   : forall cz {dz ez} -> R dz ez -> R (cz -+ dz) (cz -+ ez)
  open Shunty public

  shEdge    : Shunty Edge
  shSpanner : Shunty Spanner
  shTurns   : Shunty (Star Turn)
  shunt shEdge cz (push e) = push e
  shunt shEdge cz (pop e)  = pop e
  shunt shEdge cz (span g) = span (shunt shSpanner cz g)
  shunt shSpanner cz (spanner e v x rxs) = spanner e v x (shunt shTurns cz rxs)
  shunt shTurns cz [] = []
  shunt shTurns cz (_,-_ {mz} (r , x) rxs) =
    (shunt shEdge cz r , x) ,- shunt shTurns cz rxs
```


## Moving Anticlockwise around the Root

I want to be able to move around in these graphs. We should be able to move the
root skyhook to any sector.

```agda
  record Rejig (R : Bwd E -> Bwd E -> Set) : Set where
    field
      rejig : forall {dz ez} -> R dz ez
        -> forall oz iz -> dz ~ (oz -+ iz)  -- outers (to turn) inners (not)
        -> forall uz                        -- already turned new outers
        -> -- if we popped far enough left, we'll have done some turning
           (  Bwd E >< \ nz -- noppers are not being turned
           -> Bwd E >< \ pz -- poppers are being turned
           -> Bwd E >< \ jz -- jumpers (actually, they were pushed)
           -> oz ~ (nz -+ pz)
            * ez ~ (nz -+ jz)
            * R (uz -+ iz) (uz -% pz -+ jz))
         + -- if we didn't get far enough left, not much changes
           (  Bwd E >< \ kz -- keepers
           -> ez ~ (oz -+ kz)
            * R (uz -+ iz) (uz -+ kz))
      gijer : forall {dz ez} -> R dz ez
        -> forall oz iz -> ez ~ (oz -+ iz)
        -> forall uz
        -> (Bwd E >< \ nz
           -> Bwd E >< \ pz
           -> Bwd E >< \ jz
           -> oz ~ (nz -+ pz)
            * dz ~ (nz -+ jz)
            * R (uz -% pz -+ jz) (uz -+ iz))
         + 
           (  Bwd E >< \ kz
           -> dz ~ (oz -+ kz)
            * R  (uz -+ kz) (uz -+ iz))
  open Rejig

  reEdge    : Rejig Edge
  reSpanner : Rejig Spanner
  reTurns   : Rejig (Star Turn)
  rejig reEdge (push e) oz iz q uz
    = inr (iz -, e , (_-, e $~ q) , push e)
  rejig reEdge (pop e)  oz (iz -, .e) r~ uz
    = inr (iz , r~ , pop e)
  rejig reEdge (pop e)  (oz -, e) []  r~ uz
    = inl (oz , [] -, e , [] , r~ , r~ , push e)
  rejig reEdge (span g) oz iz q uz
    with rejig reSpanner g oz iz q uz
  ... | inr (kz , q0 , g')
    = inr (kz , q0 , span g')
  ... | inl (nz , pz , jz , q0 , q1 , g')
    = inl (nz , pz , jz , q0 , q1 , span g')
  gijer reEdge (pop e)  oz iz q uz = inr (iz -, e , (_-, e $~ q) , pop e)
  gijer reEdge (push e) oz (iz -, .e) r~ uz = inr (iz , r~ , push e)
  gijer reEdge (push e) (oz -, e) [] r~ uz = inl (oz , [] -, e , [] , r~ , r~ , pop e)
  gijer reEdge (span g) oz iz q uz
    with gijer reSpanner g oz iz q uz
  ... | inr (kz , q0 , g')
    = inr (kz , q0 , span g')
  ... | inl (nz , pz , jz , q0 , q1 , g')
    = inl (nz , pz , jz , q0 , q1 , span g')
  rejig reSpanner (spanner e v x rxs) oz iz q uz
    with rejig reTurns rxs oz iz q uz
  ... | inr (kz , q0 , rxs')
    = inr (kz , q0 , spanner e v x rxs')
  ... | inl (nz , pz , jz , q0 , q1 , rxs')
    = inl (nz , pz , jz , q0 , q1 , spanner e v x rxs')
  gijer reSpanner (spanner e v x rxs) oz iz q uz
    with gijer reTurns rxs oz iz q uz
  ... | inr (kz , q0 , rxs')
    = inr (kz , q0 , spanner e v x rxs')
  ... | inl (nz , pz , jz , q0 , q1 , rxs')
    = inl (nz , pz , jz , q0 , q1 , spanner e v x rxs')
  rejig reTurns [] oz iz q uz = inr (iz , q , [])
  rejig reTurns ((r , x) ,- rxs) oz iz q uz
    with rejig reEdge r oz iz q uz
  rejig reTurns ((r , x) ,- rxs) oz iz q uz
    | inr (kz0 , q0 , r')
    with rejig reTurns rxs oz kz0 q0 uz
  ... | inr (kz1 , q1 , rxs')
      = inr (kz1 , q1 , (r' , x) ,- rxs')
  ... | inl (nz1 , pz1 , jz1 , q2 , q3 , rxs')
      = inl (nz1 , pz1 , jz1 , q2 , q3 , (r' , x) ,- rxs')
  rejig reTurns ((r , x) ,- rxs) oz iz q uz
    | inl (nz0 , pz0 , jz0 , q0 , q1 , r')
    with rejig reTurns rxs nz0 jz0 q1 (uz -% pz0)
  ... | inr (kz1 , q2 , rxs')
      = inl (nz0 , pz0 , kz1 , q0 , q2 , (r' , x) ,- rxs')
  ... | inl (nz1 , pz1 , jz1 , r~ , q3 , rxs')
      rewrite assoc-%-+ uz pz1 pz0 ~o
      = inl (nz1 , pz1 -+ pz0 , jz1
      , q0 -~- assoc-+-+ nz1 pz1 pz0 ~o
      , q3
      , (r' , x) ,- rxs')
  gijer reTurns [] oz iz q uz = inr (iz , q , [])
  gijer reTurns ((r , x) ,- rxs) oz iz q uz
    with gijer reTurns rxs oz iz q uz
  gijer reTurns ((r , x) ,- rxs) oz iz q uz
    | inr (kz0 , q0 , rxs')
    with gijer reEdge r oz kz0 q0 uz
  ... | inr (kz1 , q1 , r') = inr (kz1 , q1 , (r' , x) ,- rxs')
  ... | inl (nz1 , pz1 , jz1 , q2 , q3 , r')
      = inl (nz1 , pz1 , jz1 , q2 , q3 , (r' , x) ,- rxs')
  gijer reTurns ((r , x) ,- rxs) oz iz q uz
    | inl (nz0 , pz0 , jz0 , q0 , q1 , rxs')
    with gijer reEdge r nz0 jz0 q1 (uz -% pz0)
  ... | inr (kz1 , q2 , r')
      = inl (nz0 , pz0 , kz1 , q0 , q2 , (r' , x) ,- rxs')
  ... | inl (nz1 , pz1 , jz1 , r~ , q3 , r')
      rewrite assoc-%-+ uz pz1 pz0 ~o
      = inl (nz1 , pz1 -+ pz0 , jz1
      , q0 -~- assoc-+-+ nz1 pz1 pz0 ~o
      , q3
      , (r' , x) ,- rxs')

  rotate : Planar -> Planar
  rotate (spanner e v x0 ((r , x1) ,- rxs))
    with rejig reTurns rxs _ [] r~ []
  ... | inr ([] , r~ , rxs') = spanner e v x1 (rxs' >>*> ((r , x0) ,- []))
  ... | inl (.[] , pz , [] , r~ , r~ , rxs')
    with gijer reEdge r _ [] r~ []
  ... | inl ([] , pz' , [] , q0 , r~ , r')
    rewrite q0
    = spanner e v x0 ((r , x1) ,- rxs)
  rotate (spanner e v x0 ((r , x1) ,- rxs))
    | inl (.[] , [] , [] , r~ , r~ , rxs') | inr ([] , r~ , r')
    = spanner e v x1 (rxs' >>*> ((r , x0) ,- []))
  rotate (spanner e v x0 ((r , x1) ,- rxs))
    | inl (.[] , _ -, _ , [] , r~ , r~ , rxs') | inr ([] , () , r')
  rotate (spanner e v x []) = spanner e v x []
```
