# One

```agda
module Lib.One where
```

In the spirit of naming types after the number of values in them, `One` is the
type with one value.

```agda
record One : Set where constructor <>
```

It is declared as a `record`, which means it is defined by its
`fields`...but there are no fields. To give a value in a record type
is to define all its fields, which is very easy to do if there are
none. Even so, it is permitted to give a record type a `constructor`,
which generates the values from the fields. Here, `<>` is a constant
of type `One`, abbreviating `record {}`, the record with no fields.

A consequence of making `One` a `record` type is that Agda treats
things of type `One` as equal if they are equal *fieldwise*, and as
there are no fields, that is trivially the case. (In the jargon, we
say that records have an &lsquo;&eta;-rule&rsquo;: every element of a
record type is automatically equal to the canonical record built by
collecting its projections. Here, every record in `One` is equal to
`record {}`, i.e., `<>`.)

Correspondingly, to be given an inhabitant of `One` is to be given
information of *no consequence*. However, if you are *asked* for an
element of `One`, you have indeed won.
