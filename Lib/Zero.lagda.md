# Zero

```agda
module Lib.Zero where
```

I like to name types after the number of values in them, starting with *none*
*at* *all*.

```agda
data Zero : Set where
```

It is impossible to manufacture values in the `Zero` type. As such, it's a
good type to use as evidence for the *impossible*.

It is extremely useful to possess a value in the `Zero` type. That can't
happen in real life, but it can happen *hypothetically*. And when it does,
you win, instantly!

```agda
naughty : forall {l}{P : Set l} -> Zero -> P
naughty ()
```

For a program which doesn't do anything, ever, there is quite a lot to say
about it.

Firstly, there are some funny looking curly braces in its type. These mark
arguments which are *implicit* by default. That means we don't write them
either at definition sites or at use sites. Here `l` and `P` are marked as
implicit. In the program, `naughty` has one explicit argument, namely `()`,
and that is a *pattern* which must cover the type of the first explicit
argument: that type is `Zero`.

Secondly, that pattern `()` is known as the *absurd* pattern. You can also
call it &lsquo;My Aunt Fanny&rsquo;, provided that you do so while
impersonating [the Glaswegian tones](https://youtu.be/y_JscVUQ6hs) of
[Bill Paterson](https://www.imdb.com/name/nm0665473/) in
[Episode One of
*Smiley's People*](https://www.imdb.com/title/tt1074420/?ref_=ttep_ep1).
It's a way of casting aspersions at something in particular and saying
&lsquo;*I* don't have to give you an answer, because *you* can't ask that
question.&rsquo;. If you have the absurd pattern on the left-hand side of
a program, there is no need to provide a right-hand side.

Thirdly, that `l` is a type-theoretic *level*, after the fashion of
[Bertrand Russell](https://en.wikipedia.org/wiki/Bertrand_Russell).
Types which talk about no types at all are at level 0; types which talk
about level 0 types are level 1 types; types which talk about level 1 types
are level 2 types; and so ad infinitum.

Fourthly, `Set l` is the type of types at level `l`. The word `Set` is used
to distinguish types that represent some sort of data from those which have
no useful data content, and are classified as inhabiting `Prop`.

Fifthly, reading the type as a whole, it says &lsquo;Whatever type of thing
you want, however far up the type-theoretic hierarchy it may be, such a thing
can be yours if you already possess a value in `Zero`.&rsquo;. That's what I
mean by &lsquo;you win&rsquo;.

Lastly, the name `naughty` was suggested by Peter Hancock (of whom more anon).
It means &lsquo;wicked&rsquo;, and if you have an element of `Zero`, someone
surely has been so. It is also pronounced &lsquo;Nought E&rsquo;, where
&lsquo;nought&rsquo; is an archaic word for &lsquo;nothing&rsquo; or the
*digit* 0, and &lsquo;E&rsquo; abbreviates &lsquo;elimination&rsquo;. An
*elimination rule* tells you what good it is to know something. When you
know something impossible, you become very powerful indeed. Enthusiasts for
Latin might also say *ex falso quodlibet*.
