# Dependent Types

Dependent types are a fairly simple extension to the lambda calculus that allows
the programmer to write types that depend upon values; more information is given
below for those who are interested.

The files `bruijn.hs` and `bruijn.ml` are implementations of very basic
dependent type systems written in Haskell and [Amulet](https://amulet.works)
respectively. They both support Pi types and universes, but lack any sort of
type variables or recursion-- any polymorphic functions would need to have
types passed in explicitly. I also opted to not implement Sigma types yet,
though that may be done later. The code for both versions is largely adapted
from [this article,](http://math.andrej.com/2012/11/08/how-to-implement-dependent-type-theory-i/)
with a little bit of work to convert it to use de bruijn indices instead (hence
the filenames.)

## Universes

Some languages like to talk about types as first-class values, allowing you to
write functions that operate on types. The naiive approach to this is to
introduce a type named `Type` that is the type of all types-- if we ask what the
type of, say, `Int` is, we'll get `Type`. We could more generally say that
anything that can be used as a type has the type `Type`:

```
Γ ⊢ x : t
------------
Γ ⊢ t : Type
```

And so if we ask what the type of `Type` is, we'll get `Type` back again:

```
---------------
Γ ⊢ Type : Type
```

However, I called this approach "naiive" for a reason-- it actually gives rise
to [Girard's Paradox.](http://liamoc.net/posts/2015-09-10-girards-paradox.html)
If you are familiar with
[Russell's Paradox](https://en.wikipedia.org/wiki/Russell%27s_paradox), it is
the type-theoretic analogue of that. For those that aren't, the issue with
allowing a type or set to contain itself is that you are then able to pose the
following question: "Does the set of all sets that do not contain themselves
contain itself?". If you answer "yes", then it contains itself and therefore
doesn't fit the requirement-- if you answer "no", then it does not contain
itself and therefore fits the requirement and ought to contain itself. As such,
it is both true and false at the same time-- so if the
[principle of explosion](https://en.wikipedia.org/wiki/Principle_of_explosion)
is present, then you can prove anything, which means your type safety is now
compromised, and you can write nonsensical proofs.

The elegant solution to this problem is to introduce "universes"; essentially,
attaching an integer to `Type` to say how many levels up we are. the type of
`Int` could be `Universe 0` (`Int : U₀`) and the type of Universe 0 is
Universe 1 (`U₀ : U₁`). More generally:

```
-------------
Γ ⊢ Uₙ : Uₙ₊₁
```

It is also often useful to say that universes are *cumulative*; that is, an
element of a given universe is also an element of all universes above that
level:

```
Γ ⊢ x : Uₙ
------------
Γ ⊢ x : Uₙ₊₁
```

One temptation might be to think about some universe at "level infinity", but if
you do that then you've gone back to square one-- this "universe infinity"
would contains all universes and all types, including itself, so it is more or
less the same as the `Type` that we worked so hard to avoid. So, put simply,
universes must have a finite level, even though there are potentially infinitely
many.

In the context of the language presented, universes are interesting as a means
for polymorphism; they can be used with lambdas just like a "normal" type, so
you can write functions like:

```
id = λt: U0. λx: t. x
```

which may be applied to a type as the first argument; for instance, `id Int`
reduces to `λx: Int. x`

## Pi Types

Pi types are a generalization of function types-- in ML or Haskell one would
write `a -> b` to mean a function from type `a` to type `b`. In a dependently
typed system, this type is instead written `Πx: a. b`, where, as the notation
suggests, `x` has the type `a` (`x : a`). The reason for this is to allow
types which depend upon values; hence the name *dependent types*.

Given the `id` example from earlier, we can write its type as
`Πt: U0. Πx: t. t`. As you can see, the type of the identity function depends
upon the value of `t`, which will be a type.

## Sigma Types

Sigma types are a generalization of tuples-- in ML or Haskell one would write
`a * b` or `(a, b)` respectively to mean a product of the types `a` and `b`.
Similar to Pi types, Sigma types take the form `Σx: a. b`; it is a tuple of
two values, one of type `a` and one of type `b`, where the type `b` depends
upon the value of `x`.
