# Dependent Types

## Introduction

Dependent types are an extension to the lambda calculus that grant the
programmer the ability to talk about types that depend upon values-- for
instance, you can write a function whose result type changes based upon what
value is passed in. Although this may seem like a pretty trivial thing, in
practice it can be used to write programs that encode invariants in the type
system, allowing you to write code that is provably correct.

The key trade-off, on the other hand, is that *elaboration* (more colloquially
sometimes referred to as "full type inference") is not decidable for a higher
order type system such as this one; principal types do not exist for
un-annotated terms, and to combat this, type annotations are needed on each
lambda. This is a big downgrade in terms of luxury compared to something like
an ML flavor or Haskell, where types can be fully inferred for you if you'd
like, so it may not be worth it to some.

The biggest changes immediately visible to the implementer are:

- The grammar for terms and types is now unified; there are no separate "expression" and "type" datatypes.
- There are now "universes" that are used to talk about the types of types-- more on that later.
- Function types `a -> b` are now replaced with "pi types" `Πx: a. b`.
- Product types `a * b`/`(a, b)` are now replaced with "sigma types" `Σx: a. b`.
- Tuples and functions must both now be type-annotated.

In this document I hope to explain all of these constructs, as well as give an
explanation for an implementation of a system involving them.

## Universes?

*"To answer that, we need to talk about parallel universes."* - pannenkoek2012

Some languages like to talk about types as first class citizens, by allowing
types to be acted on by functions. The naive, simple way of doing this is to
introduce a type named `Type`. Any type in the language, such as `Int`, has
`Type` as its type, and we say that `Type` likewise has the type `Type`.

```
---------------
Γ ⊢ Type : Type
```

However, I called this approach "naive" for a reason-- it actually gives rise
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
compromised, and you can write nonsensical proofs (or programs, in our case.)

The elegant solution to this problem is to introduce a new sort of type called
a "universe". Essentially, it will be like `Type`, but with an integer tag that
says how many "levels" up we are; the type of Universe 0 is Universe 1, the
type of Universe 1 is Universe 2, and so on.

```
-------------
Γ ⊢ Uₙ : Uₙ₊₁
```

It is also often useful to specify a heirarchy of *cumulative* universes; this
makes functions that are parametrized by a universe "more polymorphic" with
respect to the number of types they could be instantiated with, because types in
a lower universe are also valid members of the higher universe.

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

What this ends up looking like, for instance, is that you may write a function
such as:

```
id = λt: U₀. λx: t. x
```

Assuming `Int` has type `U₀`, I can write `id Int`, and that will beta-reduce
to `λx: Int. x`. Notice that the type of the λ-binder for `x` actually depends
upon that earlier binder `t`-- dependent types in action.

## Pi Types?

Pi types generalize the notion of function types `a -> b` to `Πx: a. b`;
function types are simply the degenerate case of pi-types where `b` does not
depend upon the value `x` of type `a`. For those who are interested, this
actually corresponds to universal quantification; the function type `Πx: a. b`
proposes that for all values `x` of type `a`, the proposition `b` can be
constructed, and creating a function with that type signature is proof of
that.

Given the expression `λt: U₀. λx: t. x` from earlier, we would write its type as
`Πt: U0. Πx: t. t`; the identity function yielded after the first application
has a type that depends upon the value of `t`.

## Sigma Types?

Sigma types, on the other hand, generalize the notion of product types `a * b`
(or, in Haskell, `(a, b)`) to `Σx: a. b`. Much like the relationship between
function types and pi types, product types are the edge case for sigma types
where `b` does not depend upon `x : a`. There is also a connection to logic--
the type `Σx: a. b` is tied to existential quantification, proposing there
exists at least one value `x` of type `a` such that `b` can be constructed, and
constructing a dependent pair with that type is proof of that.

## This System

This system is largely based on
[this article](http://math.andrej.com/2012/11/08/how-to-implement-dependent-type-theory-i/)
by Andrej Bauer; there are a few core differences to my implementation, however:

- I use De Bruijn indices, which he gets around to doing in part II, but he decide to use "explicit substitutions"-- I just do it normally.
- Beta-reduction is done "on the fly" as part of inference, rather than being its own function. In my opinion this makes things less error prone, and it also keeps the code much smaller.
- I implement a cumulative universe heirarchy.
- I implement dependent pairs, sigma types, and the fst/snd projections.
- He used a flavor of ML, whereas this is in Haskell.
- I opt to not do the extra normalization in `inferUnv`/`inferPi`, which he would consider a mistake; however, as my system does substitution on the fly and has no "global definition" context; I don't believe it's possible for `infer` to ever return a lambda. I challenge anyone reading to prove me wrong on that-- if you can, that would likely yield some large insight. However, I doubt that is possible. :)
- I implement the unit type and its constructor; `() : ()`.

There are some significant similarities worth noting as well:

- I still define the same sort of `inferPi`/`inferUnv` functions.
- Neither system implements eta-conversion of any sort, only beta-reduction.

Now on with the explanation.

### Terms / Types

As mentioned earlier, the grammar for terms and types is fused into one. I
define two types `AbsT a` and `ExpT a` with functor instances (for incrementing
de bruijn indices en masse later) and define aliases for them `Abs` and `Exp`
that set `a` to `Int`. Here `AbsT` holds onto a `T.Text` so that in a real
language you could have error messages that refer to the user-ascribed
variable names-- you'd likely have a "higher level" system that is converted
from a named representation to this one.

The system has De Bruijn indices, lambdas, application, universes, pi types,
dependent pairs, sigma types, and the projections `fst` and `snd`.

```Haskell
data AbsT a
  = Abs T.Text (ExpT a) (ExpT a)
  deriving (Eq, Functor)
type Abs = AbsT Int

data ExpT a                        -- e, t ::=
  = Idx a                          -- | #
  | Lam (AbsT a)                   -- | λx: t. e
  | App (ExpT a) (ExpT a)          -- | e e
  | Unv Int                        -- | U#
  | Pi  (AbsT a)                   -- | Πx: t. t
  | Tup (ExpT a) (ExpT a) (AbsT a) -- | (e, e) : (Σx : t. t)
  | Sgm (AbsT a)                   -- | Σx: t. t
  | Fst (ExpT a)                   -- | fst e
  | Snd (ExpT a)                   -- | snd e
  | Unit                           -- | ()
  | One                            -- | ()
  deriving (Eq, Functor)
type Exp = ExpT Int
```

## Substitution

First of all, we'll need a way of performing substitution. The basic algorithm
is:

- We start with a counter that we have set at 0.
- Whenever we come across an abstraction, we increment that counter by 1. The counter is not incremented when considering the type for the abstraction; only the body.
- If an index is equal to our counter, we perform the substitution.
- If an index is greater than our counter, we decrement it.
- If an index is less than our counter, we leave it untouched.

This way, indices are shifted to account for lambdas being removed, and of
course we need no variable names.

```Haskell
substRaw :: Int -> Exp -> Exp -> Exp
substRaw k w (Idx i)
  | i == k    = w
  | i > k     = Idx (i - 1)
  | otherwise = Idx i
substRaw k w (Lam (Abs x t e)) =
  Lam (Abs x (substRaw k w t) (substRaw (k + 1) w e))
substRaw k w (App a b) =
  App (substRaw k w a) (substRaw k w b)
substRaw k w (Pi (Abs x t e)) =
  Pi (Abs x (substRaw k w t) (substRaw (k + 1) w e))
substRaw _ _ (Unv u) = Unv u
substRaw k w (Tup a b (Abs x t e)) =
  Tup (substRaw k w a) (substRaw k w b) (Abs x (substRaw k w t) (substRaw (k + 1) w e))
substRaw k w (Sgm (Abs x t e)) =
  Sgm (Abs x (substRaw k w t) (substRaw (k + 1) w e))
substRaw k w (Fst e) = Fst (substRaw k w e)
substRaw k w (Snd e) = Snd (substRaw k w e)
substRaw _ _ Unit = Unit
substRwa _ _ One = One

subst :: Exp -> Exp -> Exp
subst = substRaw 0
```

## Subtyping

Here we introduce a subtyping relationship `subtype a b` that guarantees that
`a` can be passed into a function asking for `b`. This boils down to checking
for syntactic equality, because alpha-conversion isn't needed in de bruijn
indices. Other than that, we also say that if both `a` and `b` are universes,
then if the universe level of `a` is less than or equal to that of `b`, then
`a` is a subtype of `b`.

```Haskell
subtype :: Exp -> Exp -> Either T.Text ()
subtype (Unv a) (Unv b) | a <= b = Right ()
subtype a b | a == b = Right ()
subtype a b = Left $ "Attempt to pass `" <> tshow a <> "` as `" <> tshow b <> "`."
```

## Inference

**Gamma**

First, there's a type `Gam` (short for "Gamma") that represents the context,
mapping indices to their types-- this works like a stack. When we encounter an
abstraction, we'll "push that type onto the stack" by cons-ing it onto `Gam`
prior to recursing.

```Haskell
type Gam = [Exp]
```

**Helper Functions**

Then there are some helper functions we'll use to help us write `infer`, which
basically just call `infer` then make some guarantee about what kind of output
it had. `inferUnv` expects a universe output, `inferPi` expects a pi type
output, and `inferSgm` expects a sigma type output. You may be wondering why
there's an extra `Exp` bundled with their output that comes from `infer`--
I'll get to that next.

```Haskell
inferUnv :: Gam -> Exp -> Either T.Text (Int, Exp)
inferUnv g e = do
  (t, e') <- infer g e
  case t of
    Unv k -> Right (k, e')
    _ -> Left $ "Type expected, but got: " <> tshow t

inferPi :: Gam -> Exp -> Either T.Text (Abs, Exp)
inferPi g e = do
  (t, e') <- infer g e
  case t of
    Pi a -> Right (a, e')
    _ -> Left $ "Function expected, but got: " <> tshow t

inferSgm :: Gam -> Exp -> Either T.Text (Abs, Exp)
inferSgm g e = do
  (t, e') <- infer g e
  case t of
    Sgm a -> Right (a, e')
    _ -> Left $ "Sigma type expected, but got: " <> tshow t
```

**How Inference Works**

Inference in this system is actually merged with beta-reduction (or
"normalization" as the article called it) seeing as they would otherwise be
heavily mutually recursive, and it would be hard to spot how everything works.
As such, the type signature looks like as follows:

```Haskell
infer :: Gam -> Exp -> Either T.Text (Exp, Exp)
```

**Indices**

Inference for indices is simple; we check that the index is within bounds,
then shift the type we looked up by the index plus one using `fmap`, so as to
adjust it for its position. Beta-reduction for indices is a no-op, so we just
keep it as-is for the second element in the tuple.

```Haskell
infer g (Idx i)
  | i < length g = Right (fmap (+ succ i) (g !! i), Idx i)
  | otherwise = Left $ "Index out of bounds: " <> tshow i
```

**Lambdas**

Inference for lambdas is likewise easy-- we find the beta-reduced form of the
type, then use the context extended with that type to find the type and
beta-reduced form of the lambda's body. Then we have everything we need for
both the type and beta-reduction output. The reason we use `inferUnv` for
beta-reducing the type despite ignoring the universe output is because it's
necessary to gurantee that `t` is indeed a type-- otherwise we might accept
ill-formed programs.

```Haskell
infer g (Lam (Abs x t e)) = do
  (_, t') <- inferUnv g t
  (et, e') <- infer (t' : g) e
  Right (Pi $ Abs x t' et, Lam $ Abs x t' e')
```

**Application**

Application is a little bit more interesting. We use `inferPi` to check that
the first expression is indeed a function, and this gives us the normalized
form of the expression as well as its input and output types. Then, using
`infer` and `subtype`, we check that the type of the second expression matches
the input type of the first; if so, we check if the first expression is a
lambda or not. If it is, we can beta-reduce it; otherwise, we leave it
un-applied. The resulting type, on the other hand, is the result of substituting
the normalized form of the second expression into the resulting type using
`subst`.

```Haskell
infer g (App a b) = do
  (Abs _ t r, a') <- inferPi g a
  (bt, b') <- infer g b
  subtype bt t
  case a' of
    Lam (Abs _ _ e) -> Right (subst b' r, subst b' e)
    _ -> Right (subst b' r, App a' b')
```

**Universes**

The case for universes is pretty obvious-- increment them for the type,
keep them as-is for beta-reduction.

```Haskell
infer _ (Unv k) = Right (Unv (k + 1), Unv k)
```

**Pi Types**

Inference for Pi types is simple-- check the universes of the input and output
types, then take the greater of the two and that's the universe the pi type
belongs to. In finding the universe, we've also already found the beta-reduced
forms of the input and output types, so that's easy as well.

```Haskell
infer g (Pi (Abs x t e)) = do
  (tu, t') <- inferUnv g t
  (eu, e') <- inferUnv (t' : g) e
  Right (Unv $ max tu eu, Pi $ Abs x t' e')
```

**Dependent Pairs**

The code for dependent pair inference looks pretty long, but it's still fairly
easy to follow. It checks that the type of the first element is a subtype of the
first element in the sigma type, then checks that the type of the second element
is a subtype of the second element in the sigma type with the (beta-reduced)
first element substituted in (because the second type depends upon the value
of the first element.) Next, I check that the sigma type is valid, making sure
that its universe levels are the same-- unlike pi types, you can't just take
the greater of the two and call it a day, so this check is necessary.

```Haskell
infer g (Tup a b (Abs x t e)) = do
  (at, a') <- infer g a
  (bt, b') <- infer g b
  (tu, t') <- inferUnv g t
  (eu, e') <- inferUnv g e
  subtype at t'
  subtype bt (subst a' e')
  if tu == eu then
    Right (Sgm $ Abs x t' e', Tup a' b' $ Abs x t' e') 
  else
    Left "Universe levels of dependent pairs' elements must be the same."
```

**Sigma Types**

The case for sigma types is really easy-- it just finds the universes and
normalized forms of the two types, then does the same level check we did in
the rule for dependent pairs.

```Haskell
infer g (Sgm (Abs x t e)) = do
  (tu, t') <- inferUnv g t
  (eu, e') <- inferUnv g e
  if tu == eu then
    Right (Unv tu, Sgm $ Abs x t' e')
  else
    Left "Universe levels of sigma types' elements must be the same."
```

**Fst**

The first projection is easy; check that the expression is a sigma type, then
return the first of the two types. We don't perform eta reduction, so the `Fst`
stays "wrapped" for the beta-reduction output.

```Haskell
infer g (Fst s) = do                                                             
  (Abs _ t _, s') <- inferSgm g s                                                
  Right (t, Fst s') 
```

**Snd**

The second projection is only slightly trickier; it just substitutes the first
projection in for the output type, because the second type depends upon the
value of the first element.

```Haskell
infer g (Snd s) = do                                                             
  (Abs _ _ e, s') <- inferSgm g s                                                
  Right (subst (Fst s') e, Snd s') 
```

**Unit**

The type of Unit is One, and beta-normalization is a no-op.

```Haskell
infer _ Unit = Right (One, Unit)
```

**One**

The type of One is Universe 0, and beta-normalization is a no-op.

```Haskell
infer _ One = Right (Unv 0, One)
```

And that concludes the whole system. All in all, dependent types are pretty easy
to implement in a compact fashion, though you can probably get a lot fancier
when you start doing things like implicits, partial elaboration, and
eta-conversion, none of which is done here.
