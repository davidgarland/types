# Bidirectional Type Checking

## Introduction

Bidirectional type checking is a style of type checking that splits the job of inferring types
into two primary judgements, a "checking" judgement `e ⇐ A` and a "synthesis" judgement `e ⇒ A`.

The judgement `e ⇐ A` is responsible for checking that the expression `e` has the type `A`,
and making any changes to the context required to accomodate that. For instance, if the type
of `e` was unknown and assigned some type variable, then that might be instantiated by whatever `A` is.

On the other hand, the judgement `e ⇒ A` is responsible for synthesizing a general type `A` for
the expression `e`.

The two are used in tandem via mutual recursion-- checking judgement rules may refer to synthesis judgements,
and vice versa (though in a way that terminates, of course). Once everything is set up correctly, you could
simply run the synthesis judgement on your program to get an inferred and type-checked type.

## This System

This system in specific uses the paper
[Complete and Easy Bidirectional Type-Checking for Higher-Rank Polymorphism](https://www.cl.cam.ac.uk/~nk480/bidir.pdf)
by Dunfield and Krishnaswami.

In their system, they add one additional "primary" judgement:

- An "application" judgement `A • e ⇒⇒ C` that says that a function of type `A` applied to some expression `e` synthesizes the type `C`.

And three "supplementary" ones:

- A subtyping relation `A <: B` that guarantees that A is "at least as polymorphic as" B-- for instance, the type `1 -> ∀a. a` is a subtype of `1 -> 1`. Another way to frame it is that if `A <: B`, then A can be passed into a function requiring B; under this analogy, `∀a. a` being passable as `1` makes it clear that `(∀a. a) <: 1`. The opposite is not true, because a function requiring `∀a. a` cannot have `1` passed in-- therefore `1 <: ∀a. a` is **false**, and would lead to a compile-time error.
- A "left instantiation" rule that they use a fancy non-unicode symbol for-- I'll write it as `instL(∃a, A)`-- that instantiates the existential type variable `∃a` such that `∃a <: A`.
- A "right instantiation" rule that they use a fancy non-unicode symbol for-- I'l write it as `instR(A, ∃a)`-- that instantiates the existential type variable `∃a` such that `A <: ∃a`.

Implementing these using their algorithmic specification is the goal of this document.

### Terms

First of all, they define a very simple term-level language, with variable references, the unit value, lambdas,
function application, and a type coercion operator.

```
e ::= x 
    | ()
    | λx. e
    | e e
    | (e : A)
```

I translate this to the following Haskell, defining a type `Name` for `x` and a type `Expr` for `e`. The `Int` attached
to `Name` is for alpha-conversion purposes, which I won't be going over as its implementation is not novel.

```Haskell
data Name
  = Name T.Text Int
  deriving (Eq, Ord)

data Expr          -- e ::=
  = Unit           -- | ()
  | Ref  Name      -- | x
  | Lam  Name Expr -- | λx. e
  | App  Expr Expr -- | e e
  | OfTy Expr Type -- | (e : A)
```

### Types

It gets marginally more interesting in the type-level language (I've opted to write `a` where they wrote `α`,
and replace the "hat" for existential variables with the prefix `∃`), where they divide type variables into
those that are to be forall-quantified and those that are to be existentially quantified. They also have an
explicit forall constructor (hence the "For Higher-Rank Polymorphism" in the title of the paper).

```
A, B, C ::= 1 
          | a
          | ∃a
          | ∀a. A
          | A → B
```

Much like the term grammar, this translates to Haskell pretty nicely:

```Haskell
data Type          -- A, B, C ::=
  = One            -- | 1
  | TVar Name      -- | a
  | Exs  Name      -- | ∃a
  | For  Name Type -- | ∀a. A
  | Fun  Type Type -- | A -> B
```

### Contexts

Next, they define a language of ordered contexts-- their definition as a BNF grammar isn't just for show,
it actually defines more or less how they should work. Implementing contexts here as some myriad of hash maps
and hash sets isn't possible here-- it needs to be a list.

- `·` denotes the empty context.
- `Γ, a` extends the context with a forall-quantified type variable `a`.
- `Γ, x : A` extends the context with the fact that the variable `x` has the type `A`.
- `Γ, ∃a` extends the context with the fact that an existential type variable `∃a` exists.
- `Γ, ∃a = t` extends the context with the fact that an existential type variable `∃a` exists and is equal to `t`.
- `Γ, ▶∃a` adds a "scope marker" to the context that we can use to cut everything following it later on, in the case that one of our judgements produces "garbage" in the context that we don't want to propagate.

They also introduce a rather nifty syntactic shorthand.

- `Γ[a]` is shorthand for `Γ, a, Γ'`. This allows us to kind of pretend like Γ is a mapping and that we can "project" `a`, even though it is in reality an ordered list.

```
Γ, ∆, Θ ::= ·
          | Γ, a
          | Γ, x : A
          | Γ, ∃a
          | Γ, ∃a = t
          | Γ, ▶∃a
```

To translate this, I define a datatype `CtxKind` of the different kinds of context entries:

- `Mono` denoting `x : A`.
- `Poly` denoting `a`.
- `Exst` denoting either `∃a` or `∃a = t`.
- `Mark` denoting `▶∃a`.

As well as a type `Ctx` that is an associative list from `(CtxKind, Name)` to `Maybe Type`.

Using this new type `Ctx`, I'll also define a monad transformer `Infer t` as a shorthand so that
we can implicitly pass around a context and an infinite, lazy list of fresh variable names
(taken from [here](https://github.com/plt-abigail/mld/blob/fcf7971f824aa81ff5a51c5d3da6801d6aaeb40d/src/Typing/Monad.hs#L29)),
as well as being able to throw type checking errors via `throwError`.

```Haskell
data CtxKind -- Γ, ∆, Θ ::= ·
  = Mono     -- | Γ, x : A
  | Poly     -- | Γ, a
  | Exst     -- | Γ, ∃a | Γ, ∃a = t
  | Mark     -- | Γ, ▶∃a
  deriving (Eq, Show)
type Ctx = [((CtxKind, Name), Maybe Type)]

type Infer t = ExceptT T.Text (State (Ctx, [Name])) t
```

### Omitted "Boring" Functions

The following functions have uninteresting implementations and would clutter this write-up; the below explanations
should hopefully help if what they do isn't obvious or implied by how the sequent rules later on work. Alternatively,
you could look at the source code that this document is describing in the first place-- all of these functions have
concrete implementations.

- `ftv` yields the set of free type variables in a `Type`.
- `subst n a b` substitutes the type `a` in wherever the type variable with the name `n` is found, replacing it with `b`.
- `ctxInst k n t` instantiates the context entry with `(k, n)` as its key to have the value `Just t`.
- `ctxCut k n` "cuts" the context up to some entry with `(k, n)` as its key. This is what `Mark` is for.
- `ctxIdx k n` finds the index in the associative list with the key `(k, n)`.
- `ctxFind k n` performs an associative list lookup with the key `(k, n)`.
- `ctxHas t` guarantees the type `t` is well-formed in the current context.
- `ctxAppend c` adds the context `c` to the current context by doing a "dumb" concatenation-- no shadowing checks.
- `ctxPrepend k n c` adds the context `c` prior to the context entry with `(k, n)` as its key.

### Context Application

In the paper, they require that a context can be "applied to" a type as a substitution--
what this really means is that the type's existential type variables are replaced with
what the context specifies. I won't bother showing the formal definition, as it's
about as simple as it sounds; instead, here's the code, which is all one-liners anyways.

The only really interesting part here is that `ctxApply` is recursed upon again after resolving
the existential variable, because an existential can be instantiated as another existential--
so this makes sure to expand it fully.

```Haskell
ctxApply :: Type -> Infer Type
ctxApply One = pure One
ctxApply (TVar x) = pure $ TVar x
ctxApply (Exs x) = ctxFind Exst x >>= maybe (pure $ Exs x) ctxApply
ctxApply (For x t) = For x <$> ctxApply t
ctxApply (Fun a b) = Fun <$> ctxApply a <*> ctxApply b
```

### Subtyping

First of all, we must implement the subtyping judgement that corresponds to `A <: B` in the paper. Given
that it doesn't have any sort of "result" outside of modifiying the context or failing, we'll assign it
the following type:

```Haskell
subtype :: Type -> Type -> Infer ()
```

**[<:Unit]**

Let's begin with the simplest rule, for subtyping the unit type to itself.
This reads as "Given the input context `Γ`, `1` is a subtype of `1`, and `Γ` is the output context.",
from left to right.

```
-------------- [<:Unit]
Γ ⊢ 1 <: 1 ⊣ Γ
```

The corresponding Haskell is pretty easy; just do nothing. After all, we don't make any
requirements of what the context contains, nor do any additional calls.

```Haskell
subtype One One = pure ()
```

**[<:Var]**

The rule for variable subtyping is likewise simple:

```
-------------------- [<:Var]
Γ[a] ⊢ a <: a ⊣ Γ[a]
```

In the corresponding code, we check if the variables are equal in name; if not, we fall through
to the next typing rule. If so, we check that the name exists as a `Poly` entry in the context,
and then yield `()` if so. Otherwise, an error is thrown.

```Haskell
subtype (TVar a) (TVar a') | a == a' = ctxHas (TVar a)
```

**[<:Exvar]**

And the rule for subtyping existential variables is pretty much identical to that for the usual
type variables:

```
------------------------ [<:Exvar]
Γ[∃a] ⊢ ∃a <: ∃a ⊣ Γ[∃a]
```

```Haskell
subtype (Exs a) (Exs a') | a == a' = ctxHas (Exs a)
```

**[<:->]**

Finally, things start to get a little bit more interesting, starting with the rule for subtyping functions;
given `A -> A' <: B -> B'`, we perform the judgement `B <: A` for the domain, then turn around and do the opposite
`[Θ]A' <: [Θ]B'` for the codomain, which seems pretty baffling at first. 

However, it is in reality pretty simple to demonstrate. Beforehand, recall that `A <: B`
(`A` is a subtype of `B` / `B` is a supertype of `A`) means that `A` is "at least as polymorphic as"
`B`, or "can be passed to a function as" `B`. For instance, `(∀a. a) <: 1`.

So, given some function of type `(∀a. a -> 1) -> 1`, we wouldn't expect to be
able to pass in `1 -> 1`. The way we prevent this kind of behaviour is to say that `B <: A`;
the domain of the function being made a supertype must be a subtype of the domain of the function being subtyped.

On the other hand, the codomain has the opposite rule; given a function of type `(1 -> 1) -> 1`, we might want
to pass in `1 -> ∀a. a`-- therefore we say that `A' <: B'`, so that the codomain of the function being subtyped
must be a subtype of the codomain of the function being made a supertype.

```
Γ ⊢ B <: A ⊣ Θ   Θ ⊢ [Θ]A' <: [Θ]B' ⊣ ∆
--------------------------------------- [<:->]
      Γ ⊢ A -> A' <: B -> B' ⊣ ∆
```

This is easy to translate; we simply run `subtype b a`, which
implicitly mutates the current context from `Γ` to `Θ`, then apply
the context using `ctxApply` in order to get the values `[Θ]A'` (as `a''`)
and `[Θ]B'` (as `b''`) respectively, and then subtyping them to get the output
context `∆`.

```Haskell
subtype (Fun a a') (Fun b b') =
  subtype b a >> (join $ subtype <$> ctxApply a' <*> ctxApply b')
```

**[<:∀L]**

This rule is fairly straightforward-- to unify a forall-quantified
type with some other arbitrary one, we just toss out the forall-quantifier
and extend the context with an existential variable that we cut out afterwards
using a marker.

```
Γ, ▶∃a, ∃a ⊢ [∃a/a]A <: B ⊣ ∆, ▶∃a, Θ
------------------------------------- [<:∀L]
         Γ ⊢ ∀a. A <: B ⊣ ∆
```

```Haskell
subtype (For x a) b = do
  ctxAppend [((Mark, x), Nothing), ((Exst, x), Nothing)]
  subtype (subst x (Exs x) a) b
  ctxCut Mark x
```

**[<:∀R]**

Similar to `[<:∀L]`, but we extend the context with `a` as a polymorphic type variable
directly, rather than doing an existential type variable with a marker.

```
Γ, a ⊢ A <: B ⊣ ∆, a, Θ
------------------------ [<:∀R]
   Γ ⊢ A <: ∀a. B ⊣ ∆
```

And again, the Haskell is likewise simple; it's short enough that I'll
throw it all on one line, chaining with `>>`.

```Haskell
subtype a (For x b) =
  ctxAppend [((Poly, x), Nothing)] >> subtype a b >> ctxCut Poly x
```

**[<:InstantiateL]**

This rule deals with the case `∃a <: A`, which is non-trivial-- in fact,
we define a separate judgement `instL` like the authors did that does
most of the heavy lifting in this rule. The only other part to it is checking
that the existential variable doesn't occur free in the type `A`, so as to
prevent infinite looping or the need for some form of recursive types.

```
∃a ∉ FV(A)   Γ[∃a] ⊢ instL(∃a, A) ⊣ ∆
------------------------------------- [<:InstantiateL]
        Γ[∃a] ⊢ ∃a <: A ⊣ ∆
```

This is pretty simple-- just check that the context contains the type
`∃a` (named `x` here), error if it's a free type variable in `A` (named `b` here),
then do the call to `instLeft`.

```Haskell
subtype (Exs x) b = do
  ctxHas (Exs x)
  errIf (x `S.member` ftv b) $ "Failed to unify `" <> tshow x <> "` with `" <> tshow b <> "`."
  instLeft (Exs x) b
```

**[<:InstantiateR]**

Pretty much the exact same as `[<:InstantiateL]` but, well, instantiating the right-hand-side instead.

```
∃a ∉ FV(A)   Γ[∃a] ⊢ instR(A, ∃a) ⊣ ∆
------------------------------------- [<:InstantiateR]
         Γ[∃a] ⊢ A <: ∃a ⊣ ∆
```

```Haskell
subtype a (Exs x) = do
  ctxHas (Exs x)
  errIf (x `S.member` ftv a) $ "Failed to unify `" <> tshow x <> "` with `" <> tshow a <> "`."
  instRight a (Exs x)
```

### Left Instantiation

Now we can get onto left instantiation, the judgement we've been writing as `instL(∃a, A)`. As a quick recap of what I said earlier, it is responsible for guaranteeing that `∃a` is instantiated such that `∃a <: A`. Much like the
subtyping judgement, it simply takes two types as inputs and either fails, has no effect, or modifies the context, so we'll
assign it the same type:

```Haskell
instLeft :: Type -> Type -> Infer ()
```

**[InstLReach]**

First, let's do the rule for instiating one existential variable to another;
it simply checks that both existential variables are already present in the context,
then instantiates the second variable to the first.

```
------------------------------------------ [InstLReach]
Γ[∃a][∃b] ⊢ instL(∃a, ∃b) ⊣ Γ[∃a][∃b = ∃a]
```

The Haskell is pretty simple; we use `ctxIdx` to query that the two existentials
exist in the context and that their positions are correct-- we don't want to
instantiate `y` to `x` if it's not valid in the context prior to `y`.

```Haskell
instLeft (Exs x) (Exs y) = do
  xi <- ctxIdx Exst x
  yi <- ctxIdx Exst y
  errIf (xi > yi) "Invalid left-instantiation."
  ctxInst Exst y (Exs x)
```

**[InstLArr]**

Then there's the rule for functions, which is one of the more complicated ones
in the system. In order to solve  the judgement `instL(∃a, A -> A')`, it introduces existential
variables `∃a''` and `∃a'` to represent the function input/output types of `∃a`,
such that `∃a` is instantiated as `∃a' -> ∃a''`. Then, it proceeds to instantiate
`∃a'` such that `A <: ∃a'`, yielding output context `Θ`. It then instantiates `∃a''`
such that `∃a'' <: [Θ]A'`, finally yielding the desired output context `∆`.

The reasoning behind using `instR(A, ∃a')` instead of `instL(∃a', A)` has to do with the subtyping relationship
they imply-- when saying `A -> A' <: B -> B'`, we say that `B <: A` and `A' <: B'`, so that logic carries over here
because our type `∃a` is being made into a function. Therefore, we want `A <: ∃a'`, `∃a'' <: [Θ]A'`,
so we use instR and instL accordingly.

```
Γ[∃a'', ∃a', ∃a = ∃a' -> ∃a''] ⊢ instR(A, ∃a') ⊣ Θ   Θ ⊢ instL(∃a'', [Θ]A') ⊣ ∆
-------------------------------------------------------------------------------- [InstLArr]
                     Γ[∃a] ⊢ instL(∃a, A -> A') ⊣ ∆
```

The resulting Haskell code is a little big as well; we need to generate fresh names for `∃a'`
and `∃a''` via `freshNam`, prepend them into the context prior to where `∃a` already resides using
`ctxPrepend`, then instantiate `∃a` such that it is equal to `∃a' -> ∃a''` with `ctxInst`. The rest
is as you'd expect from the maths, simply doing the instantiations and the context application `[Θ]A'`.

```Haskell
instLeft (Exs x) (Fun a b) = do
  x' <- freshNam
  x'' <- freshNam
  ctxPrepend Exst x [((Exst, x''), Nothing), ((Exst, x'), Nothing)]
  ctxInst Exst x (Fun (Exs x') (Exs x''))
  instRight a (Exs x')
  b' <- ctxApply b
  instLeft (Exs x'') b'
```

**[InstLAllR]**

This rule is fairly simple-- we just check that `∃a` exists, toss the forall-quantifier aside but extend the context
with its type variable, then do a cut so that the type variable and anything following it don't escape.

```
Γ[∃a], b ⊢ instL(∃a, B) ⊣ ∆, b, ∆'
---------------------------------- [InstLAllR]
   Γ[∃a] ⊢ instL(∃a, ∀b. B) ⊣ ∆
```

```Haskell
instLeft (Exs x) (For a t) = do
  ctxHas (Exs x)
  ctxAppend [((Poly, a), Nothing)]
  instLeft (Exs x) t 
  ctxCut Poly a
```

**[InstLSolve]**

Finally, we add a "catch-all" case for the remaining monotypes, which is fairly simple at a glance--
but you may think it's odd they didn't use their more concise `Γ[∃a]` notation instead here. The reason
for that is because we need to be able to have `Γ` refer to the context *prior to* `∃a` in order to
check that `τ` is well-formed under only that subset of the context.

```
                  Γ ⊢ τ
--------------------------------------- [InstLSolve]
Γ, ∃a, Γ' ⊢ instL(∃a, τ) ⊣ Γ, ∃a = τ, Γ'
```

Because of the novelty noted above, the code is a little interesting as well; we
explicitly fetch the context, so that it can be restored with the instantiation
performed after we've verified that `τ` is well-formed under `Γ`.

```Haskell
instLeft (Exs x) t = do
  s <- get
  ctxCut Exst x
  ctxHas t
  put s
  ctxInst Exst x t
```

### Right Instantiation

Similar to left-instantiation, but with the existential on the right-hand-side, yielding
the relationship `A <: ∃a`. The type signature is the same:

```Haskell
instRight :: Type -> Type -> Infer ()
```

**[InstRReach]**

If you understood `[InstLReach]`, this is really no different-- it's just that `∃b` is now on
the left-hand side in the judgement (but is on the same side in the context.)

```
------------------------------------------ [InstRReach]
Γ[∃a][∃b] ⊢ instR(∃b, ∃a) ⊣ Γ[∃a][∃b = ∃a]
```

```Haskell
instRight (Exs x) (Exs y) = do
  xi <- ctxIdx Exst x
  yi <- ctxIdx Exst y
  errIf (yi > xi) "Invalid right-instantiation."
  ctxInst Exst x (Exs y)
```

**[InstRArr]**

Pretty much the same as `[InstLArr]`, except with opposite judgements, and
the arguments are flipped.

```
Γ[∃a'', ∃a', ∃a = ∃a' -> ∃a''] ⊢ instL(∃a', A) ⊣ Θ   Θ ⊢ [Θ] instR(A', ∃a'') ⊣ ∆
-------------------------------------------------------------------------------- [InstRArr]
                           Γ[∃a] ⊢ instR(A -> A', ∃a) ⊣ ∆
```

```Haskell
instRight (Fun a b) (Exs y) = do
  y' <- freshNam
  y'' <- freshNam
  ctxPrepend Exst y [((Exst, y''), Nothing), ((Exst, y'), Nothing)]
  ctxInst Exst y (Fun (Exs y') (Exs y''))
  instLeft (Exs y') a
  b' <- ctxApply b
  instRight b' (Exs y'')
```

**[InstRAll]**

Whereas `[InstLAll]` just introduced the type variable in a still-polymorphic form,
here we do an existential variable with a marker instead.

```
Γ[∃a], ▶∃b, ∃b ⊢ instR([∃b/b]B, ∃a) ⊣ ∆, ▶∃b, ∆'
------------------------------------------------ [InstRAll]
         Γ[∃a] ⊢ instR(∀b. B, ∃a) ⊣ ∆
```

```Haskell
instRight (For a t) (Exs y) = do
  ctxHas (TVar a)
  ctxAppend [((Mark, a), Nothing), ((Exst, a), Nothing)]
  instRight (subst a (Exs a) t) (Exs y) 
  ctxCut Mark a
```

**[InstRSolve]**

Then we do the same sort of "catch-all" case we did for InstL, this time with
the arguments to the judgement flipped-- that is all.

```
                Γ ⊢ τ
-------------------------------------- [InstRSolve]
Γ, ∃a, Γ' ⊢ instR(τ, ∃a) ⊣ Γ, ∃a=τ, Γ'
```

```Haskell
instRight t (Exs y) = do
  s <- get
  ctxCut Exst y
  ctxHas t
  put s
  ctxInst Exst y t
```

### Checking

Now that our subtyping judgement is complete with its supplementary left/right instantiation judgements,
we can get onto the "checking" judgement `e ⇐ A`. The type is as simple as you'd expect:

```Haskell
check :: Expr -> Type -> Infer ()
```

**[1I]**

Let's start with the simplest case; checking the unit value `()` against the
unit type `1`. This is pretty much a no-op; it always succeeds with no dependence
upon-- or modification to-- the environment.

```
-------------- [1I]
Γ ⊢ () ⇐ 1 ⊣ Γ
```

```Haskell
check Unit One = pure ()
```

**[->I]**

Next there's the rule for checking lambdas against function types;
when trying to check `λx. e` against `A -> B`, we simply check
`e` against `B` with the added assumption `x : A`. Afterwards,
we cut the assumption `x : A` and anything after it out, so as
to avoid it escaping.

```
Γ, x : A ⊢ e ⇐ B ⊣ ∆, x : A, Θ
------------------------------ [->I]
    Γ ⊢ λx. e ⇐ A -> B ⊣ ∆
```

```Haskell
check (Lam x e) (Fun a b) = 
  ctxAppend [((Mono, x), Just a)] >> check e b >> ctxCut Mono x
```

**[∀I]**

There's also a case for checking against forall-quantified types;
we extend the context with the polymorphic variable specified by
the quantifier, but toss the quantifier aside when recursing.
Afterwards, we cut the polymorphic quantifier and anything after it
so as to avoid them escaping.

```
Γ, a ⊢ e ⇐ A ⊣ ∆, a, Θ
---------------------- [∀I]
  Γ ⊢ e ⇐ ∀a. A ⊣ ∆
```

```Haskell
check e (For a t) =
  ctxAppend [((Poly, a), Nothing)] >> check e t >> ctxCut Poly a
```

**[Sub]**

Finally, there is a "catch-all" case `[Sub]` for checking that
gets any of the remaining cases. When checking `e ⇐ B`, we
simply use the synthesis judgement `e ⇒ A ⊣ Θ` and then verify
that `[Θ]A <: [Θ]B`-- in other words, verifiying that the type
we would naturally infer for `e` is at least as polymorphic as
the type that we're checking it has.

```
Γ ⊢ e ⇒ A ⊣ Θ   Θ ⊢ [Θ]A <: [Θ]B ⊣ ∆
------------------------------------ [Sub]
            Γ ⊢ e ⇐ B ⊣ ∆
```

```Haskell
check e t =
  join $ subtype <$> (synth e >>= ctxApply) <*> ctxApply t
```

### Application

Now we can do the "application" judgement `A • e ⇒⇒ C`; as a recap, this means that a function of
type `A` applied to some expression `e` synthesizes the type `C`. Given that it has a proper
return value in the form of the type `C`, the type we give it reflects that fact:

```Haskell
applyType :: Type -> Expr -> Infer Type
```

**[∃aApp]**

Our first case is where we apply an existential type variable `∃a` to some
expression `e`; we say that our existential type variable `∃a` is a function
`∃a' -> ∃a''`, and then we check that `e ⇐ ∃a'`. If so, then `∃a • e ⇒⇒ ^∃a''`.

```
Γ[∃a'', ∃a', ∃a = ∃a' -> ∃a''] ⊢ e ⇐ ∃a' ⊣ ∆
-------------------------------------------- [∃aApp]
         Γ[∃a] ⊢ ∃a • e ⇒⇒ ^∃a'' ⊣ ∆
```

```Haskell
applyType (Exs x) e = do
  ctxHas (Exs x)
  x' <- freshNam
  x'' <- freshNam
  ctxPrepend Exst x [((Exst, x''), Nothing), ((Exst, x'), Nothing)]
  ctxInst Exst x $ Fun (Exs x') (Exs x'')
  check e (Exs x')
  pure $ Exs x''
```

**[->App]**

Then there is a case for applying the function type `A -> C` to some expression `e`, yielding `C`. To verify this,
`e` is simply checked against `A`-- easy.

```
    Γ ⊢ e ⇐ A ⊣ ∆
---------------------- [->App]
Γ ⊢ A → C • e ⇒⇒ C ⊣ ∆
```

```Haskell
applyType (Fun a b) e = check e a $> b
```

**[∀App]**

Finally, there's a rule for applying forall-quantified function types to expressions;
it just substitutes out the type variable `a` for `∃a` and tosses aside the quantifier
when recursing. 

```
Γ, ∃a ⊢ [∃a/a]A • e ⇒⇒ C ⊣ ∆
---------------------------- [∀App]
   Γ ⊢ ∀a. A • e ⇒⇒ C ⊣ ∆
```

```Haskell
applyType (For a t) e =
  ctxAppend [((Exst, a), Nothing)] >> applyType (subst a (Exs a) t) e
```

### Synthesis

Now we can write the final judgement we need, the "synthesis" judgement `e ⇒ A`. Because it
yields `A` as an output, rather than being an input, the type reflects this; it should also
pop out as the type signature we want for a type inference engine in a general sense-- in goes
an expression, out comes a type. We'll write a function `infer` later that will unwrap the `Infer` for us.

```Haskell
synth :: Expr -> Infer Type
```

**[1I⇒]**

First, the most obvious rule: `()` synthesizes the type `1`.

```
-------------- [1I⇒]
Γ ⊢ () ⇒ 1 ⊣ Γ
```

```Haskell
synth Unit = pure One
```

**[Var]**

Next, another fairly obvious rule-- if the context says `x : A`, then `x ⇒ A`.
I'm not sure why they opted to write it like `(x : A) ∈ Γ` as though `Γ` were
a set, rather than just writing the whole rule as `Γ[x : A] ⊢ x ⇒ A ⊣ Γ[x : A]`--
judging by the name, maybe they wanted it to be similar to the rule of the same
name from the Damas-Hindley-Milner system.

```
 (x : A) ∈ Γ
------------- [Var]
Γ ⊢ x ⇒ A ⊣ Γ
```

The Haskell code is pretty simple, with the added functionality of throwing
an error if the reference doesn't have any type assigned by the context. I could
probably make use of `maybe` here to avoid the need for a `case`, but eh.

```Haskell
synth (Ref x) = do
  t <- ctxFind Mono x
  case t of
    Just t' -> pure t'
    Nothing -> throwError "Monomorphic type assignment in context without a Just."
```

**[->I⇒]**

Then there's a rule for synthesizing a function type given some
lambda expression `λx. e`. To do this, we give `x` an existential
type variable `∃a` as its type, and also perform a checking judgement
`e ⇐ ∃b`-- then, after we cut out `x : ∃a`, we've verified that
`λx. e ⇒ ∃a -> ∃b`

```
Γ, ∃a, ∃b, x : ∃a ⊢ e ⇐ ∃b ⊣ ∆, x : ∃a, Θ
---------------------------------------- [->I⇒]
      Γ ⊢ λx. e ⇒ ∃a -> ∃b ⊣ ∆
```

```Haskell
synth (Lam x e) = do
  a <- freshNam
  b <- freshNam
  ctxAppend [((Exst, a), Nothing), ((Exst, b), Nothing), ((Mono, x), Just $ Exs a)]
  check e (Exs b)
  ctxCut Mono x
  pure $ Fun (Exs a) (Exs b)
```

**[→E]**

Next we have a rule for synthesizing a type given an application `e e'`.
First, we synthesize a type `A` for the expression `e` with an output context `Θ`,
then under that context we check that `[Θ]A • e' ⇒⇒ C` yields the context `∆` without
error-- if so, then `e e' ⇒ C` with the output context `∆`.

```
Γ ⊢ e ⇒ A ⊣ Θ   Θ ⊢ [Θ]A • e' ⇒⇒ C ⊣ ∆
-------------------------------------- [→E]
          Γ ⊢ e e' ⇒ C ⊣ ∆
```

```Haskell
synth (App a b) = do
  at <- synth a >>= ctxApply
  applyType at b
```

**[Anno]**

Finally, there's the `[Anno]` rule, which deals with type annotations.
We just check that the annotation is well-formed under the input context `Γ`,
then perform the check `e ⇐ A`. If this succeeds, `(e : A)` synthesizes the
type `A`.

```
Γ ⊢ A   Γ ⊢ e ⇐ A ⊣ ∆
--------------------- [Anno]
 Γ ⊢ (e : A) ⇒ A ⊣ ∆
```

```Haskell
synth (OfTy e t) = ctxHas t >> check e t $> t
```

### Inference

Finally, we can define a wrapper function for `synth` that makes our lives a bit easier;
given some input context where you could throw in prelude functions and whatnot, it
takes an expression and returns either an inferred type or an error.

```Haskell
infer :: Ctx -> Expr -> Either T.Text Type
```

The definition is pretty basic-- it equips the state with the context we supplied
and an infinite stream of variable names `vs`.

```Haskell
infer c e =
  let vs = ((flip Name $ 0) . T.pack) <$> ([1..] >>= flip replicateM ['a'..'z'])
  in fst $ (runState . runExceptT $ (ctxApply =<< synth e)) (c, vs)
```

And with that, the system is complete, bar the supplementary "boring" functions that were
skipped over earlier. Hopefully this was somewhat enlightening or helped to explain how
you might go about implementing this yourself.
