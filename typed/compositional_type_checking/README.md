# Compositional Type Checking

## Introduction

Compositional type checking is a unique style of type checking that treats
constraints in a more "bottom-up" rather than "top-down" manner compared to
the traditional methods. Instead of generating placeholder type variables as
the tree is traversed downwards, compositional typings propagate a set of
"constraints" upon the types of an expression upwards, which are then resolved.

The advantage to this approach, at least in a practical scenario, is better
error messages-- it's more natural to think about type errors in terms of the
"uses of a variable" not matching up, rather than there being some type that we
assumed beforehand thanks to some bias, as we would using the usual constraint
generation method. (That being said, my system doesn't do a very good job of
producing nice errors, as that wasn't my top priority-- more on that in the
next section.)

## This System

This system is largely based off of the examples given by
[Abigail Magalhães](https://github.com/plt-abigail) from
[her article on the topic](https://abby.how/posts/2019-01-28.html)
and the [associated repo.](https://github.com/plt-abigail/mld) It's more or
less just a straight translation (with bugfixes, at least as far as I can tell, to how
substitution is done), and you should thank them for doing all of the
work.

The secondary source I'm using, in order to avoid my misconceptions, is
["Compositional Type Checking for Hindley-Milner Type Systems with Ad-hoc Polymorphism"](https://gergo.erdi.hu/projects/tandoori/Tandoori-Compositional-Typeclass.pdf)
by Dr. Gergő Érdi. As the title implies, that paper covers the implementation of
typeclasses as well, but this system opts not to do that. Another worthwhile
thing to look at is [Tandoori](https://github.com/gergoerdi/tandoori), which
is probably the most likely to be correct, being that it was made by the guy
who wrote the research paper. (As a trade-off, it seems to also have the most
boilerplate.)

In contrast to those twos' work, I seek to contribute the following points:

- Keeping the write-up and the source code given 1:1.
- Strike a balance between being proper and having concise code by using MTL transformers.
- Keep as much of the program as possible still in the explanation, bar things like alpha-conversion, as I hope we can all agree that's pretty boring.

But there are also a couple downsides to my approach, which should be noted:

- I don't do any nice error messages, which arguably defeats the point. MLΔ does this better by using a "Span" type-- I'd recommend giving that a look for a more practical implementation.
- Using MTL transformers means that there is an added dependency, whereas MLΔ rolls their own. "A little duplication is better than a little dependency."
- My example is not a full compiler, whereas MLΔ may be compiled to C, has a parser, etc.

To sum up, this system should be used as a compact, simple explanation of the
ideas behind how the system works, rather than as a model implementation for
how you should do things. For that, MLΔ's and Tandoori's source code seems a far
better choice.

### Terms

First, the term grammar. It's just the usual lambda calculus, but extended with
let-polymorphism and the unit constructor `()`.

```
E = v
  | λv. E
  | E E
  | let v = E in E
  | ()
```

This is pretty straightforward to translate to Haskell. The Int attached to Name
is for alpha-conversion purposes, which I won't be going over as its
implementation is not novel.

```Haskell
data Name
  = Name T.Text Int
  deriving (Eq, Ord)

data Expr
  = Ref Name
  | Lam Name Expr
  | App Expr Expr
  | Let Name Expr Expr
  | Unit
```

### Types

The type-level language is similarly simple; there are type variables, function
types, and the unit type `1`.

```
T = a
  | T -> T
  | 1
```

And again, this pretty much directly translates to Haskell.

```Haskell
data Type
  = TVar Name
  | Fun  Type Type
  | One
  deriving (Eq)
```

### Contexts, Typings, and Substitutions

Compositional type checking starts to become interesting once you begin to
consider how contexts are done. There are a couple things to be considered, so
I'll go over each individually.

**Δ-Contexts**

First, Δ-contexts ("delta contexts") map a term variable name to a monomorphic
type. Rather than defining them in terms of some sort of BNF grammar, they're
more aptly represented as an unordered set or mapping. For instance, you could
write a Δ-context that says that `x` has type `Int` as `{x :: Int}`.

The unordered nature of the contexts lends itself nicely to a simple `Map`
type, so that we can efficiently query it.

```Haskell
newtype Delta = Delta (M.Map Name Type)
```

**Typings**

The really interesting part of the system, though, is the concept of "typings".
They allow us to annotate a type with a Δ-context that gives the conditions
required for that type to be valid. For instance, if we queried the type of the
term `x` on its own, we would be given the typing `{x :: a} |- a`. From here
on out, I'll refer to the `|- a` there as the "supported type" of the typing.

```Haskell
data Typing = Typing Delta Type
```

**Γ-Contexts**

Then there are Γ-contexts ("gamma contexts") which map a term variable name to
a polymorphic typing. When we introduce a `let`-bound variable, we store that
in gamma, which gets propagated downwards. When we arrive at a use of that
variable in the sub-expression, the typing in gamma is "instantiated" for that
case-- more on how that works later.

```Haskell
newtype Gamma = Gamma (M.Map Name Typing)
```

**Substitutions**

For the sake of efficiency and simplicity, substitutions will be given their
own data type, as a mapping from type variable names to types. "Efficiency"
because the system involves a lot of multiple-variable substitutions, so using
a map here and doing a single traversal is much nicer.

```Haskell
newtype Subst = Subst (M.Map Name Type)
```

**The "Infer" Monad**

As stated earlier, MTL is used in this system to keep the amount of boilerplate
down at the cost of a dependency. Here I define an `Infer` monad that uses the
`ExceptT` monad transformer to combine the ability to throw errors with a supply
of fresh variables and the ambient substitution via `State`.

```Haskell
type Infer t = ExceptT T.Text (State ([Name], Subst)) t
```

### Substitutions

**The "Substable" Typeclass**

First, we define a typeclass `Substable` that presents two functions-- one to
apply a `Subst` to a `Substable`, hence the name, and another to list the free
type variables in a `Substable`.

```Haskell
class Substable a where
  apply :: Subst -> a -> a
  ftv :: a -> S.Set Name
```

The only interesting part here is that substitutions for type variables recurse,
which seems an odd choice-- isn't that the job of the constraint solving phase?
Well, in our case there is no separate constraint solving phase-- most all of
the unification is done when merging Δ-contexts, which relies on substitutions
to find what a type variable "really resolves to".

```Haskell
instance Substable Type where
  ftv (TVar x) = S.singleton x
  ftv (Fun a b) = ftv a <> ftv b
  ftv One = S.empty
  apply s@(Subst m) v@(TVar x) = fromMaybe v $ apply s <$> M.lookup x m
  apply s (Fun a b) = Fun (apply s a) (apply s b)
  apply _ One = One

instance Substable Delta where
  apply s (Delta m) = Delta $ fmap (apply s) m
  ftv (Delta m) = foldMap ftv m

instance Substable Typing where
  apply s (Typing d t) = Typing (apply s d) (apply s t)
  ftv (Typing d t) = ftv d <> ftv t
```

**Composing Substitutions**

Composing substitutions is something that's incredibly easy to get wrong--
just applying one substitution to another won't keep every key, applying both
substitutions to each other can lead to `[a := b]` with `[b := a]` becoming
`[a := b, b := a]`, and so on.

To do this properly, we use the `Semigroup (Map k v)` definition to keep any
fields from `a` not in `b`, but apply the substitution `a` to `b` for any fields
that are in both. Then, entries like `[a := a]` are removed, and entries like
`[a := a -> b]` are an occurs error-- if we didn't prevent these, it could lead
to mysterious hangs, since `apply` would keep trying to expand `a` ad infinitum.

```Haskell
compose :: Subst -> Subst -> Infer Subst
compose a@(Subst ma) b@(Subst mb) =
  Subst <$> (M.traverseMaybeWithKey try $ ma <> (apply a <$> mb))
    where
      try k x | (TVar k) == x = pure Nothing
      try k x | k `S.member` ftv x = throwError "Attempt to create infinite substitution."
      try k x = pure $ Just x
```

### Omitted "Boring" Functions

- `freshVar :: Infer Type` yields a fresh type variable.
- `extendSub :: Subst -> Infer ()` uses the `compose` function for `Subst` to extend the current substitution.
- `applySub :: Sustable t => t -> Infer t` applies the `Subst` stored in `Infer` to a `Substable`.

### Unification

Now we can get to unification of types for the system, which is responsible for
making sure that type variables are instantiated as needed and don't have
mismatches.

There are two functions presented here, `unify` and `doUnify`--
`unify` is more or less just a wrapper that calls `doUnify` but applies the
ambient substitution to the types being unified, like so:

```Haskell
unify :: Type -> Type -> Infer ()
unify l r = join $ doUnify <$> applySub l <*> applySub r
```

The actual heavy lifting is done by `doUnify`, which has the following type
signature:

```Haskell
doUnify :: Type -> Type -> Infer ()
```

The rules for it are detailed below.

**a ~ A**

First, there's the case for unifiying a type variable with an arbitrary type. If
a type variable is unified with itself, it will succeed, but otherwise,
unifiying a type variable with a type that has that type variable free in it is
set to fail, as that would lead to an infinite type-- that is, something like
`a ~ (a -> 1)` will fail.

```Haskell
doUnify (TVar x) t =
  if (x `S.member` ftv t) && (t /= TVar x) then
    throwError $ "Failed to unify " <> tshow (TVar x) <> " with " <> tshow t
  else
    extendSub $ Subst (M.singleton x t)
```

**A ~ a**

The rules for `a ~ A` and `A ~ a` are the same in our case, so we just recurse.

I've seen some people write unification as always having the type variable on
the left and outlawing things like `1 ~ a` as you can't make a substitution
`1 := a`, but I think that's a fairly pointless distinction-- they usually
end up writing the same thing during the constraint solving phase, which we
don't have, so we can just do that here.

```Haskell
doUnify t (TVar x) = doUnify (TVar x) t
```

**A -> B ~ A' -> B'**

Unification for function types simply unifies the domains, then applies the
ambient substitution to the codomains and unifies those substituted types--
recall that `unify` applies the substitution, whereas `doUnify` does not.

```Haskell
doUnify (Fun a b) (Fun a' b') = doUnify a a' >> unify b b'
```

**1 ~ 1**

`1` unifies with `1` with no errors, of course.

```Haskell
doUnify One One = pure ()
```

**A ~ B**

If none of the earlier cases worked, then unification fails.

```Haskell
doUnify a b = throwError $ "Failed to unify " <> tshow a <> " with " <> tshow b
```

### Delta Merging

Now that we have unification done, we need a way to "unify delta-contexts", in
a sense-- that is, merge them into one, where the types from both "agree" on
the resulting type. This has the following type signature:

```Haskell
mergeDelta :: Delta -> Delta -> Infer Delta
```

Instead of doing some complicated logic to find matches, we'll just use
`Data.Map.Merge.Strict`'s function `mergeA` which allows us to specify behaviour
for when one key is missing in either map, as well as the case when there is a
match and both maps have the key.

```Haskell
mergeDelta (Delta am) (Delta bm) = Delta <$> M.mergeA keep keep try am bm
```

Of course, we need to actually define what `keep` and `try` are. `keep` will
just keep the key as-is, whereas `try` will try to unify the two types, then
keep the latter of the two, with the ambient substitution applied.

```Haskell
  where
    keep = M.preserveMissing
    try = M.zipWithAMatched $ \_ a b -> unify a b >> applySub b
```

### Instantiation

As mentioned earlier, Δ-contexts are for monomorphic types, and this applies to
the Δ-contexts in typings as well. However, if a type occurs only in the
supported type of a typing and not in its Δ-context, it is *unconstrained*,
which means it could be unified with any type successfully.

As for how we actually get `let`-polymorpsim, that is all thanks to Γ-contexts;
they map `let`-bound variables to their typings. When we encounter the use of
one of these `let`-bound variables, we perform *instantiation* by replacing all
of the unconstrained type variables in the typing we got from the Γ-context
with fresh variables, and using that as the resulting typing. This way, we don't
need any "rigid" type variables that cannot be unified-- we just create new ones
that may be unified freely.

However, this raises the question-- if this is for polymorphism, why carry
around a Δ-context at all? Why not just have Γ-contexts be a map from type
variable names to types directly? Well, because there may be a use of a
monomorphic type variable inside of a `let`-polymorphic binding. Consider for
instance the following program, taken from Gergő Érdi’s paper:

```
toUpper :: Char -> Char
not :: Int -> Int
map :: (a -> b) -> [a] -> [b]

λxs. let xform f = map f xs in (xform toUpper, xform not)
```

This code produces the typing `{xs :: [a]} |- (a -> b) -> [b]` for `xform`,
because how we instantiate `f` for `xform` actually impacts what type `xs` must
have! The above code *will not* type check, because the left usage generates
the typing `{xs :: [Char]} |- (Char -> Char) -> [Char]`, whereas the right-hand
usage `{xs :: [Int]} |- (Int -> Int) -> [Int]`. When we go to unify the
Δ-contexts of these two typings, we'll get the error that the types `[Int]`
and `[Char]` for `xs` couldn't be unified, as expected. Were we to not carry
around this information about a monomorphic type variable in gamma, we would
not have caught this error, and this program would be admitted by the
typechecker-- not a desirable result.

Now that you hopefully have a decent understanding of how typings and the
implicit distinction between monomorphic and polymorphic type variables in the
system works, you should also understand that we need that aforementioned
instantiation function-- here we'll call it `refresh`, and it will use the
fresh variable supply from the `Infer` monad to do the renaming we need.

```Haskell
refresh :: Typing -> Infer Typing
```

The code itself is also very simple-- we fetch the set of variables `vs` and
ambient substitution `s`, find the list of type variables `tau_fv` that are
free in the supported type `tau` but not the Δ-context `delta`, take as many
type variables from the supply as there are variables in `tau_fv`, then remap
the old type variable names to the new ones by creating a temporary
substitution `s''` that we apply to our typing.

```Haskell
refresh (Typing delta tau) = do
  (vs, s) <- get
  let tau_fv = S.toList (ftv tau `S.difference` ftv delta)
  let (used, vs') = splitAt (length tau_fv) vs
  let s' = Subst $ M.fromList (zip tau_fv (map TVar used))
  s'' <- compose s s'
  put (vs', s)
  pure . apply s'' $ Typing delta tau
```

### Reduction

Reduction is another simple operation that we need in order to implement
`let`-polymorphism. It serves two purposes: first, it removes all types from
the typing that don't have type variables that intersect with the supported
type, then it removes the entry for the specified term variable from the
Δ-context.

The reason for this is fairly simple-- in our earlier example, the only reason
`xform` had any impact on the type of `xs` was because it shared a type variable
with it, namely `a`. If no such connection exists, then keeping that entry in
the Δ-context only serves to make the typing "less polymorphic" and admit
fewer perfectly valid programs.

As for why we want to remove a specified term variable-- that is for the
`let`-bound variable name, because we don't want that to be unified. The type
of the `let`-bound variable is not handled by `refresh` since it may occur in
the Δ-context thanks to recursive `let` bindings. If we didn't remove it, then
its type would be monomorphic because it is in the Δ-context-- which obviously
isn't what we want.

```Haskell
reduce :: Name -> Typing -> Typing
reduce v (Typing (Delta dm) tau) = do
  let tau_fv = ftv tau
  let keep sigma = not . S.null $ ftv sigma `S.intersection` tau_fv
  let dm' = M.filter keep (M.delete v dm)
  Typing (Delta dm') tau
```

### Inference

The type signature for inference is pretty much what you'd expect; we need the
Γ-context to propagate our polymorphic typings downwards, and we want to
infer a typing from an expression.

```Haskell
infer :: Gamma -> Expr -> Infer Typing
```

The rules for inference are given below.

**[Var]**

First, there's the case for term variables. If the term variable is `let`-bound,
we take the typing from that and refresh it. Otherwise, we generate a fresh
variable and use that as the constraint upon the term variable's type.

```Haskell
infer (Gamma gm) (Ref x) =
  case M.lookup x gm of
    Just xt ->
      refresh xt
    Nothing -> do
      alpha <- freshVar
      pure $ Typing (Delta $ M.singleton x alpha) alpha
```

**[Abs]**

Next, we have lambda-abstractions. First, we infer a type `sigma` and Δ-context
`delta` for the expression. If the bound variable is already given a typing by
`delta`, we use that definition with the bound variable removed from `delta`,
and the supported type is `tau -> sigma` where `tau` was the type for the
bound variable we got by querying `delta`. Otherwise, we generate a fresh type
`alpha`, use `delta` as our resulting Δ-context, and `alpha -> sigma` is the
supported type.

```Haskell
infer g (Lam x e) = do
  Typing delta@(Delta dm) sigma <- infer g e
  case M.lookup x dm of
    Just tau ->
      pure $ Typing (Delta $ M.delete x dm) (Fun tau sigma)
    Nothing -> do
      alpha <- freshVar
      pure $ Typing delta (Fun alpha sigma)
```

**[App]**

The rule for applications is a little bit more interesting. First, both branches
of the application are recursed upon, and we get the Δ-context and supported
type for each. Then, we make a fresh type variable `alpha` and perform the
unification `at ~ (bt -> alpha)`. This way, `alpha` is the resulting type of
the function-- we only need to make sure that `ad` and `bd` are compatible by
merging them, then applying the substitution to `alpha` to get the final result.

```Haskell
infer g (App a b) = do
  Typing ad at <- infer g a
  Typing bd bt <- infer g b
  alpha <- freshVar
  unify at (Fun bt alpha)
  abd <- mergeDelta ad bd
  applySub $ Typing abd alpha
```

**[Let]**

`let`-bindings are very easy-- given `let x = a in b`, first we find the typing
of `a`, then reduce it with respect to `x`. After that's done, we find the
typing for `b` and use that reduced typing from earlier as a new entry in the
Γ-context, with `x` as the key. Afterwards, the Δ-contexts of both branches
are merged, and the type for `b` with the merged Δ-contex is the result.

```Haskell
infer g@(Gamma gm) (Let x a b) = do
  at@(Typing ad _) <- reduce x <$> infer g a
  Typing bd tau <- infer (Gamma $ M.insert x at gm) b
  abd <- mergeDelta ad bd
  pure $ Typing abd tau
```

**[Unit]**

Aaaaand finally the most trivial case.

```Haskell
infer _ Unit = pure $ Typing (Delta M.empty) One
```

### Running Inference

Although in a practical scenario you'd want to delay this as much as possible
so that the substitution and fresh name supply would be kept intact, here a
function `runInfer` is defined to give a basic idea of how to actually run
`infer`, with an infinite supply of variable names.

```Haskell
runInfer :: Gamma -> Expr -> Either T.Text Typing
runInfer g e =
  let vs = ((`Name` 0) . T.pack) <$> ([1..] >>= flip replicateM ['a'..'z'])
   in fst $ (runState . runExceptT $ (infer g e)) (vs, Subst M.empty)
```

Thus concludes the implementation of the system, and hopefully I've managed to
present one that actually works and is somewhat concise.
