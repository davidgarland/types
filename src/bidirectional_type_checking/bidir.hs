{-
  An example implementation of bidirectional type checking, as described in the
  paper "Complete and Easy Bidirectional Typecheckingfor Higher-Rank
  Polymorphism" by Dunfield and Krishnaswami.
-}

{-# LANGUAGE OverloadedStrings #-}

import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.List as L
import Control.Monad.State
import Control.Monad.Except
import Data.Functor

-- Core

data Name
  = Name T.Text Int
  deriving (Eq, Ord)

data Exp         -- e ::=
  = Unit         -- | ()
  | Ref Name     -- | x
  | Lam Name Exp -- | λx. e
  | App Exp  Exp -- | e e
  | OfT Exp  Typ -- | (e : A)

data Typ         -- T ::=
  = One          -- | 1
  | Var Name     -- | a
  | Exs Name     -- | ∃a
  | For Name Typ -- | ∀a. T
  | Fun Typ  Typ -- | T -> T

data CtxK
  = Mono -- Just Typ
  | Poly -- Nothing
  | Exst -- Maybe Typ
  | Mark -- Nothing
  deriving (Eq, Show)
type CtxE = ((CtxK, Name), Maybe Typ)
type Ctx = [CtxE]

type Infer t = ExceptT T.Text (State (Ctx, [Name])) t

-- Show Instances

instance Show Name where
  show (Name n v) = T.unpack n

instance Show Exp where
  show Unit = "()"
  show (Ref n) = show n
  show (Lam n e) = "λ" ++ show n ++ ". " ++ show e
  show (App a b) = show a ++ " " ++ show b
  show (OfT e t) = "(" ++ show e ++ " : " ++ show t ++ ")"

instance Show Typ where
  show One = "()"
  show (Var n) = show n
  show (Exs n) = "∃" ++ show n
  show (For n t) = "∀" ++ show n ++ ". " ++ show t
  show (Fun a b) = show a ++ " -> " ++ show b

tshow :: Show a => a -> T.Text
tshow = T.pack . show

-- Alpha-Renaming

type Rnm = M.Map T.Text Int

incNam :: Name -> Rnm -> Rnm
incNam n@(Name t _) r = let Name _ v' = getNam r n in M.insert t (v' + 1) r

getNam :: Rnm -> Name -> Name
getNam r (Name t _) = Name t $ M.findWithDefault 0 t r

rename :: Rnm -> Exp -> Exp
rename r Unit = Unit
rename r (Ref x) = Ref $ getNam r x
rename r (Lam x e) =
  let r' = incNam x r in
  Lam (getNam r' x) (rename r' e)
rename r (App a b) = App (rename r a) (rename r b)
rename r (OfT e t) = OfT (rename r e) t

-- Helper Functions

ftv :: Typ -> S.Set Name
ftv One = S.empty
ftv (Var x) = S.singleton x
ftv (Exs x) = S.singleton x
ftv (For x t) = x `S.delete` ftv t
ftv (Fun a b) = ftv a <> ftv b

subst :: Name -> Typ -> Typ -> Typ
subst n w One = One
subst n w (Var x) = if n == x then w else Var x
subst n w (Exs x) = Exs x
subst n w (For x t) = For x (subst n w t)
subst n w (Fun a b) = Fun (subst n w a) (subst n w b)

freshNam :: Infer Name
freshNam = do
  (ctx, vs) <- get
  case vs of
    x : xs -> do
      put (ctx, xs)
      pure x
    _ -> throwError "Failed to generate a fresh name. Is the supply empty?"

errIf :: Bool -> T.Text -> Infer ()
errIf c e = if c then throwError e else return ()

-- Context Cut / Instantiation

cut :: Eq a => a -> e -> [(a, b)] -> Either e [(a, b)]
cut k e ((x, _) : xs)
  | k == x    = Right xs
  | otherwise = cut k e xs
cut k e [] = Left e

inst :: Eq a => a -> b -> e -> [(a, b)] -> Either e [(a, b)]
inst k v e ((x, y) : xys)
  | k == x    = Right $ (k, v) : xys
  | otherwise = ((x, y) :) <$> inst k v e xys
inst k v e [] = Left e

ctxDo :: (Ctx -> Either T.Text Ctx) -> Infer ()
ctxDo f = do
  (c, v) <- get
  case f c of
    Right c' -> put (c', v)
    Left e -> throwError e

ctxCut :: CtxK -> Name -> Infer ()
ctxCut k n = do
  (c, _) <- get
  ctxDo . cut (k, n) $ "Failed to cut variable `" <> tshow k <> " "<> tshow n <> "` from `" <> tshow c <> "`."

ctxInst :: CtxK -> Name -> Typ -> Infer ()
ctxInst k n t = ctxDo . inst (k, n) (Just t) $ "Failed to instantiate variable `" <> tshow k <> " " <> tshow n <> "`."

-- Context Querying

ctxFind :: CtxK -> Name -> Infer (Maybe Typ)
ctxFind k n = do
  (c, _) <- get
  maybe (throwError $ "Failed to find variable `" <> tshow k <> " " <> tshow n <> "`.") return $ L.lookup (k, n) c

ctxHas :: Typ -> Infer ()
ctxHas One = pure ()
ctxHas (Var x) = ctxFind Poly x $> ()
ctxHas (Exs x) = ctxFind Exst x $> ()
ctxHas (For x t) = do
  ctxAppend [((Poly, x), Nothing)]
  ctxHas t
  ctxCut Poly x
ctxHas (Fun a b) = ctxHas a >> ctxHas b

-- Context Adding

ctxAppend :: Ctx -> Infer ()
ctxAppend c' = modify (\(c, vs) -> (c' ++ c, vs))

ctxPrepend :: CtxK -> Name -> Ctx -> Infer ()
ctxPrepend k n c' = do
  (c, vs) <- get
  case L.break (\((ck, cn), cm) -> (ck, cn) == (k, n)) c of
    (a, b@(_ : _)) -> put (a ++ c' ++ b, vs)
    _ -> throwError $ "Failed to find variable `" <> tshow k <> " " <> tshow n <> "` in context for prepend."

-- Context Application

ctxApply :: Typ -> Infer Typ
ctxApply One = pure One
ctxApply (Var x) = pure $ Var x
ctxApply (Exs x) = ctxFind Exst x >>= maybe (pure $ Exs x) ctxApply
ctxApply (For x t) = For x <$> ctxApply t
ctxApply (Fun a b) = Fun <$> ctxApply a <*> ctxApply b

-- Main Judgements

subtyp :: Typ -> Typ -> Infer ()
subtyp One One = pure ()
subtyp (Var a) (Var a')
  | a == a' = ctxFind Poly a $> ()
  | otherwise =
    throwError $ "Failed to unify `" <> tshow a <> "` with `" <> tshow a' <> "`."
subtyp (Exs a) (Exs a')
  | a == a' = ctxFind Exst a $> ()
  | otherwise = do
    ctxHas (Exs a)
    ctxHas (Exs a')
    instLeft (Exs a) (Exs a')
subtyp (Fun a a') (Fun b b') = do
  subtyp b a
  a'' <- ctxApply a'
  b'' <- ctxApply b'
  subtyp a'' b''
subtyp (For x a) b = do
  x' <- freshNam
  ctxAppend [((Exst, x'), Nothing), ((Mark, x'), Nothing)]
  subtyp (subst x (Exs x') a) b
  ctxCut Mark x'
subtyp a (For x b) = do
  ctxAppend [((Poly, x), Nothing)]
  subtyp a b
  ctxCut Poly x
subtyp (Exs x) b = do
  ctxHas (Exs x)
  errIf (x `S.member` ftv b) $ "Failed to unify `" <> tshow x <> "` with `" <> tshow b <> "`."
  instLeft (Exs x) b
subtyp a (Exs x) = do
  ctxHas (Exs x)
  errIf (x `S.member` ftv a) $ "Failed to unify `" <> tshow x <> "` with `" <> tshow a <> "`."
  instRight a (Exs x)

instLeft :: Typ -> Typ -> Infer ()
instLeft (Exs x) (Exs y) = ctxInst Exst y (Exs x)
instLeft (Exs x) (Fun a b) = do
  x' <- freshNam
  x'' <- freshNam
  ctxPrepend Exst x [((Exst, x''), Nothing), ((Exst, x'), Nothing)]
  ctxInst Exst x (Fun (Exs x') (Exs x''))
  instRight a (Exs x')
  b' <- ctxApply b
  instLeft (Exs x'') b'
instLeft (Exs x) (For a t) = do
  _ <- ctxFind Exst x
  ctxAppend [((Poly, a), Nothing)]
  instLeft (Exs x) t 
  ctxCut Poly a
instLeft (Exs x) y = ctxInst Exst x y
instLeft x _ = throwError "Inexhaustive pattern in instLeft."

instRight :: Typ -> Typ -> Infer ()
instRight (Exs x) (Exs y) = ctxInst Exst x (Exs y)
instRight (Fun a b) (Exs y) = do
  y' <- freshNam
  y'' <- freshNam
  ctxPrepend Exst y [((Exst, y''), Nothing), ((Exst, y'), Nothing)]
  ctxInst Exst y (Fun (Exs y') (Exs y''))
  instLeft (Exs y') a
  b' <- ctxApply b
  instRight b' (Exs y'')
instRight (For a t) (Exs y) = do
  ctxHas (Var a)
  a' <- freshNam
  ctxAppend [((Mark, a'), Nothing), ((Exst, a'), Nothing)]
  instRight (subst y (Exs a') t) (Exs y) 
  ctxCut Mark a'
instRight t (Exs y) = do
  (c, vs) <- get
  ctxCut Exst y
  ctxHas t
  put (c, vs)
  ctxInst Exst y t
instRight _ _ = throwError "Inexhaustive pattern in instRight."

check :: Exp -> Typ -> Infer ()
check Unit One = return ()
check (Lam x e) (Fun a b) = do
  ctxAppend [((Mono, x), Just a)]
  check e b
  ctxCut Mono x
check e (For a t) = do
  ctxAppend [((Poly, a), Nothing)]
  check e t
  ctxCut Poly a
check e t = do
  et <- synth e
  et' <- ctxApply et
  t' <- ctxApply t
  subtyp et' t'

applyTyp :: Typ -> Exp -> Infer Typ
applyTyp (Exs x) e = do
  ctxHas (Exs x)
  x' <- freshNam
  x'' <- freshNam
  ctxPrepend Exst x [((Exst, x''), Nothing), ((Exst, x'), Nothing)]
  ctxInst Exst x $ Fun (Exs x') (Exs x'')
  check e (Exs x')
  pure $ Exs x''
applyTyp (Fun a b) e = do
  check e a
  return b
applyTyp (For a t) e = do
  a' <- freshNam
  ctxAppend [((Exst, a'), Nothing)]
  applyTyp (subst a (Exs a') t) e

synth :: Exp -> Infer Typ
synth Unit = pure One
synth (Ref x) = do
  t <- ctxFind Mono x
  case t of
    Just t' -> pure t'
    Nothing -> throwError "Monomorphic type assignment in context without a Just."
synth (Lam x e) = do
  a <- freshNam
  b <- freshNam
  ctxAppend [((Exst, a), Nothing), ((Exst, b), Nothing), ((Mono, x), Just $ Exs a)]
  check e (Exs b)
  ctxCut Mono x
  pure $ Fun (Exs a) (Exs b)
synth (App a b) = do
  at <- synth a
  at' <- ctxApply at
  applyTyp at' b
synth (OfT e t) = do
  ctxHas t
  check e t
  pure t

infer :: Ctx -> Exp -> (Either T.Text Typ, (Ctx, [Name]))
infer c e =
  let vs = ((flip Name $ 0) . T.pack) <$> ([1..] >>= flip replicateM ['a'..'z'])
  in (runState . runExceptT $ synth e) (c, vs)

-- Examples

name :: T.Text -> Name
name x = Name x 0

var :: T.Text -> Typ
var = Var . name

ref :: T.Text -> Exp
ref = Ref . name

lam :: T.Text -> Exp -> Exp
lam n e = Lam (name n) e

eid :: Exp
eid = lam "x" $ ref "x"

test :: String -> Exp -> IO ()
test n e = do
  putStrLn $ " -- " ++ n ++ " --"
  putStrLn $ "Input:    " ++ show e
  let infrd = infer [] $ rename M.empty e
  case infrd of
    (Right t, (c, _))  -> putStrLn $ "Inferred: " ++ show t ++ "\nGamma:    " ++ show c
    (Left err, (c, _)) -> putStrLn $ T.unpack err ++ "\nGamma: " ++ show c

main = do
  test "id" eid
  test "poly id" (OfT eid (For (name "'t") (Fun (var "'t") (var "'t"))))
