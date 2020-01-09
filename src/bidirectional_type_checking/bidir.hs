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

data Nam
  = Nam T.Text Int
  deriving (Eq, Ord)

data Exp        -- e ::=
  = Unt         -- | ()
  | Ref Nam     -- | x
  | Lam Nam Exp -- | λx. e
  | App Exp Exp -- | e e
  | OfT Exp Typ -- | (e : A)

data Typ        -- T ::=
  = One         -- | 1
  | Var Nam     -- | a
  | Exs Nam     -- | ∃a
  | For Nam Typ -- | ∀a. T
  | Fun Typ Typ -- | T -> T

data CtxK
  = Mono -- Just Typ
  | Poly -- Nothing
  | Exst -- Maybe Typ
  | Mark -- Nothing
  deriving (Eq, Show)
type CtxE = ((CtxK, Nam), Maybe Typ)
type Ctx = [CtxE]

type Infer t = ExceptT T.Text (State (Ctx, [Nam])) t

-- Show Instances

instance Show Nam where
  show (Nam n v) = T.unpack n

instance Show Exp where
  show Unt = "()"
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

incNam :: Nam -> Rnm -> Rnm
incNam n@(Nam t _) r = let Nam _ v' = getNam r n in M.insert t (v' + 1) r

getNam :: Rnm -> Nam -> Nam
getNam r (Nam t _) = Nam t $ M.findWithDefault 0 t r

rename :: Rnm -> Exp -> Exp
rename r Unt = Unt
rename r (Ref x) = Ref $ getNam r x
rename r (Lam x e) =
  let r' = incNam x r in
  Lam (getNam r' x) (rename r' e)
rename r (App a b) = App (rename r a) (rename r b)
rename r (OfT e t) = OfT (rename r e) t

-- Monadic Functions

class Substs s where
  fvs :: s -> S.Set Nam
  subst :: Nam -> s -> s -> s

instance Substs Exp where
  fvs Unt = S.empty
  fvs (Ref x) = S.singleton x
  fvs (Lam x e) = x `S.delete` fvs e
  fvs (App a b) = fvs a <> fvs b
  fvs (OfT x t) = fvs x
  subst n w Unt = Unt
  subst n w (Ref x) = if n == x then w else Ref x
  subst n w (Lam x e) = Lam x (subst n w e)
  subst n w (App a b) = App (subst n w a) (subst n w b)
  subst n w (OfT x t) = OfT (subst n w x) t

instance Substs Typ where
  fvs One = S.empty
  fvs (Var x) = S.singleton x
  fvs (Exs x) = S.singleton x
  fvs (For x t) = x `S.delete` fvs t
  fvs (Fun a b) = fvs a <> fvs b
  subst n w One = One
  subst n w (Var x) = if n == x then w else Var x
  subst n w (Exs x) = Exs x
  subst n w (For x t) = For x (subst n w t)
  subst n w (Fun a b) = Fun (subst n w a) (subst n w b)

freshNam :: Infer Nam
freshNam = do
  (ctx, vs) <- get
  case vs of
    x : xs -> do
      put (ctx, xs)
      pure x
    _ -> throwError "Failed to generate a fresh name. Is the supply empty?"

errIf :: Bool -> T.Text -> Infer ()
errIf c e = if c then throwError e else return ()

-- List Functions

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

-- Context Searching

ctxFind :: CtxK -> Nam -> Infer (Maybe Typ)
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

ctxPrepend :: CtxK -> Nam -> Ctx -> Infer ()
ctxPrepend k n c' = do
  (c, vs) <- get
  case L.break (\((ck, cn), cm) -> (ck, cn) == (k, n)) c of
    (a, b@(_ : _)) -> put (a ++ c' ++ b, vs)
    _ -> throwError $ "Failed to find variable `" <> tshow k <> " " <> tshow n <> "` in context for prepend."

-- Context Cutting / Instantiation

ctxDo :: (Ctx -> Either T.Text Ctx) -> Infer ()
ctxDo f = do
  (c, v) <- get
  case f c of
    Right c' -> put (c', v)
    Left e -> throwError e

ctxCut :: CtxK -> Nam -> Infer ()
ctxCut k n = do
  (c, _) <- get
  ctxDo . cut (k, n) $ "Failed to cut variable `" <> tshow k <> " "<> tshow n <> "` from `" <> tshow c <> "`."

ctxInst :: CtxK -> Nam -> Typ -> Infer ()
ctxInst k n t = ctxDo . inst (k, n) (Just t) $ "Failed to instantiate variable `" <> tshow k <> " " <> tshow n <> "`."

-- Context Application

ctxApply :: Typ -> Infer Typ
ctxApply One = pure One
ctxApply (Var x) = pure $ Var x
ctxApply (Exs x) = ctxFind Exst x >>= maybe (pure $ Exs x) ctxApply
ctxApply (For x t) = For x <$> ctxApply t
ctxApply (Fun a b) = Fun <$> ctxApply a <*> ctxApply b

-- a <= b

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
    instl (Exs a) (Exs a') -- instl? instr?
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
  errIf (x `S.member` fvs b) $ "Failed to unify `" <> tshow x <> "` with `" <> tshow b <> "`."
  instl (Exs x) b
subtyp a (Exs x) = do
  ctxHas (Exs x)
  errIf (x `S.member` fvs a) $ "Failed to unify `" <> tshow x <> "` with `" <> tshow a <> "`."
  instr a (Exs x)

-- a :=< b

instl :: Typ -> Typ -> Infer ()
instl (Exs x) (Exs y) = ctxInst Exst y (Exs x)
instl (Exs x) (Fun a b) = do
  x' <- freshNam
  x'' <- freshNam
  ctxPrepend Exst x [((Exst, x''), Nothing), ((Exst, x'), Nothing)]
  ctxInst Exst x (Fun (Exs x') (Exs x''))
  instr a (Exs x')
  b' <- ctxApply b
  instl (Exs x'') b'
instl (Exs x) (For a t) = do
  _ <- ctxFind Exst x
  ctxAppend [((Poly, a), Nothing)]
  instl (Exs x) t 
  ctxCut Poly a
instl (Exs x) y = ctxInst Exst x y
instl x _ = throwError "Inexhaustive pattern in instl."

-- a =:< b

instr :: Typ -> Typ -> Infer ()
instr (Exs x) (Exs y) = ctxInst Exst x (Exs y)
instr (Fun a b) (Exs y) = do
  y' <- freshNam
  y'' <- freshNam
  ctxPrepend Exst y [((Exst, y''), Nothing), ((Exst, y'), Nothing)]
  ctxInst Exst y (Fun (Exs y') (Exs y''))
  instl (Exs y') a
  b' <- ctxApply b
  instr b' (Exs y'')
instr (For a t) (Exs y) = do
  ctxHas (Var a)
  a' <- freshNam
  ctxAppend [((Mark, a'), Nothing), ((Exst, a'), Nothing)]
  instr (subst y (Exs a') t) (Exs y) 
  ctxCut Mark a'
instr t (Exs y) = do
  (c, vs) <- get
  ctxCut Exst y
  ctxHas t
  put (c, vs)
  ctxInst Exst y t
instr _ _ = throwError "Inexhaustive pattern in instr."

-- Type Checking

check :: Exp -> Typ -> Infer ()
check Unt One = return ()
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

-- Type Application

app :: Typ -> Exp -> Infer Typ
app (Exs x) e = do
  ctxHas (Exs x)
  x' <- freshNam
  x'' <- freshNam
  ctxPrepend Exst x [((Exst, x''), Nothing), ((Exst, x'), Nothing)]
  ctxInst Exst x $ Fun (Exs x') (Exs x'')
  check e (Exs x')
  pure $ Exs x''
app (Fun a b) e = do
  check e a
  return b
app (For a t) e = do
  a' <- freshNam
  ctxAppend [((Exst, a'), Nothing)]
  app (subst a (Exs a') t) e

-- Type Synthesis

synth :: Exp -> Infer Typ
synth Unt = pure One
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
  app at' b
synth (OfT e t) = do
  ctxHas t
  check e t
  pure t

-- Type Inference

infer :: Ctx -> Exp -> (Either T.Text Typ, (Ctx, [Nam]))
infer c e =
  let vs = ((flip Nam $ 0) . T.pack) <$> ([1..] >>= flip replicateM ['a'..'z'])
  in (runState . runExceptT $ synth e) (c, vs)

-- Examples

nam :: T.Text -> Nam
nam x = Nam x 0

var :: T.Text -> Typ
var = Var . nam

ref :: T.Text -> Exp
ref = Ref . nam

lam :: T.Text -> Exp -> Exp
lam n e = Lam (nam n) e

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
  test "poly id" (OfT eid (For (nam "'t") (Fun (var "'t") (var "'t"))))
