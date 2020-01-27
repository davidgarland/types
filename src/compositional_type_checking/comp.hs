{-
  An example implementation of compositional type elaboration, inference, and   
  checking.
  
  The code here is largely adapted from the following article:
    https://abby.amulet.works/posts/2019-01-28.html
  See also their full implementation, MLΔ:
    https://github.com/plt-abigail/mld
-}

{-# LANGUAGE OverloadedStrings #-}

import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.Map.Merge.Strict as M
import qualified Data.Set as S
import Control.Monad.Except
import Control.Monad.State
import Data.Maybe

-- Core

data Name
  = Name T.Text Int
  deriving (Eq, Ord)

data Expr
  = Ref Name
  | Lam Name Expr
  | App Expr Expr
  | Let Name Expr Expr
  | Unit

data Type
  = TVar Name
  | Fun  Type Type
  | One
  deriving (Eq)

newtype Delta   = Delta (M.Map Name Type)
newtype Subst   = Subst (M.Map Name Type)
data    Typing  = Typing Delta Type
newtype Gamma   = Gamma (M.Map Name Typing)
type    Infer t = ExceptT T.Text (State ([Name], Subst)) t

-- Show Instances

instance Show Name where
  show (Name t _) = T.unpack t

instance Show Expr where
  show (Ref x) = show x
  show (Lam x e) = "λ" ++ show x ++ ". " ++ show e
  show (App a (App b c)) = show a ++ " (" ++ show (App b c) ++ ")"
  show (App a b) = show a ++ " " ++ show b
  show (Let x a b) = "let " ++ show x ++ " = " ++ show a ++ " in " ++ show b
  show Unit = "()"

instance Show Type where
  show (TVar x) = show x
  show (Fun (Fun a b) c) = "(" ++ show (Fun a b) ++ ") -> " ++ show c
  show (Fun a b) = show a ++ " -> " ++ show b
  show One = "1"

instance Show Delta where
  show (Delta dm) = "{" ++ (showNamMap $ M.toList dm) ++ "}"

instance Show Subst where
  show (Subst sm) = "{" ++ (showNamMap $ M.toList sm) ++ "}"

instance Show Typing where
  show (Typing delta tau) = show delta ++ " |- " ++ show tau

showNamMap :: [(Name, Type)] -> String
showNamMap [] = ""
showNamMap ((k, v) : []) = show k ++ " : " ++ show v
showNamMap ((k, v) : kvs) = show k ++ " : " ++ show v ++ ", " ++ showNamMap kvs

tshow :: Show a => a -> T.Text
tshow = T.pack . show

-- Alpha-Renaming

type Rnm = M.Map T.Text Int

incNam :: Name -> Rnm -> Rnm
incNam n@(Name t _) r = let Name _ v' = getNam r n in M.insert t (v' + 1) r

getNam :: Rnm -> Name -> Name
getNam r (Name t _) = Name t $ M.findWithDefault 0 t r

rename :: Rnm -> Expr -> Expr
rename r (Ref x) = Ref $ getNam r x
rename r (Lam x e) =
  let r' = incNam x r in
  Lam (getNam r' x) (rename r' e)
rename r (App a b) = App (rename r a) (rename r b)
rename r (Let x a b) =
  let r' = incNam x r in
  Let (getNam r' x) (rename r' a) (rename r' b)
rename _ Unit = Unit

-- Typeclasses

class Substable a where
  apply :: Subst -> a -> a
  ftv :: a -> S.Set Name

instance Substable Type where
  ftv (TVar x) = S.singleton x
  ftv (Fun a b) = ftv a <> ftv b
  ftv One = S.empty
  apply s@(Subst m) v@(TVar x) = fromMaybe v $ apply s <$> M.lookup x m
  apply s (Fun a b) = Fun (apply s a) (apply s b)
  apply _ One = One

instance Substable Subst where
  apply s (Subst a) = Subst $ apply s <$> a
  ftv (Subst a) = foldMap ftv a

instance Substable Delta where
  apply s (Delta m) = Delta $ fmap (apply s) m
  ftv (Delta m) = foldMap ftv m

instance Substable Typing where
  apply s (Typing d t) = Typing (apply s d) (apply s t)
  ftv (Typing d t) = ftv d <> ftv t

compose :: Subst -> Subst -> Infer Subst
compose a@(Subst ma) b@(Subst mb) =
  Subst <$> (M.traverseMaybeWithKey try $ ma <> (apply a <$> mb))
    where
      try k x | (TVar k) == x = pure Nothing
      try k x | k `S.member` ftv x = throwError "Attempt to create infinite substitution."
      try k x = pure $ Just x

-- Monadic Functions

freshVar :: Infer Type
freshVar = do
  (vars, s) <- get
  case vars of
    x : xs -> do
      put (xs, s)
      pure $ TVar x
    _ -> throwError "Failed to generate a fresh variable. Is the supply empty?"

refresh :: Typing -> Infer Typing
refresh (Typing delta tau) = do
  (vs, s) <- get
  let tau_fv = S.toList (ftv tau `S.difference` ftv delta)
  let (used, vs') = splitAt (length tau_fv) vs
  let s' = Subst $ M.fromList (zip tau_fv (map TVar used))
  s'' <- compose s s'
  put (vs', s)
  pure . apply s'' $ Typing delta tau

reduce :: Name -> Typing -> Typing
reduce v (Typing (Delta dm) tau) = do
  let tau_fv = ftv tau
  let keep sigma = not . S.null $ ftv sigma `S.intersection` tau_fv
  let dm' = M.filter keep (M.delete v dm)
  Typing (Delta dm') tau

extendSub :: Subst -> Infer ()
extendSub s' = do
  (vs, s) <- get
  s'' <- compose s s'
  put (vs, s'')

mergeDelta :: Delta -> Delta -> Infer Delta
mergeDelta (Delta am) (Delta bm) = Delta <$> M.mergeA keep keep try am bm
  where
    keep = M.preserveMissing
    try = M.zipWithAMatched $ \_ a b -> unify a b >> applySub b

applySub :: Substable t => t -> Infer t
applySub tau = do
  (_, s) <- get
  pure $ apply s tau

-- Type Inference

unify :: Type -> Type -> Infer ()
unify l r = join $ doUnify <$> applySub l <*> applySub r

doUnify :: Type -> Type -> Infer ()
doUnify (TVar x) t =
  if (x `S.member` ftv t) && (t /= TVar x) then
    throwError $ "Failed to unify " <> tshow (TVar x) <> " with " <> tshow t
  else
    extendSub $ Subst (M.singleton x t)
doUnify t (TVar x) = doUnify (TVar x) t
doUnify (Fun a b) (Fun a' b') = doUnify a a' >> unify b b'
doUnify One One = pure ()
doUnify a b = throwError $ "Failed to unify " <> tshow a <> " with " <> tshow b

infer :: Gamma -> Expr -> Infer Typing
infer (Gamma gm) (Ref x) =
  case M.lookup x gm of
    Just xt ->
      refresh xt
    Nothing -> do
      alpha <- freshVar
      pure $ Typing (Delta $ M.singleton x alpha) alpha
infer g (Lam x e) = do  
  Typing delta@(Delta dm) sigma <- infer g e
  case M.lookup x dm of
    Just tau ->
      pure $ Typing (Delta $ M.delete x dm) (Fun tau sigma)
    Nothing -> do
      alpha <- freshVar
      pure $ Typing delta (Fun alpha sigma)
infer g (App a b) = do
  Typing ad at <- infer g a
  Typing bd bt <- infer g b
  alpha <- freshVar
  unify at (Fun bt alpha)
  abd <- mergeDelta ad bd
  applySub $ Typing abd alpha
infer g@(Gamma gm) (Let x a b) = do
  at@(Typing ad _) <- reduce x <$> infer g a
  Typing bd tau <- infer (Gamma $ M.insert x at gm) b
  abd <- mergeDelta ad bd
  pure $ Typing abd tau
infer _ Unit = pure $ Typing (Delta M.empty) (One)

runInfer :: Gamma -> Expr -> (Either T.Text Typing, ([Name], Subst))
runInfer g e =
  let vs = ((`Name` 0) . T.pack) <$> ([1..] >>= flip replicateM ['a'..'z'])
   in (runState . runExceptT $ (infer g e)) (vs, Subst $ M.empty)

-- Examples

name :: T.Text -> Name
name x = Name x 0

ref :: T.Text -> Expr
ref = Ref . name

lam :: T.Text -> Expr -> Expr
lam n e = Lam (name n) e

eid :: Expr
eid = Lam (Name "x" 0) $ Ref (Name "x" 0)

etrue :: Expr
etrue = lam "x" $ lam "y" $ ref "x"

edollar :: Expr
edollar = Lam (name "f") $ Lam (name "x") $ App (ref "f") (ref "x")

egen :: Expr
egen = Let (name "true") etrue $ Let (name "id") eid $ App (App (ref "true") (App (ref "id") (ref "id"))) Unit

test :: String -> Expr -> IO ()
test n e = do
  putStrLn $ " -- " ++ n ++ " --"
  putStrLn $ "Input:    " ++ show e
  case fst . runInfer (Gamma M.empty) $ rename M.empty e of
    Right t  -> putStrLn $ "Inferred: " ++ show t
    Left err -> putStrLn $ T.unpack err

main :: IO ()
main = do
  test "x" (ref "x")
  test "id" (eid)
  test "$" (edollar)
  test "egen" (egen)
