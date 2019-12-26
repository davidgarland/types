{-
  An example implementation of compositional type elaboration, inference, and   
  checking.
  
  The code here is largely adapted from the following article:
    https://hydraz.semi.works/posts/2019-01-28.html
  See also their full implementation, MLΔ:
    https://github.com/zardyh/mld
-}

{-# LANGUAGE OverloadedStrings #-}

import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.Map.Merge.Strict as M
import qualified Data.Set as S
import Control.Monad.Except
import Control.Monad.State

-- Core

data Nam
  = Nam T.Text Int
  deriving (Eq, Ord)

data Exp
  = Ref Nam
  | Lam Nam Exp
  | App Exp Exp
  | Let Nam Exp Exp
  | Num Int

data Typ
  = Var Nam
  | Fun Typ Typ
  | Con T.Text
  deriving (Eq)

newtype Delta   = Delta (M.Map Nam Typ)
newtype Subst   = Subst (M.Map Nam Typ)
data    Typing  = Typing Delta Typ
newtype Gamma   = Gamma (M.Map Nam Typing)
type    Infer t = ExceptT T.Text (State ([Nam], Subst)) t


-- Show Instances

instance Show Nam where
  show (Nam t _) = T.unpack t

instance Show Exp where
  show (Ref x) = show x
  show (Lam x e) = "λ" ++ show x ++ ". " ++ show e
  show (App a (App b c)) = show a ++ " (" ++ show (App b c) ++ ")"
  show (App a b) = show a ++ " " ++ show b
  show (Let x a b) = "let " ++ show x ++ " = " ++ show a ++ " in " ++ show b
  show (Num n) = show n

instance Show Typ where
  show (Var x) = show x
  show (Fun (Fun a b) c) = "(" ++ show (Fun a b) ++ ") -> " ++ show c
  show (Fun a b) = show a ++ " -> " ++ show b
  show (Con x) = T.unpack x

instance Show Delta where
  show (Delta dm) = "{" ++ (showNamMap $ M.toList dm) ++ "}"

instance Show Subst where
  show (Subst sm) = "{" ++ (showNamMap $ M.toList sm) ++ "}"

instance Show Typing where
  show (Typing delta tau) = show delta ++ " |- " ++ show tau

showNamMap :: [(Nam, Typ)] -> String
showNamMap [] = ""
showNamMap ((k, v) : []) = show k ++ " : " ++ show v
showNamMap ((k, v) : kvs) = show k ++ " : " ++ show v ++ ", " ++ showNamMap kvs

tshow :: Show a => a -> T.Text
tshow = T.pack . show

-- Alpha-Renaming

type Rnm = M.Map T.Text Int

incNam :: Nam -> Rnm -> Rnm
incNam n@(Nam t _) r = let Nam _ v' = getNam r n in M.insert t (v' + 1) r

getNam :: Rnm -> Nam -> Nam
getNam r (Nam t _) = Nam t $ M.findWithDefault 0 t r

rename :: Rnm -> Exp -> Exp
rename r (Ref x) = Ref $ getNam r x
rename r (Lam x e) =
  let r' = incNam x r in
  Lam (getNam r' x) (rename r' e)
rename r (App a b) = App (rename r a) (rename r b)
rename r (Let x a b) =
  let r' = incNam x r in
  Let (getNam r' x) (rename r' a) (rename r' b)
rename _ (Num n) = Num n

-- Typeclasses

instance Semigroup Subst where
  a@(Subst ma) <> b@(Subst mb) =
    Subst (fmap (apply b) ma <> fmap (apply a) mb)

class Substable a where
  apply :: Subst -> a -> a
  ftv :: a -> S.Set Nam

instance Substable Typ where
  ftv (Var x) = S.singleton x
  ftv (Fun a b) = ftv a <> ftv b
  ftv (Con _) = S.empty
  apply (Subst m) (Var x) = M.findWithDefault (Var x) x m
  apply s (Fun a b) = Fun (apply s a) (apply s b)
  apply _ x@(Con _) = x

instance Substable Delta where
  apply s (Delta m) = Delta $ fmap (apply s) m
  ftv (Delta m) = foldMap ftv m

instance Substable Typing where
  apply s (Typing d t) = Typing (apply s d) (apply s t)
  ftv (Typing d t) = ftv d <> ftv t

-- Monadic Functions

freshVar :: Infer Typ
freshVar = do
  (vars, s) <- get
  case vars of
    x : xs -> do
      put (xs, s)
      return $ Var x
    _ -> throwError "Failed to generate a fresh variable. Is the supply empty?"

refresh :: Typing -> Infer Typing
refresh (Typing delta tau) = do
  (vs, s) <- get
  let tau_fv = S.toList (ftv tau `S.difference` ftv delta)
  let (used, vs') = splitAt (length tau_fv) vs
  let s' = Subst $ M.fromList (zip tau_fv (map Var used))
  put (vs', s)
  return . apply (s <> s') $ Typing delta tau

reduce :: Nam -> Typing -> Typing
reduce v (Typing (Delta dm) tau) = do
  let tau_fv = ftv tau
  let keep sigma = not . S.null $ ftv sigma `S.intersection` tau_fv
  let dm' = M.filter keep (M.delete v dm)
  Typing (Delta dm') tau

extendSub :: Subst -> Infer ()
extendSub s' = modify (\(vs, s) -> (vs, s <> s'))

mergeDelta :: Delta -> Delta -> Infer Delta
mergeDelta (Delta am) (Delta bm) = Delta <$> M.mergeA keep keep try am bm where
  keep = M.preserveMissing
  try = M.zipWithAMatched $ \_ a b -> do
    unify a b
    b' <- applySub b
    return $ b'

applySub :: Substable t => t -> Infer t
applySub tau = do
  (_, s) <- get
  return $ apply s tau

-- Type Inference

doUnify :: Typ -> Typ -> Infer ()
doUnify (Var x) t =
  if (x `S.member` ftv t) && (t /= Var x) then
    throwError $ "Failed to unify " <> tshow (Var x) <> " with " <> tshow t
  else
    extendSub $ Subst (M.singleton x t)
doUnify t (Var x) = doUnify (Var x) t
doUnify (Fun a b) (Fun a' b') = do
  doUnify a a'
  join $ unify <$> applySub b <*> applySub b'
doUnify (Con a) (Con b) =
  if a == b then
    return ()
  else
    throwError $ "Failed to unify " <> tshow a <> " with " <> tshow b
doUnify a b = throwError $ "Failed to unify " <> tshow a <> " with " <> tshow b

unify :: Typ -> Typ -> Infer ()
unify l r = join $ doUnify <$> applySub l <*> applySub r

infer :: Gamma -> Exp -> Infer Typing
infer (Gamma gm) (Ref x) =
  case M.lookup x gm of
    Just xt ->
      refresh xt
    Nothing -> do
      alpha <- freshVar
      return $ Typing (Delta $ M.singleton x alpha) alpha
infer g (Lam x e) = do  
  Typing delta@(Delta dm) sigma <- infer g e
  case M.lookup x dm of
    Just tau ->
      return $ Typing (Delta $ M.delete x dm) (Fun tau sigma)
    Nothing -> do
      alpha <- freshVar
      return $ Typing delta (Fun alpha sigma)
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
  return $ Typing abd tau
infer _ (Num _) = return $ Typing (Delta M.empty) (Con "Int")

runInfer :: Gamma -> Exp -> (Either T.Text Typing, ([Nam], Subst))
runInfer g e =
  let vs = ((flip Nam $ 0) . T.pack) <$> ([1..] >>= flip replicateM ['a'..'z'])
   in (runState . runExceptT $ (infer g e)) (vs, Subst $ M.empty)

-- Examples

nam :: T.Text -> Nam
nam x = Nam x 0

ref :: T.Text -> Exp
ref = Ref . nam

lam :: T.Text -> Exp -> Exp
lam n e = Lam (nam n) e

eid :: Exp
eid = Lam (Nam "x" 0) $ Ref (Nam "x" 0)

etrue :: Exp
etrue = lam "x" $ lam "y" $ ref "x"

edollar :: Exp
edollar = Lam (Nam "f" 0) $ Lam (Nam "x" 0) $ App (Ref (Nam "f" 0)) (Ref (Nam "x" 0))

egen :: Exp
egen = Let (nam "true") etrue $ Let (nam "id") eid $ App (App (ref "true") (App (ref "id") (ref "id"))) (Num 0)

test :: String -> Exp -> IO ()
test n e = do
  putStrLn $ " -- " ++ n ++ " --"
  putStrLn $ "Input:    " ++ show e
  case fst $ runInfer (Gamma M.empty) e of
    Right t  -> putStrLn $ "Inferred: " ++ show t
    Left err -> putStrLn $ T.unpack err

main :: IO ()
main = do
  test "x" (ref "x")
  test "id" (eid)
  test "$" (edollar)
  test "egen" (egen)
