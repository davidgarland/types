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
import Data.Maybe

-- Helper Functions

tshow :: Show a => a -> T.Text
tshow = T.pack . show

-- Core

data Nam =
  Nam T.Text Int
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

-- Show Instances

instance Show Nam where
  show (Nam t v) = T.unpack t ++ show v

instance Show Exp where
  show (Ref x) = show x
  show (Lam x e) = "λ" ++ show x ++ ". " ++ show e
  show (App a b) = "(" ++ show a ++ ") " ++ show b
  show (Let x a b) = "let " ++ show x ++ " = " ++ show a ++ " in " ++ show b
  show (Num n) = show n

instance Show Typ where
  show (Var x) = show x
  show (Fun a b) = show a ++ " -> " ++ show b
  show (Con x) = T.unpack x

-- Alpha-Renaming

type Rnm = M.Map T.Text Int

incNam :: Nam -> Rnm -> Rnm
incNam n@(Nam t _) r = let Nam _ v' = getNam r n in M.insert t (v' + 1) r

getNam :: Rnm -> Nam -> Nam
getNam r (Nam t v) = Nam t $ M.findWithDefault 0 t r

rename :: Rnm -> Exp -> Exp
rename r (Ref x) = Ref $ getNam r x
rename r (Lam x e) =
  let r' = incNam x r in
  Lam (getNam r' x) (rename r' e)
rename r (App a b) = App (rename r a) (rename r b)
rename r (Let x a b) =
  let r' = incNam x r in
  Let (getNam r' x) (rename r' a) (rename r' b)
rename r (Num n) = Num n

-- Type Variables & Substitution

itv :: Int -> Typ
itv n = Var $ Nam (tshow n <> "t") 0

ftv :: Typ -> S.Set Nam
ftv (Var x) = S.singleton x
ftv (Fun a b) = ftv a <> ftv b
ftv (Con _) = S.empty

apply :: Subst -> Typ -> Typ
apply s (Var x) = M.findWithDefault (Var x) x s
apply s (Fun a b) = Fun (apply s a) (apply s b)
apply s (Con x) = Con x

ftvDelta :: Delta -> S.Set Nam
ftvDelta = foldMap ftv

applyDelta :: Subst -> Delta -> Delta
applyDelta s = fmap (apply s)

-- Type Inference

type Delta = M.Map Nam Typ    -- Delta maps names to their monomorphic types.
type Subst = M.Map Nam Typ    -- A substitution from names to types.
type Typing = (Delta, Typ)    -- Typings pair a delta-context and a type.
type Gamma = M.Map Nam Typing -- Gamma maps names to their polymorphic typings.
type Infer t = ExceptT T.Text (State (Int, Subst)) t

extendSub :: Subst -> Infer ()
extendSub sub = modify (\(n, sub') -> (n, sub <> sub'))

applySub :: Typ -> Infer Typ
applySub tau = do
  (n, sub) <- get
  return $ apply sub tau

doUnify :: Typ -> Typ -> Infer ()
doUnify (Var v) t =
  if (v `S.member` ftv t) && (t /= Var v) then
    throwError "no"
  else
    extendSub $ M.singleton v t
doUnify t (Var v) = unify (Var v) t
doUnify (Fun a b) (Fun a' b') = do
  doUnify a a'
  join $ unify <$> applySub b <*> applySub b'
doUnify (Con a) (Con b) =
  if a == b then
    pure ()
  else
    throwError $ "Types not equal: " <> tshow a <> " and " <> tshow b
doUnify a b = throwError $ "Types not equal: " <> tshow a <> "and " <> tshow b

unify :: Typ -> Typ -> Infer ()
unify l r = join $ doUnify <$> applySub l <*> applySub r

fresh :: Infer Int
fresh = do
  (i, s) <- get
  put (i + 1, s)
  return i

freshVar :: Infer Typ
freshVar = do
  i <- fresh
  return $ itv i

mergeDelta :: Delta -> Delta -> Infer Delta
mergeDelta da db = M.mergeA keep keep try da db where
  keep = M.preserveMissing
  try = M.zipWithAMatched $ \v a b -> do
    unify a b
    b' <- applySub b
    return b' -- TODO: is this right???

reduceTyping :: Nam -> Typing -> Typing
reduceTyping x (delta, tau) =
  let tau_fv = ftv tau
      delta' = M.filter keep (M.delete x delta)
      keep sigma = not $ S.null (ftv sigma `S.intersection` tau_fv)
   in (delta', tau)

infer :: Gamma -> Exp -> Infer Typing
infer g (Ref x) =
  case M.lookup x g of
    Just t@(delta, tau) -> do
      (i, s) <- get
      let tau_fv = S.toList (ftv tau `S.difference` foldMap ftv delta)
      put (i + length tau_fv, s)
      let sub = M.fromList . zip tau_fv $ fmap itv [1..length tau_fv]
      return (applyDelta sub delta, apply sub tau)
    Nothing -> do
      alpha <- freshVar
      return (M.singleton x alpha, alpha)
infer g (App a b) = do
  (da, ta) <- infer g a
  (db, tb) <- infer g b
  alpha <- freshVar
  unify (Fun tb alpha) ta
  (_, s) <- get
  let da' = applyDelta s da
      db' = applyDelta s db
  dab <- mergeDelta da' db'
  return (dab, apply s alpha)
infer g (Lam x e) = do
  (_, s) <- get
  alpha <- freshVar
  let mono = (M.singleton x alpha, alpha)
  let new_env = (M.insert x mono g)
  (body_delta, body_ty) <- infer new_env e
  let delta' = (M.delete x body_delta)
  return (delta', apply s (Fun alpha body_ty))
infer g (Let x a b) = do
  exp_t <- infer g a
  let exp_s = reduceTyping x exp_t
      g' = M.insert x exp_s g
  infer g' b
infer g (Num n) = return $ (M.empty, Con "Int")

test :: String -> Exp -> IO ()
test n e = do
  putStrLn $ " -- " ++ n ++ " --"
  putStrLn $ "Raw:     " ++ show e
  putStrLn $ "Renamed: " ++ (show $ rename M.empty e)
  let (Right (_, typ), (_, b)) = (runState . runExceptT $ infer M.empty e) (0, M.empty)
  putStrLn $ "Inferred: " ++ show b ++ " |- " ++ show typ

eid :: Exp
eid = Lam (Nam "x" 0) $ Ref (Nam "x" 0)

epid :: Exp
epid = Let (Nam "z" 0) eid $ Ref (Nam "z" 0)

edollar :: Exp
edollar = Lam (Nam "f" 0) $ Lam (Nam "x" 0) $ App (Ref (Nam "f" 0)) (Ref (Nam "x" 0))

main :: IO ()
main = do
  test "id" eid
  test "pid" epid
  test "$" edollar
