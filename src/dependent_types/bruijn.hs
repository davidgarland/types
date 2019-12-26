{-
  An implementation of substitution, normalization via beta-reduction, and a
  simple implementation of type inference (NOT normalization; in other words,
  all lambdas are type-annotated) for dependent types.

  The code here is largely adapated from the following article:
    http://math.andrej.com/2012/11/08/how-to-implement-dependent-type-theory-i/
  except retrofitted to work with de bruijn indices, and a (possibly naiive?)
  implementation of cumulative universes.
-}

{-# LANGUAGE OverloadedStrings, DeriveFunctor #-}

import qualified Data.Text as T
import qualified Data.Map as M
import Control.Monad.Except
import Control.Monad.State

-- Helper Defintions

tshow :: Show a => a -> T.Text
tshow = T.pack . show

-- Core Syntax

data AbsT a
  = Abs T.Text (ExpT a) (ExpT a)
  deriving (Eq, Functor)
type Abs = AbsT Int

data ExpT a 
  = Ref T.Text
  | Idx a
  | Lam (AbsT a)
  | App (ExpT a) (ExpT a)
  | Unv Int
  | Pi  (AbsT a)
  | Tup (AbsT a) (ExpT a)
  | Sgm (AbsT a)
  deriving (Eq, Functor)
type Exp = ExpT Int

instance Show a => Show (AbsT a) where
  show (Abs x (Lam a) e) = "(" ++ show (Lam a) ++ "). " ++ show e
  show (Abs x (Pi a) e) = "(" ++ show (Pi a) ++ "). " ++ show e
  show (Abs x t e) = show t ++ ". " ++ show e

instance Show a => Show (ExpT a) where
  show (Ref n) = T.unpack n
  show (Idx i) = show i
  show (Lam a) = "λ" ++ show a
  show (App (Lam a) b) = "(" ++ show (Lam a) ++ ") " ++ show b
  show (App a (App b c)) = show a ++ " (" ++ show (App b c) ++ ")"
  show (App a b) = show a ++ " " ++ show b
  show (Pi  a) = "Π" ++ show a
  show (Unv u) = "Set" ++ show u
  show (Tup (Abs _ t b) a) = "(" ++ show a ++ ": " ++ show t ++ ", " ++ show b ++ ")"
  show (Sgm a) = "Σ" ++ show a

-- Substitution

substRaw :: Int -> Exp -> Exp -> Exp
substRaw k w (Ref n) = Ref n
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
substRaw k w (Unv u) = Unv u
substRaw k w (Tup (Abs x t b) a) =
  Tup (Abs x (substRaw k w t) (substRaw (k + 1) w t)) (substRaw k w a)
substRaw k w (Sgm (Abs x t e)) =
  Sgm (Abs x (substRaw k w t) (substRaw (k + 1) w e))

subst :: Exp -> Exp -> Exp
subst = substRaw 0

-- Normalization

type Gam = ([Exp], M.Map T.Text (Exp, Maybe Exp))

gempty :: Gam
gempty = ([], M.empty)

norm :: Gam -> Exp -> Either T.Text Exp
norm (_, m) (Ref n) =
  case M.lookup n m of
    Just (_, Just v) -> Right v
    Just (_, Nothing) -> Right $ Ref n
    Nothing -> Left $ "Undefined identifier: " <> n
norm g (Idx i) = Right $ Idx i
norm g (Lam (Abs x t e)) = do
  t' <- norm g t
  e' <- norm g e
  Right . Lam $ Abs x t' e'
norm g (App a b) = do
  a' <- norm g a
  b' <- norm g b
  case a' of
    Lam (Abs x t e) -> norm g $ subst b' e
    _ -> Right $ App a' b'
norm g (Pi (Abs x t e)) = do
  t' <- norm g t
  e' <- norm g e
  Right . Pi $ Abs x t' e'
norm g (Unv u) = Right $ Unv u
norm g (Tup (Abs x t b) a) = do
  t' <- norm g t
  a' <- norm g a
  b' <- norm g b
  Right $ Tup (Abs x t' b') a'
norm g (Sgm (Abs x t e)) = do
  t' <- norm g t
  e' <- norm g e
  Right . Sgm $ Abs x t' e'

-- Type Passing

passes :: Exp -> Exp -> Bool
passes (Unv a) (Unv b) = a <= b
passes a b = a == b

checkPasses :: Exp -> Exp -> Either T.Text ()
checkPasses a b =
  if passes a b then
    Right ()
  else
    Left $ "Attempt to pass `" <> tshow a <> "` as `" <> tshow b <> "`."

-- Inference

inferUnv :: Gam -> Exp -> Either T.Text Int
inferUnv g e = do
  t <- infer g e
  t' <- norm g t
  case t' of
    Unv k -> Right k
    _ -> Left "Type expected."

inferPi :: Gam -> Exp -> Either T.Text Abs
inferPi g e = do
  t <- infer g e
  t' <- norm g t
  case t' of
    Pi a -> Right a
    _ -> Left "Function expected."

infer :: Gam -> Exp -> Either T.Text Exp
infer (_, m) (Ref n) =
  case M.lookup n m of
    Just (t, _) -> Right t
    Nothing -> Left $ "Undefined identifier: " <> n
infer (s, _) (Idx i) = 
  if i < length s then
    Right . fmap (+ succ i) $ (s !! i)
  else
    Left $ "Index out of bounds: " <> tshow i
infer g@(s, m) (Lam (Abs x t e)) = do
  t' <- norm g t
  _ <- inferUnv g t'
  et <- infer (t' : s, m) e
  Right . Pi $ Abs x t' et
infer g@(s, m) (App a b) = do
  a' <- norm g a
  Abs x t e <- inferPi g a'
  b' <- norm g b
  bt <- infer g b'
  checkPasses bt t
  Right $ subst b' e
infer g@(s, m) (Pi (Abs x t e)) = do
  t' <- norm g t
  tu <- inferUnv g t'
  eu <- inferUnv (t' : s, m) e
  Right . Unv $ max tu eu
infer g (Unv u) = Right $ Unv (u + 1)
infer g@(s, m) (Tup (Abs x t b) a) = do
  t' <- norm g t
  _ <- inferUnv g t'
  at <- infer g a
  checkPasses at t'
  bt <- infer (t' : s, m) b
  Right . Sgm $ Abs x t' bt
infer g@(s, m) (Sgm (Abs x t e)) = do
  t' <- norm g t
  e' <- norm g e
  tu <- inferUnv g t'
  eu <- inferUnv g e'
  Right . Unv $ max tu eu

-- Examples

lam :: T.Text -> Exp -> Exp -> Exp
lam x t e = Lam $ Abs x t e

pit :: T.Text -> Exp -> Exp -> Exp
pit x t e = Pi  $ Abs x t e

-- (x : T = a, b)
tup :: T.Text -> Exp -> Exp -> Exp -> Exp
tup x t a b = Tup (Abs x t b) a

eid :: Exp
eid = lam "t" (Unv 1) . lam "x" (Idx 0) $ (Idx 0)

edollar :: Exp
edollar = lam "t" (Unv 1) 
        . lam "f" (pit "y" (Idx 0) (Idx 1))
        . lam "x" (Idx 1) 
        $ App (Idx 1) (Idx 0)

exy :: Exp
exy = lam "t" (Unv 1)
    . lam "x" (Idx 0)
    . lam "y" (Idx 1)
    $ tup "x" (Idx 2) (Idx 1) (Idx 1) 

-- Main Program

test :: String -> Gam -> Exp -> IO ()
test n g e = do
  putStrLn $ "-- " ++ n ++ " --"
  putStrLn $ "Raw:        " ++ show e
  putStrLn $ "Norm: " ++ (show $ norm g e)
  putStrLn $ "Type: " ++ (show $ infer g e)

main = do
  test "id" gempty eid
  test "id Unv 0" gempty (App eid (Unv 0))
  test "$" gempty edollar
  test "$ Unv 0" gempty (App edollar (Unv 0))
  test "xy" gempty exy
  test "xy Unv 0" gempty (App exy (Unv 0))
