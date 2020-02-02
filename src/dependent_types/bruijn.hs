{-
  An implementation of substitution, normalization via beta-reduction, and
  basic type inference (NOT elaboration; in other words, all lambdas are
  type-annotated) for dependent types.

  The code here is largely adapated from the following article:
    http://math.andrej.com/2012/11/08/how-to-implement-dependent-type-theory-i/
  However, there are several key differences:
  - I use De Bruijn indices, which he gets around to doing later, but he uses
  "explicit substitutions"-- I just do it normally.
  - Beta-reduction is done "on the fly" as part of inference, rather than being
  its own function. In my opinion this makes things less error prone, and it
  also keeps the code much smaller.
  - I implement a cumulative universe heirarchy, though perhaps naiively (?)
  - I implement dependent pairs, sigma types, and the fst/snd projections.
  - He used a flavor of ML, whereas this is in Haskell.
-}

{-# LANGUAGE OverloadedStrings, DeriveFunctor #-}
{-# OPTIONS_GHC -Wall #-}

import qualified Data.Text as T

-- Helper Defintions

tshow :: Show a => a -> T.Text
tshow = T.pack . show

-- Core Syntax

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
  | One                            -- | 1
  deriving (Eq, Functor)
type Exp = ExpT Int

instance Show a => Show (AbsT a) where
  show (Abs _ (Lam a) e) = "(" ++ show (Lam a) ++ "). " ++ show e
  show (Abs _ (Pi a) e) = "(" ++ show (Pi a) ++ "). " ++ show e
  show (Abs _ t e) = show t ++ ". " ++ show e

instance Show a => Show (ExpT a) where
  show (Idx i) = show i
  show (Lam a) = "\\" ++ show a
  show (App (Lam a) b) = "(" ++ show (Lam a) ++ ") " ++ show b
  show (App a (App b c)) = show a ++ " (" ++ show (App b c) ++ ")"
  show (App a b) = show a ++ " " ++ show b
  show (Pi  a) = "^" ++ show a
  show (Unv u) = "Set" ++ show u
  show (Tup a b t) = "(" ++ show a ++ ", " ++ show b ++ ") : (" ++ show t ++ ")"
  show (Sgm a) = "E" ++ show a
  show (Fst e) = "fst " ++ show e
  show (Snd e) = "snd " ++ show e
  show Unit = "()"
  show One = "()"

-- Substitution

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
substRaw _ _ One = One

subst :: Exp -> Exp -> Exp
subst = substRaw 0

-- Type Passing

subtype :: Exp -> Exp -> Either T.Text ()
subtype (Unv a) (Unv b) | a <= b = Right ()
subtype a b | a == b = Right ()
subtype a b = Left $ "Attempt to pass `" <> tshow a <> "` as `" <> tshow b <> "`."

-- Inference / Normalization

type Gam = [Exp]

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

infer :: Gam -> Exp -> Either T.Text (Exp, Exp)
infer g (Idx i)
  | i < length g = Right (fmap (+ succ i) (g !! i), Idx i)
  | otherwise = Left $ "Index out of bounds: " <> tshow i
infer g (Lam (Abs x t e)) = do
  (_, t') <- inferUnv g t
  (et, e') <- infer (t' : g) e
  Right (Pi $ Abs x t' et, Lam $ Abs x t' e')
infer g (App a b) = do
  (Abs _ t r, a') <- inferPi g a
  (bt, b') <- infer g b
  subtype bt t
  case a' of
    Lam (Abs _ _ e) -> Right (subst b' r, subst b' e)
    _ -> Right (subst b' r, App a' b')
infer _ (Unv k) = Right (Unv (k + 1), Unv k)
infer g (Pi (Abs x t e)) = do
  (tu, t') <- inferUnv g t
  (eu, e') <- inferUnv (t' : g) e
  Right (Unv $ max tu eu, Pi $ Abs x t' e')
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
infer g (Sgm (Abs x t e)) = do
  (tu, t') <- inferUnv g t
  (eu, e') <- inferUnv g e
  if tu == eu then
    Right (Unv tu, Sgm $ Abs x t' e')
  else
    Left "Universe levels of sigma types' elements must be the same."
infer g (Fst s) = do
  (Abs _ t _, s') <- inferSgm g s
  Right (t, Fst s')
infer g (Snd s) = do
  (Abs _ _ e, s') <- inferSgm g s
  Right (subst (Fst s') e, Snd s')
infer _ Unit = Right (One, Unit)
infer _ One = Right (Unv 0, One)

-- Examples

lam :: T.Text -> Exp -> Exp -> Exp
lam x t e = Lam $ Abs x t e

pit :: T.Text -> Exp -> Exp -> Exp
pit x t e = Pi  $ Abs x t e

eid :: Exp
eid = lam "t" (Unv 1) . lam "x" (Idx 0) $ (Idx 0)

edollar :: Exp
edollar = lam "t" (Unv 1) 
        . lam "f" (pit "y" (Idx 0) (Idx 1))
        . lam "x" (Idx 1) 
        $ App (Idx 1) (Idx 0)

-- Main Program

test :: String -> Gam -> Exp -> IO ()
test n g e = do
  putStrLn $ "-- " ++ n ++ " --"
  putStrLn $ "Raw:        " ++ show e
  let te = infer g e
  putStrLn $ "Norm: " ++ (show . fmap snd $ te)
  putStrLn $ "Type: " ++ (show . fmap fst $ te)

main :: IO ()
main = do
  test "id" [] eid
  test "id Unv 0" [] (App eid (Unv 0))
  test "id One" [] (App eid One)
  test "$" [] edollar
  test "$ Unv 0" [] (App edollar (Unv 0))
  test "$ One" [] (App edollar One)
