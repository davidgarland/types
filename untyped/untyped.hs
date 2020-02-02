{-
  An example implementation of the untyped lambda calculus, as a sort of
  beginners' guide to the idea.
-}

import qualified Data.Text as T

data Name
  = Name T.Text Int

main :: IO ()
main = putStrLn "This is a placeholder."
