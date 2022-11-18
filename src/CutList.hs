module CutList where

import Control.Monad (ap, when)
import Prelude hiding (fail)

data CutList a = a :. CutList a | Nil | Zero

cut :: CutList ()
cut = () :. Zero

fromList :: [a] -> CutList a
fromList (x : xs) = x :. fromList xs
fromList [] = Nil

toList :: CutList a -> [a]
toList (x :. xs) = x : toList xs
toList _ = []

instance Functor CutList where
  fmap f (x :. xs) = f x :. fmap f xs
  fmap f Nil = Nil
  fmap f Zero = Zero
instance Applicative CutList where
  pure = return
  (<*>) = ap

concatC :: CutList (CutList a) -> CutList a
concatC ((a :. xs) :. xss) = a :. concatC (xs :. xss)
concatC (Nil :. xss) = concatC xss
concatC (Zero :. _) = Zero
concatC Nil = Nil
concatC Zero = Zero

instance Monad CutList where
  return a = a :. Nil
  m >>= f = concatC (fmap f m)

---------------------------------------------------------------
fail :: CutList ()
fail = Nil

takeWhileC :: (a -> Bool) -> CutList a -> CutList a
takeWhileC p xs = do
  x <- xs
  -- when (not (p x)) (cut >> fail)
  when (not (p x)) Zero
  return x

-- >>> toList (takeWhileC even (fromList [2,4,5,8]))
-- [2,4]

