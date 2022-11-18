module CutList2 where

import Control.Monad (ap, when, join)
import Prelude hiding (fail)
import Debug.Trace

data Idem a = Ret a | Flag a deriving Show

fromIdem :: Idem a -> a
fromIdem (Ret a) = a
fromIdem (Flag a) = a

instance Functor Idem where
  fmap f (Ret a) = Ret (f a)
  fmap f (Flag a) = Flag (f a)
instance Applicative Idem where
  pure = return
  (<*>) = ap
instance Monad Idem where
  return a = Ret a
  Ret a >>= f = f a
  Flag a >>= f = Flag (fromIdem (f a))

distr :: [Idem a] -> Idem [a]
distr (Ret a : xs) = fmap (\y -> a : y) (distr xs)
distr (Flag a : xs) = Flag [a]
distr [] = Ret []

newtype CutList a = CutList { fromCutList :: Idem [a] } deriving Show

cut :: CutList ()
cut = CutList $ Flag [()]

fromList :: [a] -> CutList a
fromList = CutList . Ret

toList :: CutList a -> [a]
toList = fromIdem . fromCutList

append :: CutList a -> CutList a -> CutList a
append (CutList (Ret xs)) ys = CutList $ fmap ((++) xs) $ fromCutList ys
append (CutList (Flag xs)) _ = CutList (Flag xs)

instance Functor CutList where
  fmap f x = CutList $ fmap (fmap f) (fromCutList x)
instance Applicative CutList where
  pure = return
  (<*>) = ap
instance Monad CutList where
  -- return a = CutList $ fmap return (return a)
  return a = CutList $ return (return a)
  -- return a = CutList $ Ret [a] -- any difference ?
  m >>= f = CutList $ fmap join (join (fmap distr (fmap (fmap (fromCutList . f)) (fromCutList m))))
  -- m >>= f = CutList $ fmap join (join (fmap distr (fromCutList (fmap (fromCutList . f) m))))

---------------------------------------------------------------
fail :: CutList a
fail = CutList $ Ret []

scope :: CutList a -> CutList a
scope = fromList . toList
-- scope = flag2ret'

-- flag2ret :: Idem a -> Idem a
-- flag2ret (Flag x) = Ret x
-- flag2ret x = x

-- flag2ret' :: CutList a -> CutList a
-- flag2ret' = CutList . flag2ret . fromCutList

takeWhileC :: (a -> Bool) -> CutList a -> CutList a
takeWhileC p xs = scope $ do
  x <- xs
  when (not (p x)) (cut >> fail)
  return x

-- >>> takeWhileC even (fromList [2,4,5,8])
-- CutList {fromCutList = Ret [2,4]}

prefixes :: CutList Int
prefixes = do
  x <- fromList [fromList [2,4,5,2], fromList [8,9,10]]
  traceM $ show x
  traceM $ show (takeWhileC even x)
  y <- takeWhileC even x
  traceM $ show y
  return y
-- >>> prefixes
-- CutList {fromCutList = Ret [2,4,8]}

cutlist :: [a] -> CutList a
cutlist = CutList . Ret
