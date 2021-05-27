{-# LANGUAGE FlexibleContexts, UndecidableInstances, StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}

data Foobar x = Foo (x (Foobar x))
deriving instance Show (x (Foobar x)) => Show (Foobar x)


class Functor f => TermAlgebra h f | h -> f where
  var :: a -> h a
  con :: f (h a) -> h a

class Test1 a b where
  hi1 :: a -> b

class Test2 a b | a -> b where
  hi2 :: a -> b

instance Test1 Int Int where
  hi1 = const 3

instance Test1 Int Char where
  hi1 = const 'a'

-- instance Test2 Int Int where
--   hi2 = const 3

-- instance Test2 Int Char where
--   hi2 = const 3

qwq :: Monad m => m Int
qwq = return 3

test :: Maybe Int
test = do
  x <- Just 5
  y <- if x == 5 then Nothing else Just 6
  return (y + 1)

test' = Just 5 >>= (\x -> if x == 5 then Nothing else Just 6 >>= (\y -> return (y + 1)))