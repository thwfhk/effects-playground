{-# LANGUAGE RankNTypes #-}
import Control.Monad (liftM, liftM2, ap, join)

-- | Free Monad
data Free sig a = Return a | Op (sig (Free sig a))

instance Functor sig => Functor (Free sig) where
  fmap = liftM
instance Functor sig => Applicative (Free sig) where
  pure  = return
  (<*>) = ap
instance Functor sig => Monad (Free sig) where
  return x = Return x
  Return x >>= f = f x
  Op op    >>= f = Op (fmap (>>=f) op)

free :: (Functor f, Monad g) =>
        (forall a. f a -> g a) -> (forall a. Free f a -> g a)
free f (Return a) = return a
free f (Op fa) = join (f (fmap (free f) fa)) -- bottom-up
-- free f (Op fa) = f (fmap (free f) fa) >>= id
-- free f (Op fa) = f fa >>= free f -- top-down
-- free f (Op fa) = join (fmap (free f) (f fa))
-- I think this two kinds of implementation is identical because of
-- the property of monad homomorphism.