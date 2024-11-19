{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
module ModularCarrier where

-- Implementation of Modular Carriers
-- From the paper: N. Wu and T. Schrijvers, “Efficient Algebraic Effect Handlers,” p. 22.

import FreeMonad (Free(..), fold, type (+)(..), Void, (#))
import Control.Monad

class MCarrier c where
  fwd :: Monad m => m (c m) -> c m

forward :: (Functor sig, MCarrier c) => sig (c (Free sig)) -> c (Free sig)
forward op = fwd (Op (fmap Return op))

newtype FreeEM a m = FreeEM { unFreeEM :: m a }
instance MCarrier (FreeEM a) where
  fwd = FreeEM . join . fmap unFreeEM

data MHandler sig c a b = MHandler {
    gen :: forall m . Monad m => a -> c m,
    alg :: forall m . Monad m => sig (c m) -> c m,
    run :: forall m . Monad m => c m -> m b
}

handle :: (Functor f, Functor sig, MCarrier c)
       => MHandler sig c a b -> Free (sig + f) a -> Free f b
handle h = run h . fold (gen h) (alg h # forward)

-- Evil

newtype Evil a = Evil a deriving (Show, Functor)

newtype EvilCarrier a m = EC { unEC :: m (() -> m a) }

hEvil :: MHandler Evil (EvilCarrier a) a a
hEvil = MHandler {
  gen = \x -> EC . return $ \() -> return x,
  alg = \(Evil k) -> undefined,
  run = undefined
}