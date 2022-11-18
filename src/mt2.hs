{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}

import Control.Monad.Trans (MonadTrans, lift)
import Control.Monad (liftM, liftM2, ap)
import Data.Char (isAlpha, isNumber)
import Prelude hiding (MonadFail, fail)
import Control.Monad.State.Lazy
import FreeMonad

class Monad m => MNondet m where
  mzero  :: m a
  mplus  :: m a -> m a -> m a

-- class Monad m => MState s m | m -> s where
--     get :: m s
--     put :: s -> m ()

instance MNondet (StateT s []) where
  mzero = StateT $ \s -> []
  -- mplus :: StateT s [] a -> StateT s [] a -> StateT s [] a
  mplus x y = StateT $ \s -> runStateT x s ++ runStateT y s
