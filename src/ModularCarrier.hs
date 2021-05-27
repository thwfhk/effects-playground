
-- Implementation of Modular Carriers
-- From the paper: N. Wu and T. Schrijvers, “Efficient Algebraic Effect Handlers,” p. 22.

module ModularCarrier where

-- class ModularCarrier c where
  -- fwdMC :: Monad m => m (c m) -> c m

-- fwdsig :: (Functor sig, ModularCarrier c) => sig (c (Free sig)) -> c (Free sig)
-- fwdsig op = fwdMC (Op (fmap Return op))

-- -- Carrier for State s
-- newtype StateH s a m = StateH {runStateH :: s -> m a}
-- instance ModularCarrier (StateH s a) where
--   fwdMC :: (Monad m) => m (StateH s a m) -> StateH s a m
--   fwdMC mf = StateH (\s -> mf >>= \f -> runStateH f s)

-- handleSH :: Monad m => Free (State s) a -> StateH s a m
-- handleSH = fold genSH algSH
--   where
--     genSH :: Monad m => a -> StateH s a m
--     genSH x = StateH (\s -> return x)
--     algSH :: Monad m => State s (StateH s a m) -> StateH s a m
--     algSH (Get k) = StateH (\s -> runStateH (k s) s)
--     algSH (Put s' k) = StateH (\s -> runStateH (k ()) s')