{-# LANGUAGE StandaloneDeriving, UndecidableInstances #-}
{-# LANGUAGE TypeOperators, EmptyCase, InstanceSigs #-}

-- Implementation of Algebraic Effects using Free Monad
-- From the paper: N. Wu and T. Schrijvers, “Efficient Algebraic Effect Handlers,”

module FreeMonad where

import Control.Monad (liftM, liftM2, ap)

-- | Free Monad
data Free sig a = Return a | Op (sig (Free sig a))
deriving instance (Show (sig (Free sig a)), Show a) => Show (Free sig a)

instance Functor sig => Functor (Free sig) where
  fmap = liftM
instance Functor sig => Applicative (Free sig) where
  pure  = return
  (<*>) = ap
instance Functor sig => Monad (Free sig) where
  return x = Return x
  Return x >>= f = f x
  Op op    >>= f = Op (fmap (>>=f) op)

-- | Composition of sig/operations/effects
data (sig1 + sig2) a = Inl (sig1 a) | Inr (sig2 a)
instance (Functor sig1, Functor sig2) => Functor (sig1 + sig2) where
  fmap f (Inl x) = Inl (fmap f x)
  fmap f (Inr y) = Inr (fmap f y)

(#) :: (sig1 b -> b) -> (sig2 b -> b) -> ((sig1 + sig2) b -> b)
(alg1 # alg2) (Inl op) = alg1 op
(alg1 # alg2) (Inr op) = alg2 op

-- | handler
fold :: Functor sig => (a -> b) -> (sig b -> b) -> (Free sig a -> b)
fold gen alg (Return x) = gen x
fold gen alg (Op op)    = alg (fmap (fold gen alg) op)

-- | normal forward
fwd :: Functor sig => sig (Free sig b) -> Free sig b
fwd op = Op op

-- | forward for parameter-passing style
fwdPP :: Functor sig => sig (s -> Free sig b) -> (s -> Free sig b)
fwdPP op = \s -> Op $ fmap (\k -> k s) op

-- Some common operations, the most general form is 
--    data Sig a b k = Op a (b -> k)

--------------------------------
-- | Void
data Void k
instance Functor Void where
  fmap f x = case x of

-- Void is usually used as the leftmost
handleV :: Free Void a -> a
handleV (Return x) = x

--------------------------------
-- | Fail
data Fail k = Fail
instance Functor Fail where
  fmap f Fail = Fail
-- smart constructor
fail :: Free Fail a
fail = Op Fail

handleF :: Functor sig => Free (Fail + sig) a -> Free sig (Maybe a)
handleF = fold genF (algF # fwd)
  where
    genF :: Monad m => a -> m (Maybe a)
    genF x = return (Just x)
    algF :: Monad m => Fail (m (Maybe a)) -> m (Maybe a)
    algF Fail = return Nothing

--------------------------------
-- | Undeterminism
data Decide k = Decide (Bool -> k)
instance Functor Decide where
  fmap f (Decide k) = Decide (f . k)

handleD :: Functor sig => Free (Decide + sig) a -> Free sig a
handleD = fold genD (algD # fwd)
  where
    genD :: Monad m => a -> m a
    genD = return
    algD :: Monad m => Decide (m a) -> m a
    algD (Decide k) = k False

--------------------------------
-- | State s
data State s k = Get (s -> k) | Put s (() -> k)
instance Functor (State s) where
  fmap f (Get g) = Get (f . g)
  fmap f (Put s g) = Put s (f . g)

handleS :: Functor sig => Free (State s + sig) a -> (s -> Free sig a)
handleS = fold genS (algS # fwdPP)
  where
    genS :: Monad m => a -> (s -> m a)
    genS x = \s -> return x
    algS :: Monad m => State s (s -> m a) -> (s -> m a)
    algS (Get k) = \s -> k s s
    algS (Put s' k) = \s -> k () s'

-- examples of combining different effects
get :: Functor sig => Free (State s + sig) s
get = Op (Inl $ Get return)

put :: Functor sig => s -> Free (State s + sig) ()
put s = Op (Inl $ Put s return)

decide :: (Functor sig1, Functor sig2) => Free (sig1 + (Decide + sig2)) Bool
decide = Op (Inr . Inl $ Decide return)

-- the order of sig in the type determines the order to apply handlers
prog2 :: Free (State Int + (Decide + Void)) Int
prog2 = do
  s <- get
  b <- decide
  if b then put (s+1) else put (s+2)
  get

prog2' :: Free (State Int + (Decide + Void)) Int
prog2' =
  Op $ Inl $ Get $ \s ->
  Op $ (Inr . Inl) $ Decide $ \b ->
  (if b then (\k -> Op $ Inl $ Put (s+1) k) else (\k -> Op $ Inl $ Put (s+2) k)) $ \s ->
  Op $ Inl $ Get $ \s ->
  Return s

runProg :: Free (State Int + (Decide + Void)) a -> a
runProg = handleV . handleD . flip handleS 0

-- >>> runProg prog2
-- 2
-- >>> runProg prog2'
-- 2
