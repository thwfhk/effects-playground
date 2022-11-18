{-# LANGUAGE StandaloneDeriving, UndecidableInstances, DeriveFunctor #-}
{-# LANGUAGE TypeOperators, EmptyCase, InstanceSigs #-}

module NewState where

import Control.Monad (liftM, liftM2, ap)
import Prelude hiding (or, fail)

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
infixr +
data (sig1 + sig2) a = Inl (sig1 a) | Inr (sig2 a) deriving Show
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
-- data Void k
data Void k = Void deriving Show
instance Functor Void where
  fmap f x = case x of

-- Void is usually used as the leftmost
run :: Free Void a -> a
run (Return x) = x

--------------------------------
-- | Nondeterminism
data Nondet k = Fail | Or (Bool -> k) deriving Functor

hNondet :: Functor sig => Free (Nondet + sig) a -> Free sig [a]
hNondet = fold genD (algD # fwd)
  where
    genD :: Monad m => a -> m [a]
    genD = return . return
    algD :: Monad m => Nondet (m [a]) -> m [a]
    algD (Or k) = do x <- k True; y <- k False; return (x ++ y)


--------------------------------
-- | State s
data State s k = Get (s -> k) | Put s (() -> k)
instance Functor (State s) where
  fmap f (Get g) = Get (f . g)
  fmap f (Put s g) = Put s (f . g)

hState :: Functor sig => Free (State s + sig) a -> Free sig (s -> Free sig a)
hState = fold genS (algS # fwd)
  where
    genS :: Monad m => a -> m (s -> m a)
    genS x = return $ \s -> return x
    algS :: Monad m => State s (m (s -> m a)) -> m (s -> m a)
    algS (Get k) = return $ \s -> do f <- k s; f s
    algS (Put s' k) = return $ \s -> do f <- k (); f s'

-- examples of combining different effects
get :: Functor sig => Free (State s + sig) s
get = Op (Inl $ Get return)

put :: Functor sig => s -> Free (State s + sig) ()
put s = Op (Inl $ Put s return)

decide :: (Functor sig1, Functor sig2) => Free (sig1 + (Nondet + sig2)) Bool
-- or x y = (Op . Inr . Inl . Or) (\ b -> if b then x else y)
decide = (Op . Inr . Inl . Or) return

prog :: Free (State Int + Nondet + Void) Int
prog = do
  x <- do b <- decide; if b then return 5 else return 10
  t <- get
  return (t + x)

tmp :: Free (Nondet + Void) (Int -> Free (Nondet + Void) Int)
tmp = hState prog

t = (run . hNondet) $ do f <- hState prog; f 0
-- >>> t
-- [5,10]

varbind :: Functor f => Int -> Free f (s -> Free f Int)
varbind = \s -> hState (Return s)

x = run $ run (varbind 1) 0
-- >>> x
-- 1
