{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE EmptyCase, EmptyDataDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}

-- Implementation of Algebraic Effects using Free Monad and Datatype a la Carte
-- From the paper: “Effect Handlers in Scope.”

module AlgebraicEffects where

import Prelude hiding ((||), fail)
import Control.Monad (liftM, liftM2, ap)
import Data.Typeable

-- | Free Monad
data Free sig a = Return a | Op (sig (Free sig a))
deriving instance (Show (sig (Free sig a)), Show a) => Show (Free sig a)

instance Functor sig => Functor (Free sig) where
  fmap = liftM
instance Functor sig => Applicative (Free sig) where
  pure = return
  (<*>) = ap
instance Functor sig => Monad (Free sig) where
  return v = Return v
  Return v >>= f = f v
  Op op    >>= f = Op (fmap (>>= f) op)

-- | The Standard Operation
data Operation p r x = Opt p (r -> x)
instance Functor (Operation p r) where
  fmap f (Opt p k) = Opt p (f . k)

----------------------------------------------------------------
-- | Datatypes a la Carte
-- One advantage of using Datatypes a la Carte is that your constructors are
-- "smarter", which means you don't need to care about the order of effects
-- when writing programs (but you still need to consider it when handling).

-- The "project" is used to extract the top constructor.
-- If every handler is handling the leftmost signature, there is no need
-- to use it as we can use an operation (#) to combine two algebras.

infixr +
data (sig1 + sig2) a = Inl (sig1 a) | Inr (sig2 a) deriving Show

instance (Functor sig1, Functor sig2) => Functor (sig1 + sig2) where
  fmap f (Inl x) = Inl (fmap f x)
  fmap f (Inr y) = Inr (fmap f y)

class (Functor sub, Functor sup) => sub < sup where
  inj :: sub a -> sup a
  prj :: sup a -> Maybe (sub a)

instance Functor sig => sig < sig where
  inj = id
  prj = Just

instance {-# OVERLAPS #-} (Functor sig1, Functor sig2) => sig1 < (sig1 + sig2) where
  inj         = Inl
  prj (Inl x) = Just x
  prj _       = Nothing

instance {-# OVERLAPS #-} (Functor sig1, sig < sig2) => sig < (sig1 + sig2) where
  inj         = Inr . inj
  prj (Inr x) = prj x
  prj _       = Nothing

inject :: (sub < sup) => sub (Free sup a) -> Free sup a
inject = Op . inj

project :: (sub < sup) => Free sup a -> Maybe (sub (Free sup a))
project (Op x) = prj x
project _ = Nothing

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

-------------------------------
-- | Void
data Void k deriving Show
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

-- pattern Fail' <- (project -> Just Fail)
fail :: (Fail < sig) => Free sig a
fail = inject Fail

handleF :: Functor sig => Free (Fail + sig) a -> Free sig (Maybe a)
handleF = fold genF (algF # fwd)
  where
    genF x = return (Just x)
    algF Fail = return Nothing

-- do nothing is ok as long as you guarantee the type signature is correct
candyF :: Fail < sig => Free (Fail + sig) a -> Free sig a
candyF = fold gen (alg # fwd)
  where
    gen = return
    alg Fail = fail

--------------------------------
-- | Non-determinism
data Nondet k = End | k :|: k
instance Functor Nondet where
  fmap f End = End
  fmap f (k1 :|: k2) = f k1 :|: f k2

end :: (Nondet < sig) => Free sig a
end = inject End
(|>) :: (Nondet < sig) => Free sig a -> Free sig a -> Free sig a
p |> q = inject (p :|: q)

handleN :: Functor sig => Free (Nondet + sig) a -> Free sig [a]
handleN = fold genN (algN # fwd)
  where
    genN x = return [x]
    algN End = return []
    algN (p1 :|: p2) = liftM2 (++) p1 p2

--------------------------------
-- | Cut
data Cut k = Cutfail
instance Functor Cut where
  fmap f Cutfail = Cutfail

cutfail :: (Cut < sig) => Free sig a
cutfail = inject Cutfail

-- The handler call is not a T-homomorphism.

--------------------------------
-- | Randomness
data Decide k = Decide (Bool -> k)
instance Functor Decide where
  fmap f (Decide k) = Decide (f . k)

decide :: (Decide < sig) => Free sig Bool
decide = inject $ Decide return

handleD :: Functor sig => Free (Decide + sig) a -> Free sig a
handleD = fold genD (algD # fwd)
  where
    genD :: Monad m => a -> m a
    genD = return
    algD :: Monad m => Decide (m a) -> m a
    algD (Decide k) = k False

handleDMax :: (Functor sig, Ord a) => Free (Decide + sig) a -> Free sig a
handleDMax = fold genD (algD # fwd)
  where
    genD = return
    algD (Decide k) = liftM2 max (k True) (k False)

--------------------------------
-- | State s
data State s k = Get (s -> k) | Put s (() -> k)
instance Functor (State s) where
  fmap f (Get g) = Get (f . g)
  fmap f (Put s g) = Put s (f . g)

get :: (State s < sig) => Free sig s
get = inject $ Get return

put :: (State s < sig) => s -> Free sig ()
put s = inject $ Put s return

handleS :: Functor sig => Free (State s + sig) a -> (s -> Free sig (s, a))
handleS = fold genS (algS # fwdPP)
  where
    genS x = \s -> return (s, x)
    algS (Get k) = \s -> k s s
    algS (Put s' k) = \s -> k () s'

-- another way to implement handleS
-- handleS' :: Functor sig => s -> Free (State s + sig) a -> Free sig (s, a)
-- handleS' s (Return x) = return (s, x)
-- handleS' s (Op (Inl (Get k))) = handleS' s (k s)
-- handleS' s (Op (Inl (Put s' k))) = handleS' s' (k ())
-- handleS' s (Op (Inr op)) = fwd (fmap (handleS' s) op)

runLocal :: Functor sig => s -> Free (State s + (Fail + sig)) a -> Free sig (Maybe (s, a))
runLocal s = handleF . flip handleS s

runGlobal :: Functor sig => s -> Free (Fail + (State s + sig)) a -> Free sig (s, Maybe a)
runGlobal s = flip handleS s . handleF

prog :: (State Integer < sig, Fail < sig) => Free sig Integer
prog = do
  s <- get
  if s == 0 then fail else put (s+1)
  return (s+1)

-- different orders lead to different results
-- >>> handleV $ runLocal (0::Integer) prog
-- Nothing
-- >>> handleV $ runGlobal (0::Integer) prog
-- (0,Nothing)
-- >>> handleV $ runLocal (1::Integer) prog
-- Just (2,2)
-- >>> handleV $ runGlobal (1::Integer) prog
-- (2,Just 2)
