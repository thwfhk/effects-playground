{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE EmptyCase, EmptyDataDeriving #-}
{-# LANGUAGE StandaloneDeriving, UndecidableInstances #-}

module FreeMonad where

import Prelude hiding ((||), fail)
import Control.Monad (liftM, liftM2, ap)
import Data.Typeable

-- | Free Monad

data Prog sig a
  = Return a
  | Op (sig (Prog sig a))
deriving instance (Show (sig (Prog sig a)), Show a) => Show (Prog sig a)

-- printFM :: (Show a) => Prog sig a -> String
-- printFM (Return x) = "Return " ++ show x
-- printFM (Op x) = "Op(" + ")"

instance Functor sig => Functor (Prog sig) where
  fmap = liftM
  -- fmap f (Return v) = Return (f v)
  -- fmap f (Op op) = Op (fmap (fmap f) op)
  -- fmap f m1 = m1 >>= return . f

instance Functor sig => Applicative (Prog sig) where
  pure = return
  (<*>) = ap

instance Functor sig => Monad (Prog sig) where
  return v = Return v
  Return v >>= f = f v
  Op op    >>= f = Op (fmap (>>= f) op) -- the behavior of fmap is determined by sig

-- | A Standard Operation
data Operation p a x = Opt p (a -> Operation p a x)
instance Functor (Operation p a) where
  fmap f (Opt p k) = Opt p (fmap f . k)
----------------------------------------------------------------
-- | Datatypes a la Carte

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

instance (Functor sig1, Functor sig2) => sig1 < (sig1 + sig2) where
  inj         = Inl
  prj (Inl x) = Just x
  prj _       = Nothing

instance (Functor sig1, sig < sig2) => sig < (sig1 + sig2) where
  inj         = Inr . inj
  prj (Inr x) = prj x
  prj _       = Nothing

inject :: (sub < sup) => sub (Prog sup a) -> Prog sup a
inject = Op . inj

project :: (sub < sup) => Prog sup a -> Maybe (sub (Prog sup a))
project (Op x) = prj x
project _ = Nothing

----------------------------------------------------------------
-- | Nondeterminism
data Nondet a
  = Fail'
  | a :||? a
  deriving Show

instance Functor Nondet where
  fmap f Fail' = Fail'
  fmap f (x :||? y) = f x :||? f y

-- smart constructors (using inject)
fail :: (Nondet < sig) => Prog sig a
fail = inject Fail'

(||) :: (Nondet < sig) => Prog sig a -> Prog sig a -> Prog sig a
p || q = inject (p :||? q)

data Void a deriving Show
instance Functor Void where
  fmap f x = case x of

run :: Prog Void a -> a
run (Return x) = x

-- pattern synonyms for destructing (using project)
pattern Fail <- (project -> Just Fail')
pattern p :|| q <- (project -> Just (p :||? q))
pattern Other s = Op (Inr s)

sol :: Functor sig => Prog (Nondet + sig) a -> Prog sig [a]
sol (Return a) = return [a]
sol Fail = return []
sol (p :|| q) = liftM2 (++) (sol p) (sol q)
sol (Other op) = Op (fmap sol op)

allsols :: Prog (Nondet + Void) a -> [a]
allsols = run . sol

-- Example
knapsack :: (Nondet < sig) => Int -> [Int] -> Prog sig [Int]
knapsack w vs | w < 0  = fail
              | w == 0 = return []
              | w > 0  = do v <- select vs
                            vs' <- knapsack (w-v) vs
                            return (v:vs')
select :: (Nondet < sig) => [a] -> Prog sig a
select = foldr (||) fail . map Return

t :: Prog (Nondet + Void) Int
t = fail || Return 3 || Return 4

----------------------------------------------------------------
-- | State
data State s a
  = Get' (s -> a) -- state |-> continuation
  | Put' s a      -- state continuation
  deriving Show

instance (Typeable a, Typeable b) => Show (a -> b) where
  -- show _ = "<func>"
  show f = "<" ++ show (typeOf f) ++ ">"

instance Functor (State s) where
  fmap f (Get' g)   = Get' (f . g)
  fmap f (Put' s k) = Put' s (f k)

-- smart constructors
get :: (State s < sig) => Prog sig s
get = inject (Get' return)

put :: (State s < sig) => s -> Prog sig ()
put s = inject (Put' s (return ()))

-- destructors
pattern Get k <- (project -> Just (Get' k))
pattern Put s k <- (project -> Just (Put' s k))

runState :: Functor sig => s -> Prog (State s + sig) a -> Prog sig (s, a)
runState s (Return a) = return (s, a) -- return (state, result)
runState s (Get k) = runState s (k s) -- pass state s to continuation k and run k
runState s (Put s' k) = runState s' k -- totally change state and run continuation k
runState s (Other op) = Op (fmap (runState s) op) -- other operations are preserved

extractReturn :: Functor sig => Prog sig a -> a
extractReturn (Return x) = x
extractReturn _ = error "Not Return."

----------------------------------------------------------------
choices :: (Nondet < sig, State Int < sig) => Prog sig a -> Prog sig a
choices (Return a) = return a
choices Fail = fail
choices (p :|| q) = incr >> (choices p || choices q) -- NOTE: :(
choices (Op op) = Op (fmap choices op) -- No need to use Other.
incr :: (State Int < sig) => Prog sig ()
incr = get >>= put . (succ :: Int -> Int)

test1 = run . sol . runState (0::Int) . choices
test2 = run . runState (0::Int) . sol . choices
----------------------------------------------------------------
-- | Cutfail
data Cut a = Cutfail' deriving Show
instance Functor Cut where
  fmap f Cutfail' = Cutfail'
cutfail :: (Cut < sig) => Prog sig a
cutfail = inject Cutfail'
pattern Cutfail <- (project -> Just Cutfail')

cut :: (Nondet < sig, Cut < sig) => Prog sig ()
cut = skip || cutfail
skip :: Monad m => m ()
skip = return ()

-- once :: (Nondet < sig) => Prog (Cut + sig) a -> Prog sig a
test :: (Nondet < sig, Cut < sig) => Prog sig b -> Prog sig b
test p = do x <- p; cut; return x