{-# LANGUAGE StandaloneDeriving, UndecidableInstances, GADTs #-}
{-# LANGUAGE TypeOperators, EmptyCase, InstanceSigs, DeriveFunctor #-}

module Frank where

import Control.Monad (liftM, liftM2, ap)
import Prelude hiding (or, fail)

-- Free Monad
data Prog sig a = Return a | Op (sig (Prog sig a))
deriving instance (Show (sig (Prog sig a)), Show a) => Show (Prog sig a)

instance Functor sig => Functor (Prog sig) where
  fmap = liftM
instance Functor sig => Applicative (Prog sig) where
  pure  = return
  (<*>) = ap
instance Functor sig => Monad (Prog sig) where
  return x = Return x
  Return x >>= f = f x
  Op op    >>= f = Op (fmap (>>=f) op)

-- Composition
infixr +
data (sig1 + sig2) a = Inl (sig1 a) | Inr (sig2 a) deriving Show
instance (Functor sig1, Functor sig2) => Functor (sig1 + sig2) where
  fmap f (Inl x) = Inl (fmap f x)
  fmap f (Inr y) = Inr (fmap f y)

infixr #
(#) :: (sig1 b -> b) -> (sig2 b -> b) -> ((sig1 + sig2) b -> b)
(alg1 # alg2) (Inl op) = alg1 op
(alg1 # alg2) (Inr op) = alg2 op

-- Handler
fold :: Functor sig => (a -> b) -> (sig b -> b) -> (Prog sig a -> b)
fold gen alg (Return x) = gen x
fold gen alg (Op op)    = alg (fmap (fold gen alg) op)

-- Nil
data Nil a deriving Functor

run :: Prog Nil a -> a
run (Return x) = x

----------------------------------------------------------------
-- State

data State s k = Get (s -> k) | Put s (() -> k)
instance Functor (State s) where
  fmap f (Get g) = Get (f . g)
  fmap f (Put s g) = Put s (f . g)

hState :: Functor f => Prog (State s + f) a -> Prog f (s -> Prog f a)
hState = fold genS (algS # Op)
  where
    genS x = return $ \s -> return x
    algS (Get k) = return $ \s -> do f <- k s; f s
    algS (Put s' k) = return $ \s -> do f <- k (); f s'

get :: Functor f => Prog (f + State s) s
get = Op (Inr $ Get return)

put :: Functor f => s -> Prog (f + State s) ()
put s = Op (Inr $ Put s return)

insertNil :: Functor f => Prog f a -> Prog (f + Nil) a
insertNil (Return x) = Return x
insertNil (Op x) = Op . Inl $ fmap insertNil x

----------------------------------------------------------------
-- Frank-style scoped effects and handlers
----------------------------------------------------------------

data ND k where
  Fail :: ND k
  Or :: (Bool -> k) -> ND k 
  Once :: (Prog ND a) -> (a -> k) -> ND k

instance Functor ND where
  fmap k Fail = Fail
  fmap f (Or k) = Or (f . k)
  fmap f (Once x k) = Once x (f . k)

nd :: Prog ND a -> [a]
nd = fold return alg
  where
    alg Fail = []
    alg (Or k) = k True ++ k False
    alg (Once m k) = case (nd m) of [] -> [] -- genenral recursion
                                    (x:_) -> k x

or :: Prog ND a -> Prog ND a -> Prog ND a
or x y = Op $ Or (\b -> if b then x else y)

once :: Prog ND a -> (a -> Prog ND k) -> Prog ND k
once x y = Op $ Once x y

example :: Prog ND Int
example = once (or (return 1) (return 5)) (\x -> or (return x) (return (x+1)))

-- >>> nd example
-- [1,2]

----------------------------------------------------------------

data ND2 k where
  Fail2 :: ND2 k
  Or2 :: (Bool -> k) -> ND2 k 
  Once2 :: (Prog (ND2 + State String) a) -> (a -> k) -> ND2 k
  -- Once2 :: Functor f => (Prog (ND2 + f) a) -> (a -> k) -> ND2 k

instance Functor ND2 where
  fmap k Fail2 = Fail2
  fmap f (Or2 k) = Or2 (f . k)
  fmap f (Once2 x k) = Once2 x (f . k)

-- nd2 :: Functor f => Prog (ND2 + f) a -> Prog f [a]
nd2 :: Prog (ND2 + State String) a -> Prog (State String) [a]
nd2 = fold gen (alg # Op)
  where
    gen = return . return
    -- alg :: Functor f => ND2 (Prog f [a]) -> Prog f [a]
    alg Fail2 = return []
    alg (Or2 k) = do x <- k True; y <- k False; return (x ++ y)
    alg (Once2 m k) = do x <- nd2 m                -- general recursion
                         case x of [] -> return []
                                   (x:_) -> k x

or2 :: Functor f => Prog (ND2 + f) a -> Prog (ND2 + f) a -> Prog (ND2 + f) a
or2 x y = Op . Inl $ Or2 (\b -> if b then x else y)

once2 :: Prog (ND2 + State String) a -> (a -> Prog (ND2 + State String) k) -> Prog (ND2 + State String) k
once2 x y = Op . Inl $ Once2 x y

example2 :: Prog (ND2 + State String) String
example2 = once2 (or2 (do put "4"; get) (return "2")) (\x -> return x)

-- >>> run $ (run . hState . insertNil . nd2 $ example2) ""
-- ["4"]

-- nd2 is correct
-- forwarding of scoped effects is not needed here

----------------------------------------------------------------

data ND3 k where
  Fail3 :: ND3 k
  Or3 :: (Bool -> k) -> ND3 k
  Once3 :: (Prog (State String + ND3) a) -> (a -> k) -> ND3 k

instance Functor ND3 where
  fmap k Fail3 = Fail3
  fmap f (Or3 k) = Or3 (f . k)
  fmap f (Once3 x k) = Once3 x (f . k)

nd3 :: Functor f => Prog (ND3 + f) a -> Prog f [a]
-- nd3 :: Prog (State String + ND3) a -> Prog (State String) [a]
nd3 = fold gen (alg # Op)
  where
    gen = return . return
    alg :: Functor f => ND3 (Prog f [a]) -> Prog f [a]
    alg Fail3 = return []
    alg (Or3 k) = do x <- k True; y <- k False; return (x ++ y)
    alg (Once3 m k) = do x <- nd3 m                -- general recursion
                         case x of [] -> return []
                                   (x:_) -> k x

-- nd3 is not well-typed
-- For the scoped computation in Once3, it is impossible to handle (State String) before handling ND3. 
-- Because the previous handlers will ignore the computation in the parameter position.