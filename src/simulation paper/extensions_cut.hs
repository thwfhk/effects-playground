{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

import Background

import Control.Monad (ap, join, liftM, when)
import Control.Monad.Trans (lift)
import Data.Either (isLeft)
import Prelude hiding (fail)
import Debug.Trace

data Idem a = Ret a | Flag a 
  deriving Show
unIdem :: Idem a -> a
unIdem (Ret   x)  = x
unIdem (Flag  x)  = x

newtype CutList a = CutList { unCutList :: Idem [a] }
  deriving Show
distr :: [Idem a] -> Idem [a]
distr (Ret   x  : xs)   = fmap ((:) x) (distr xs)
distr (Flag  x  : xs)   = Flag [x]
distr []                = Ret []
instance Functor Idem where
  fmap f (Ret a)   = Ret (f a)
  fmap f (Flag a)  = Flag (f a)
instance Applicative Idem where
  pure = return
  (<*>) = ap
instance Monad Idem where
  return a = Ret a
  Ret a >>= f   = f a
  Flag a >>= f  = Flag (unIdem (f a))

instance Functor CutList where
  fmap f x = CutList $ fmap (fmap f) (unCutList x)
instance Applicative CutList where
  pure = return
  (<*>) = ap
instance Monad CutList where
  return a = CutList $ return (return a)
  m >>= f = CutList $ fmap join (join (fmap distr (fmap (fmap (unCutList . f)) (unCutList m))))
instance Foldable CutList where
  foldMap f x = foldMap f (unIdem $ unCutList x)
instance Traversable CutList where
  traverse f (CutList (Ret xs)) = fmap (CutList . Ret) $ traverse f xs
  traverse f (CutList (Flag xs)) = fmap (CutList . Flag) $ traverse f xs

cut      :: CutList ()
cut      = CutList $ Flag [()]

fail     :: CutList a
fail     = CutList $ Ret []

cutList  :: [a] -> CutList a
cutList  = CutList . Ret

scope    :: CutList a -> CutList a
scope    = cutList . unIdem . unCutList

append   :: CutList a -> CutList a -> CutList a
append   (CutList (Ret xs))   ys  = CutList $ fmap ((++) xs) $ unCutList ys
append   (CutList (Flag xs))  _   = CutList (Flag xs)

data CutF    a  = Cut
data ScopeF  a  = Scope a
instance Functor CutF where
  fmap f Cut = Cut

instance Functor ScopeF where
  fmap f (Scope x) = Scope (f x)

data FreeS f g a  =  Return a
                  |  Call (f (FreeS f g a))
                  |  Enter (g (FreeS f g (FreeS f g a)))
instance (Functor f, Functor g) => Functor (FreeS f g) where
  fmap = liftM

instance (Functor f, Functor g) => Applicative (FreeS f g) where
  pure   = return
  (<*>)  = ap

instance (Functor f, Functor g) => Monad (FreeS f g) where
  return = Return
  (>>=) (Return x)  f = f x 
  (>>=) (Call op)   f = Call (fmap (>>= f) op) 
  (>>=) (Enter op)  f = Enter (fmap (fmap (>>= f)) op)
data Alg f g a = Alg  { call   :: f a -> a
                      , enter  :: g (FreeS f g a) -> a }

foldS :: (Functor f, Functor g) => (a -> b) -> Alg f g b -> FreeS f g a -> b
foldS gen alg (Return  x)   = gen x
foldS gen alg (Call    op)  = (call   alg  . fmap (foldS gen alg))         op
foldS gen alg (Enter   op)  = (enter  alg  . fmap (fmap (foldS gen alg)))  op

type NondetF' = NondetF :+: CutF

hCut  :: (Functor f, Functor g)
      => FreeS (NondetF' :+: f) (ScopeF :+: g) a
      -> FreeS f g (CutList a)
hCut = foldS gen (Alg (algNDCut # Call) (algSC # fwdSC))
  where
    gen                      = return . return
    algNDCut (Inl Fail)      = return fail
    algNDCut (Inl (Or x y))  = append <$> x <*> y
    algNDCut (Inr Cut)       = return (cut >> fail)
    algSC    (Scope k)       = (join . fmap (fmap join . sequenceA . scope) . hCut) k
    fwdSC                    = Enter . fmap (fmap (fmap join . sequenceA) . hCut)

run :: FreeS NilF NilF a -> a
run (Return x) = x

fail'     = (Call . Inl . Inl) Fail
or' x y   = (Call . Inl . Inl) $ Or x y
cut'      = (Call . Inl . Inr) Cut
scope' x  = (Enter . Inl) $ Scope x

takeWhileS :: (Functor f, Functor g) => (a -> Bool) -> FreeS (NondetF' :+: f) (ScopeF :+: g) a -> FreeS (NondetF' :+: f) (ScopeF :+: g) a
takeWhileS p prog = scope'
  (do x <- prog; when (not (p x)) cut'; return $ return x)

prog1 :: (Functor f, Functor g) => FreeS (NondetF' :+: f) (ScopeF :+: g) Int
prog1 = or' (or' (return 2) (return 4)) (or' (return 5) (return 8))

prog2 :: (Functor f, Functor g) => FreeS (NondetF' :+: f) (ScopeF :+: g) Int
prog2 = or' (or' (return 6) (return 9)) (return 10)

prefixes' :: (Functor f, Functor g) => FreeS (NondetF' :+: f) (ScopeF :+: g) Int
prefixes' = or' (takeWhileS even prog1) (takeWhileS even prog2)

-- > (run . hCut) (takeWhileS even prog1)
-- CutList {unCutList = Flag [2,4]}

-- > (run . hCut) prefixes'
-- CutList {unCutList = Ret [2,4,6]}

prog :: (Functor f, Functor g) => FreeS (NondetF' :+: f) (ScopeF :+: g) Int
prog = or' (scope' (or' (return $ return 2) (return $ return 4))) (return 6)

-- \wenhao{Shoule we also change it to a syntax-level simulation?}

-- \wenhao{Shoule we combine this extension with other effects?}

newtype STCut a = STCut {runSTCut :: State (CutList a, [STCut a]) ()}

type V a = FreeS NilF NilF a

simulate :: FreeS (NondetF' :+: NilF) (ScopeF :+: NilF) a -> V (STCut a)
simulate = foldS genCut (Alg (algNDCut # undefined) (algSCCut # undefined)) where
  genCut :: a -> V (STCut a)
  genCut x                 = return $ appendCut x popCut
  algNDCut :: (NondetF :+: CutF) (V (STCut a)) -> V (STCut a)
  algNDCut (Inl Fail)      = return $ popCut
  algNDCut (Inl (Or p q))  = return $ pushCut (run q) (run p)
  algNDCut (Inr Cut)       = return $ undoCut
  algSCCut :: ScopeF (FreeS (NondetF' :+: NilF) (ScopeF :+: NilF) (V (STCut a))) -> V (STCut a)
  algSCCut (Scope k)       = return $ joinSTCut (run (simulate (fmap run k)))

joinSTCut :: STCut (STCut a) -> STCut a
joinSTCut x = STCut $ State $ \ (cl, stack) -> let t = scope $ fmap extractCut (extractCut x) in 
  case stack of
    [] -> ((), (append cl (join t), []))
    STCut p : ps -> runState p (append cl (join t), ps)

extractCut :: STCut a -> CutList a
extractCut x = fst $ snd $ runState (runSTCut x) (fail, [])

popCut :: STCut a
popCut = STCut $ do
  (xs, stack) <- get
  case stack of
    [] -> return ()
    STCut p : ps -> do put (xs, ps); p

appendCut :: a -> STCut a -> STCut a
appendCut x p = STCut $ do
  (xs, stack) <- get
  put (append xs (return x), stack)
  runSTCut p

pushCut :: STCut a -> STCut a -> STCut a
pushCut q p = STCut $ do
  (xs, stack) <- get
  put (xs, q : stack)
  runSTCut p

undoCut :: STCut a
undoCut = STCut $ do
  (xs, stack) <- get
  put (append xs (cut >> fail), stack)