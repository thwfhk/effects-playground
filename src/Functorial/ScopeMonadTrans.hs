{-# LANGUAGE TypeOperators, RankNTypes, GADTs, KindSignatures, RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables, QuantifiedConstraints, MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies, FlexibleInstances, ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor, InstanceSigs, UndecidableInstances, FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}

import Control.Monad.Trans
import Control.Monad


-- Models of Algebraic Operations
---------------------------------------------

-- |aSig :: * -> *| is an endofunctor encoding the signature
-- of operations.

-- A (simple) model/algebra of a functor |aSig|
class SimpleModel aSig a | a -> aSig where
  alg :: aSig a -> a


-- A monad model of a signature
class Monad t => Model aSig (t :: (* -> *)) | t -> aSig where
  alg' :: aSig x -> t x

-- Simple models and 'monad models' are 'equivalent' for interpretation.
--   a |-> Cont a
-- and
--   t |-> t x   (for any x)


-- Modular Models of Algebraic Operations
---------------------------------------------

-- A problem is that we can't easily combine models of different signatures:
-- given |aSig a -> a| and  |bSig b -> b|
-- we don't have an obvious model for |aSig + bSig|.
--
-- The problem is addressed in the following two papers.

-- Schrijvers, T., Piróg, M., Wu, N., & Jaskelioff, M. (2019).
-- Monad transformers and modular algebraic effects:What binds them together.
-- Haskell 2019 

-- Zhixuan Yang and Nicolas Wu. (2021).
-- Reasoning about effect interaction by fusion. 
-- ICFP 2019


class SimpleModModel aSig (a :: (* -> *) -> *) | a -> aSig where
  -- New operations can be handled
  algSMM :: Monad m => aSig (a m) -> a m
  
  -- And existing effects |m| can be 'subsumed' by the modular model |a m|
  fwdSMM :: Monad m => m (a m) -> a m

  -- Consequently any algebraic operations on |m| can be lifted to |a m|
  -- in a canonical way.
  liftOpSMM :: (Functor f, Monad m)
            => (forall x . f (m x) -> m x) 
            -> f (a m) -> a m
  liftOpSMM alg = fwdSMM . alg . fmap return
  -- And it can be shown that |fwdSMM| from |MonadTrans| is an algebra homomorphism
  -- from |alg| to |liftOpSMM alg|.


class (MonadTrans t, forall m . Monad m => Monad (t m))
      => ModModel aSig (t :: (* -> *) -> (* -> *)) | t -> aSig where

  algMM :: Monad m => aSig (t m x) -> t m x

  -- It can be shown that |lift| from |MonadTrans| is an algebra homomorphism
  -- from |alg| to |liftOpMM alg|.
  liftOpMM :: (Functor f, Monad m)
            => (forall x . f (m x) -> m x) 
            -> (forall x . f (t m x) -> t m x)
  liftOpMM alg = join . lift .  alg . fmap return 


-- Modular Models of Scoped Operations
---------------------------------------------

data Alg f g c = Alg 
  { call  :: forall x . f (c x) -> c x
  , enter :: forall x . g (c (c x)) -> c x
  }

class MonadTrans t => ModModelSc aSig sSig t | t -> aSig sSig where
  algMMS :: Monad m => Alg aSig sSig (t m)

  liftOpMMS :: Monad m => Alg f g m -> Alg f g (t m)
  -- Law: |lift| from |MonadTrans| shall be an algebra homomorphism
  -- from |alg| to |liftOpMMS alg|.

  -- Note: we no longer have a default implementation for liftOp!


class SimpleModModelSc aSig sSig (a :: (* -> *) -> (* -> *)) | a -> aSig sSig where
  algSMMS :: Monad m => Alg aSig sSig (a m)

  liftOpSMMS :: Monad m => Alg f g m -> Alg f g (a m)

  fwdSMMS :: Monad m => m (a m x) -> a m x
  -- Law : |fwdSMMS| and |liftOpSMMS| should make this diagram to commute (so
  --   that a simple model still corresponds to a monad model).
  --
  --                      alg . a m
  --       S m  .  a m  ---------------->  m . a m
  --           |                            |
  --           |  Θ                         |
  --           ∨                            |
  --       S (m . a m)                      |  fwd
  --           |                            |
  --           |  S fwd                     |
  --           ∨                            ∨
  --        S (a m)  ------------------->  a m
  --                     liftOpSMMS alg
  --
  --  where (.) means functor composition,  S = f . - + g . - . -,
  --    and Θ is the evident pointed strength for S.

