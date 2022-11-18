{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeOperators, FlexibleContexts, UndecidableInstances #-}

module Functorial.Union where

infixr 4 :+:
data (sig1 :+: sig2) a = Inl (sig1 a) | Inr (sig2 a)

instance (Functor sig1, Functor sig2) => Functor (sig1 :+: sig2) where
  fmap f (Inl t) = Inl (fmap f t)
  fmap f (Inr t) = Inr (fmap f t)


class In sub sup where
  inj :: sub a -> sup a

instance In sub sub where
  inj = id

instance {-# OVERLAPPABLE #-} In s (s1 :+: (s2 :+: s3)) => In s ((s1 :+: s2) :+: s3) where
  inj = assoc . inj where
    assoc :: (s1 :+: (s2 :+: s3)) a -> ((s1 :+: s2) :+: s3) a
    assoc (Inl x) = Inl (Inl x)
    assoc (Inr (Inl x)) = Inl (Inr x)
    assoc (Inr (Inr x)) = Inr x

instance {-# OVERLAPPABLE #-} In sig1 (sig1 :+: sig2) where
  inj = Inl

instance {-# OVERLAPPABLE #-} In sig sig2 => In sig (sig1 :+: sig2) where
  inj = Inr . inj
