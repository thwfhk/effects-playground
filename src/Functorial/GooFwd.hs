{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeOperators, FlexibleContexts, UndecidableInstances #-}

import Control.Monad (join, ap)

infixr 4 :+:
data (sig1 :+: sig2) a = Inl (sig1 a) | Inr (sig2 a)
instance (Functor sig1, Functor sig2) => Functor (sig1 :+: sig2) where
  fmap f (Inl t) = Inl (fmap f t)
  fmap f (Inr t) = Inr (fmap f t)


data Prog f g a
  = Return a
  | Call (f (Prog f g a))
  | Enter (g (Prog f g (Prog f g a)))

instance (Functor f , Functor g) => Functor (Prog f g) where 
    fmap f (Return x) = Return (f x)
    fmap f (Call t)   = Call (fmap (fmap f ) t)
    fmap f (Enter t)  = Enter (fmap (fmap (fmap f )) t)

instance (Functor f , Functor g) => Applicative (Prog f g) where 
    pure  = return
    (<*>) = ap

instance (Functor f, Functor g) => Monad (Prog f g) where
    return = Return
    Return x >>= f = f x
    Call op  >>= f = Call (fmap (>>= f) op)
    Enter sc >>= f = Enter (fmap (fmap (>>= f)) sc)

----------------------------------------------------------------

-- Consider a special case of MCarrier: c m' x = m' (m x)
-- handler
h :: (Functor f, Functor g, Functor f', Functor g')
  => Prog (f' :+: f) (g' :+: g) a -> Prog f g (m a)
h = undefined
-- simplified liftC of the MCarrier
liftC :: (Functor f, Functor g) => Prog f g a -> Prog f g (m a)
liftC = undefined
-- lift clause (from the calculus) used by the handler
lift :: (Functor f, Functor g) => m (Prog f g (m a)) -> Prog f g (m a)
lift = undefined
-- fwd clause (from the calculus) used by the handler
fwd :: (Functor f, Functor g)
    => g (Prog f g (m (Prog f g (m a)))) -> Prog f g (m a)
fwd k = Enter $ fmap (fmap lift) k

-- liftC is a algebra homomorphism: lhs == rhs
lhs :: (Functor f, Functor g) => g (Prog f g (Prog f g a)) -> Prog f g (m a)
lhs = liftC . Enter

rhs :: (Functor f, Functor g) => g (Prog f g (Prog f g a)) -> Prog f g (m a)
rhs = fwd . fmap liftC . fmap (fmap liftC)

-- commutativity of removing and handling: lhs' == rhs'
lhs' :: (Functor f, Functor g, Functor f', Functor g')
     => g (Prog (f' :+: f) (g' :+: g) (Prog (f' :+: f) (g' :+: g) a))
     -> g (Prog f g (m a))
lhs' = \ c -> fmap h (fmap join c)

rhs' :: (Functor f, Functor g, Functor f', Functor g')
     => g (Prog (f' :+: f) (g' :+: g) (Prog (f' :+: f) (g' :+: g) a))
     -> g (Prog f g (m a))
rhs' = \ c -> let c' = fmap h . fmap (fmap h) $ c
              in fmap join (fmap (fmap lift) c')
