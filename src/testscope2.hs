{-# LANGUAGE StandaloneDeriving, UndecidableInstances, DeriveFunctor,
    RankNTypes, TypeOperators, GADTs, DataKinds, KindSignatures #-}

import Control.Monad (liftM, liftM2, ap)
import Prelude hiding (or, fail)

data Prog f g a = Return a
                | Call (f (Prog f g a))
                | Enter (g (Prog f g (Prog f g a)))
-- deriving instance (Show (g (Prog f g (Prog f g a))), Show (f (Prog f g a)), Show a) => Show (Prog f g a)

instance (Functor f, Functor g) => Functor (Prog f g) where
  fmap = liftM
instance (Functor f, Functor g) => Applicative (Prog f g) where
  pure = return
  (<*>) = ap
instance (Functor f, Functor g) => Monad (Prog f g) where
  return = Return
  Return x >>= f = f x
  Call op  >>= f = Call (fmap (>>=f) op)
  Enter sc >>= f = Enter (fmap (fmap (>>=f)) sc)

-- Handler

data BaseAlg f g c d = BaseAlg 
  { callB  :: f d -> d
  , enterB :: g (c d) -> d
  }

data EndoAlg f g c = EndoAlg
  { returnE :: forall x. x -> c x
  , callE   :: forall x. f (c x) -> c x
  , enterE  :: forall x. g (c (c x)) -> c x
  }

hcata :: (Functor f, Functor g) => EndoAlg f g c -> Prog f g a -> c a
hcata alg (Return x) = returnE alg x
hcata alg (Call op)  = (callE alg . fmap (hcata alg)) op
hcata alg (Enter sc) = (enterE alg . fmap (hcata alg . fmap (hcata alg))) sc

eval :: (Functor f, Functor g) => EndoAlg f g c -> BaseAlg f g c b -> (a -> b) -> Prog f g a -> b
eval ealg balg gen (Return x) = gen x
eval ealg balg gen (Call op)  = (callB balg . fmap (eval ealg balg gen)) op
eval ealg balg gen (Enter sc) = (enterB balg . fmap (hcata ealg . fmap (eval ealg balg gen))) sc

data Nat = Zero | Succ Nat
data Nested f a :: Nat -> * where
  NestZ :: a -> Nested f a Zero
  NestS :: f (Nested f a n) -> Nested f a (Succ n)

unNestZ :: Nested f a Zero -> a
unNestZ (NestZ x) = x
unNestS :: Nested f a (Succ n) -> f (Nested f a n)
unNestS (NestS x) = x

data BaseAlg' f g c d = BaseAlg'
  { callB'  :: f d -> d
  , enterB' :: forall n. g (Nested c d (Succ n)) -> Nested c d n
  }

-- data EndoAlg' f g c d = EndoAlg'
--   { returnE' :: forall n. Nested c d n -> Nested c d (Succ n)
--   , callE'   :: forall n. f (Nested c d (Succ n)) -> Nested c d (Succ n)
--   , enterE'  :: forall n. g (Nested c d (Succ (Succ n))) -> Nested c d (Succ n)
  -- }
data EndoAlg' f g c d = EndoAlg'
  { returnE' :: forall x. x -> c x
  , callE'   :: forall n. f (Nested c d (Succ n)) -> Nested c d (Succ n)
  , enterE'  :: forall x. g (c (c x)) -> c x
  -- , callE0   :: forall n. f (Nested c d Zero) -> Nested c d Zero
  }

hcata' :: (Functor f, Functor g, Functor c) => EndoAlg' f g c a -> Prog f g (Nested c a n) -> Nested c a (Succ n)
hcata' alg (Return x) = NestS (returnE' alg x)
hcata' alg (Call op)  = (callE' alg . fmap (hcata' alg)) op
hcata' alg (Enter sc) = NestS $ (enterE' alg . fmap (fmap unNestS . unNestS . hcata' alg . fmap (hcata' alg))) sc

eval' :: (Functor f, Functor g, Functor c) => EndoAlg' f g c b -> BaseAlg f g c b -> (a -> b) -> Prog f g a -> b
eval' ealg balg gen (Return x) = gen x
eval' ealg balg gen (Call op)  = (callB balg . fmap (eval' ealg balg gen)) op
eval' ealg balg gen (Enter sc) = (enterB balg . fmap qwq) sc
  where
    qwq x = let NestS y = (hcata' ealg . fmap (NestZ . eval' ealg balg gen)) x in
            fmap unNestZ y

-- Combine two operations

data (sig1 + sig2) a = Inl (sig1 a) | Inr (sig2 a)
instance (Functor sig1, Functor sig2) => Functor (sig1 + sig2) where
  fmap f (Inl x) = Inl (fmap f x)
  fmap f (Inr y) = Inr (fmap f y)

(#) :: (sig1 b -> b) -> (sig2 b -> b) -> ((sig1 + sig2) b -> b)
(alg1 # alg2) (Inl op) = alg1 op
(alg1 # alg2) (Inr op) = alg2 op

---------------------------------------------------------------
data Void a = Void deriving (Functor, Show)

runVoid :: Prog Void Void a -> a
runVoid (Return x) = x

---------------------------------------------------------------
-- Example 1

data Choice a = Fail | Or a a deriving (Functor, Show)
data Once a = Once a deriving (Functor, Show)

-- handler
-- allsols :: Prog (Choice + Void) (Once + Void) a -> Prog Void Void [a]
-- allsols = eval undefined (BaseAlg (call # Call) enter) undefined
--   where
--     call Fail = return []
--     call (Or pxs pys) = do xs <- pxs; ys <- pys; return (xs ++ ys)
--     enter = undefined
--     calle Fail = []
--     calle (Or xs ys) = xs ++ ys
--     entere (Once (xs : xss)) = xs

allsols :: Prog Choice Once a -> [a]
allsols = eval (EndoAlg return call enter) (BaseAlg call enter) return
  where
    call Fail = []
    call (Or xs ys) = xs ++ ys
    enter (Once []) = []
    enter (Once (xs : xss)) = xs

-- smart constructors
fail :: Functor g => Prog Choice g a
fail = Call Fail
or :: Functor g => Prog Choice g a -> Prog Choice g a -> Prog Choice g a
or x y = Call (Or x y)
once :: Functor f => Prog f Once a -> Prog f Once a
once x = Enter (Once (fmap return x))

---------------------------------------------------------------
-- Example 3: combine scoped operations with algebraic operations

data Add a = Add a a deriving (Functor, Show)

add :: Functor g => Prog Add g a -> Prog Add g a -> Prog Add g a
add x y = Call (Add x y)

addnum :: (Functor f, Functor g, Num a) => Prog (Add + f) g a -> Prog f g a
addnum = eval' ealg (BaseAlg (callb # Call) Enter) return
  where
    callb :: (Num a, Functor f, Functor g) => Add (Prog f g a) -> Prog f g a
    callb (Add px py) = do x <- px; y <- py; return (x+y)
    ealg :: Functor f => EndoAlg' (Add + f) g (Prog f g) a
    ealg = EndoAlg' Return calle Enter
      where
        calle :: Functor f => (Add + f) (Nested (Prog f g) a (Succ n)) -> (Nested (Prog f g) a (Succ n))
        calle = undefined # (NestS . Call . fmap unNestS)