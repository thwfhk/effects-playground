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


---------------------------------------------------------------
-- Example : Choice & Once

data Choice a = Fail | Or a a deriving (Functor, Show)
data Once a = Once a deriving (Functor, Show)

-- handler
allsols :: Prog Choice Once a -> [a]
allsols = eval (EndoAlg return call enter) (BaseAlg call enter) return
  where
    call Fail = []
    call (Or xs ys) = xs ++ ys
    enter (Once []) = []
    enter (Once (xs : xss)) = xs
    -- enter (Once (xs : xss)) = head xss -- twice

-- failed attemp
-- allsols :: Prog (Choice + Void) (Once + Void) a -> Prog Void Void [a]
-- allsols = eval undefined (BaseAlg (call # Call) enter) undefined
--   where
--     call Fail = return []
--     call (Or pxs pys) = do xs <- pxs; ys <- pys; return (xs ++ ys)
--     enter = undefined
--     calle Fail = []
--     calle (Or xs ys) = xs ++ ys
--     entere (Once (xs : xss)) = xs

---------------------------------------------------------------
-- Example : combine (Choice & Once) and Add

-- | Combine two operations
data (sig1 + sig2) a = Inl (sig1 a) | Inr (sig2 a)
instance (Functor sig1, Functor sig2) => Functor (sig1 + sig2) where
  fmap f (Inl x) = Inl (fmap f x)
  fmap f (Inr y) = Inr (fmap f y)

(#) :: (sig1 b -> b) -> (sig2 b -> b) -> ((sig1 + sig2) b -> b)
(alg1 # alg2) (Inl op) = alg1 op
(alg1 # alg2) (Inr op) = alg2 op

-- | Void
-- data Void a = Void deriving (Functor, Show)

-- runVoid :: Prog Void Void a -> a
-- runVoid (Return x) = x

-- | Add
data Add a = Add a a deriving (Functor, Show)

-- | Indexed Type
-- Nested f a n ≅ f^n a
data Nat = Zero | Succ Nat
data Nested f a :: Nat -> * where
  NestZ :: a -> Nested f a Zero
  NestS :: f (Nested f a n) -> Nested f a (Succ n)

unNestZ :: Nested f a Zero -> a
unNestZ (NestZ x) = x
unNestS :: Nested f a (Succ n) -> f (Nested f a n)
unNestS (NestS x) = x

-- data EndoAlg' f g c d = EndoAlg'
--   { returnE' :: forall n. Nested c d n -> Nested c d (Succ n)
--   , callE'   :: forall n. f (Nested c d (Succ n)) -> Nested c d (Succ n)
--   , enterE'  :: forall n. g (Nested c d (Succ (Succ n))) -> Nested c d (Succ n)
  -- }
data EndoAlg' f g c a = EndoAlg'
  { returnE' :: forall x. x -> c x
  -- , callE'   :: forall x. f (c x) -> c x  -- original
  , enterE'  :: forall x. g (c (c x)) -> c x
  -- , callE'   :: forall n. f (c (Nested c d n)) -> c (Nested c d n)  -- what we want
  , callE0   :: f (c (Nested c a Zero)) -> c (Nested c a Zero)
  , lift     :: forall n. (f (c (Nested c a n)) -> c (Nested c a n)) -> f (c (Nested c a (Succ n))) -> c (Nested c a (Succ n))
  -- the function list should be the same for all c ? c should be a monad ?
  }

hcata' :: (Functor f, Functor g, Functor c)
        => EndoAlg' f g c a
        -> (f (c (Nested c a n)) -> c (Nested c a n)) -- new parameter
        -> Prog f g (Nested c a n)
        -> c (Nested c a n)
hcata' alg calln (Return x) = returnE' alg x
hcata' alg calln (Call op)  = (calln . fmap (hcata' alg calln)) op -- use calln instead of callE
hcata' alg calln (Enter sc) = (enterE' alg . fmap (fmap unNestS . hcata' alg (lift alg calln) . fmap (NestS . hcata' alg calln))) sc
--     hcata alg (Enter sc) = (enterE  alg . fmap (               hcata  alg                  . fmap (        hcata  alg      ))) sc
-- pass (lift alg calln)

eval' :: (Functor f, Functor g, Functor c)
      => EndoAlg' f g c b
      -> BaseAlg f g c b
      -> (a -> b) -> Prog f g a -> b
eval' ealg balg gen (Return x) = gen x
eval' ealg balg gen (Call op)  = (callB balg . fmap (eval' ealg balg gen)) op
eval' ealg balg gen (Enter sc) = (enterB balg . fmap (fmap unNestZ . hcata' ealg (callE0 ealg) . fmap (NestZ . eval' ealg balg gen))) sc
--eval ealg balg gen (Enter sc)= (enterB balg . fmap (               hcata ealg                . fmap (        eval ealg balg gen))) sc

-- f = Add+f, g = g, c = Prog f g, b = Prog f g a
addnum :: (Functor f, Functor g, Num a) => Prog (Add + f) g a -> Prog f g a
addnum = eval' (EndoAlg' Return Enter calle0 lift) (BaseAlg (callb # Call) Enter) return
  where
    callb :: (Functor f, Functor g, Num a) => Add (Prog f g a) -> Prog f g a
    callb (Add px py) = do x <- px; y <- py; return (x+y)

    calle0 :: (Functor f, Functor g, Num a) => (Add + f) (Prog f g (Nested (Prog f g) (Prog f g a) Zero)) -> (Prog f g (Nested (Prog f g) (Prog f g a) Zero))
    calle0 = addalg0 # Call
      where
        addalg0 (Add px py) = do 
          x <- px; 
          y <- py;
          return $ NestZ $ callb (Add (unNestZ x) (unNestZ y))

    lift :: (Functor f, Functor g, Num a) => ((Add + f) ((Prog f g) (Nested (Prog f g) (Prog f g a) n)) -> (Prog f g) (Nested (Prog f g) (Prog f g a) n)) -> (Add + f) ((Prog f g) (Nested (Prog f g) (Prog f g a) (Succ n))) -> (Prog f g) (Nested (Prog f g) (Prog f g a) (Succ n))
    lift qwq = qwqadd # Call
      where
        qwqadd (Add px py)= do
          x <- px
          y <- py
          return $ NestS $ qwq (Inl (Add (unNestS x) (unNestS y)))

-- smart constructors
add :: Prog (Add + sig2) g a -> Prog (Add + sig2) g a -> Prog (Add + sig2) g a
add x y = Call $ Inl $ Add x y

fail :: Prog (f + Choice) g a
fail = Call $ Inr $ Fail

or :: Prog (sig1 + Choice) g a -> Prog (sig1 + Choice) g a -> Prog (sig1 + Choice) g a
or x y = Call $ Inr $ (Or x y)

once :: Functor f => Prog f Once a -> Prog f Once a
once x = Enter (Once (fmap return x))

-- example programs
program1 :: Prog (Add + Choice) Once Int
program1 = add (Return 1) (Return 2)
-- >>> allsols . addnum $ program1
-- [3]

program2 :: Prog (Add + Choice) Once Int
program2 = add (or (Return 1) (Return 2)) (or (return 10) (return 20))
-- >>> allsols . addnum $ program2
-- [11,21,12,22]


program3 :: Prog (Add + Choice) Once Int
program3 = once (add (or (Return 1) (Return 2)) (or (return 10) (return 20)))
-- >>> allsols . addnum $ program3
-- [11]

program4 :: Prog (Add + Choice) Once Int
program4 = do
  x <- once (add (or (Return 1) (Return 2)) (or (return 10) (return 20)))
  or (Return x) (Return (x*10))
-- >>> allsols . addnum $ program4
-- [11,101,20,110]

