{-# LANGUAGE StandaloneDeriving, UndecidableInstances, DeriveFunctor,
    RankNTypes, TypeOperators #-}
module ScopedEffects where

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
  , enterE  :: forall x. g (c (c x)) -> c x}

hcata :: (Functor f, Functor g) => EndoAlg f g c -> Prog f g a -> c a
hcata alg (Return x) = returnE alg x
hcata alg (Call op)  = (callE alg . fmap (hcata alg)) op
hcata alg (Enter sc) = (enterE alg . fmap (hcata alg . fmap (hcata alg))) sc

eval :: (Functor f, Functor g) => EndoAlg f g c -> BaseAlg f g c b -> (a -> b) -> Prog f g a -> b
eval ealg balg gen (Return x) = gen x
eval ealg balg gen (Call op)  = (callB balg . fmap (eval ealg balg gen)) op
eval ealg balg gen (Enter sc) = (enterB balg . fmap (hcata ealg . fmap (eval ealg balg gen))) sc

-- Combine two operations

data (sig1 + sig2) a = Inl (sig1 a) | Inr (sig2 a)
instance (Functor sig1, Functor sig2) => Functor (sig1 + sig2) where
  fmap f (Inl x) = Inl (fmap f x)
  fmap f (Inr y) = Inr (fmap f y)

(#) :: (sig1 b -> b) -> (sig2 b -> b) -> ((sig1 + sig2) b -> b)
(alg1 # alg2) (Inl op) = alg1 op
(alg1 # alg2) (Inr op) = alg2 op

---------------------------------------------------------------
-- Example 1

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

-- smart constructors
fail :: Functor g => Prog Choice g a
fail = Call Fail
or :: Functor g => Prog Choice g a -> Prog Choice g a -> Prog Choice g a
or x y = Call (Or x y)
once :: Functor f => Prog f Once a -> Prog f Once a
once x = Enter (Once (fmap return x))

-- print
-- printProg :: Show a => Prog Choice Once a -> String
-- printProg (Return x) = "Return (" ++ show x ++ ")"
-- printProg (Call op) = "Call (" ++ case op of
--   Fail -> "Fail)"
--   Or x y -> "Or (" ++ printProg x ++ ", " ++ printProg y ++ ")"
-- printProg (Enter sc) = "Enter (" ++ case sc of
--   Once x -> "Once (" ++ printProgProg x ++ ")"
-- printProgProg :: Show a => Prog Choice Once (Prog Choice Once a) -> String
-- printProgProg (Return x) = "Return (" ++ printProg x ++ ")"
-- printProgProg (Call op) = "Call (" ++ case op of
--   Fail -> "Fail)"
--   Or x y -> "Or (" ++ printProgProg x ++ ", " ++ printProgProg y ++ ")"
-- printProgProg (Enter sc) = "SCOPE"

-- progs
prog1 :: Prog Choice Once Int
prog1 = once (or (return 1) (return 5)) >>= \x -> or (return x) (return (x+1))
test1 :: Prog Choice Once Int
test1 = or (return 1) (return 5)
test2 :: Prog Choice Once Int
test2 = once (or (return 1) (return 5))

select :: Functor g => [a] -> Prog Choice g (a, [a])
select [] = fail
select (x:xs) = return (x,xs) `or` do {(y,ys) <- select xs; return (y,x:ys)}

perm :: Functor g => [a] -> Prog Choice g [a]
perm [] = return []
perm xs = do (y,ys) <- select xs; zs <- perm ys; return (y:zs)

prog1' :: Prog Choice Once [Int]
prog1' = perm [1,2,3,4]

---------------------------------------------------------------
-- Example 2

data Depth a = Depth Int a deriving (Functor, Show)
depth :: Functor f => Int -> Prog f Depth a -> Prog f Depth a
depth d p = Enter (Depth d (fmap return p))

newtype DepthCarrier a = DepthCarrier (Int -> [a])

dbs :: Prog Choice Depth a -> [a]
dbs = eval (EndoAlg returnd calld enterd) (BaseAlg calll exitd) return where
  returnd x = DepthCarrier (const [x])
  calld Fail = DepthCarrier (const [])
  calld (Or (DepthCarrier fxs) (DepthCarrier fys)) =
    DepthCarrier (\d -> if d == 0 then [] else fxs (d-1) ++ fys (d-1))
  enterd (Depth d (DepthCarrier fxs)) =
    DepthCarrier (\d' -> concat [fys d' | DepthCarrier fys <- fxs d])
  -- enterd要想把fxs里面的也减去，需要知道fys实际上有几层 -> 需要额外返回一个实际层数
  calll (Or xs ys) = xs ++ ys
  exitd (Depth d (DepthCarrier  fxs)) = concat (fxs d)

prog2 :: Prog Choice Depth Int
prog2 = depth 2 (or (or (or (return 1) (return 2)) (return 3)) (or (return 4) (return 5)))
-- [3,4,5]

prog2' :: Prog Choice Depth Int
prog2' = depth 2 (or (depth 2 (or (or (return 1) (return 2)) (return 3))) (or (return 4) (return 5)))
-- [1,2,3,4,5]

---------------------------------------------------------------
-- Example 3: combine scoped operations with algebraic operations

data Id a = Id a deriving (Functor, Show)

data Add a = Add a a deriving (Functor, Show)

add :: Functor g => Prog Add g a -> Prog Add g a -> Prog Add g a
add x y = Call (Add x y)

addnum :: (Functor f, Functor g, Num a) => Prog (Add + f) g a -> Prog f g a
addnum = eval ealg (BaseAlg (callb # Call) Enter) return
  where
    callb :: (Num a, Functor f, Functor g) => Add (Prog f g a) -> Prog f g a
    callb (Add px py) = do x <- px; y <- py; return (x+y)
    ealg :: EndoAlg (Add + f) g (Prog f g)
    ealg = EndoAlg Return (calle # Call) Enter
      where
        calle :: Add (Prog f g x) -> Prog f g x
        calle = undefined -- NOTE: This is the problem!