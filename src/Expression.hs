{-# LANGUAGE TypeOperators,
             RankNTypes,
             FlexibleContexts,
             MultiParamTypeClasses,
             FunctionalDependencies,
             FlexibleInstances #-}

-- ALgebraic effects are not sufficient for implementing the STLC.
-- From the paper: “Staged Effects and Handlers for Modular Languages with Abstraction,”

module Expression where

import AlgebraicEffects
import Debug.Trace

data Arith r = Add (Int, Int) (Int -> r) | Inc Int (Int -> r)

instance Functor Arith where
  fmap f (Add t g) = Add t (f . g)
  fmap f (Inc t g) = Inc t (f . g)

add :: (Arith < sig) => Int -> Int -> Free sig Int
add x y = inject $ Add (x, y) return

inc :: (Arith < sig) => Int -> Free sig Int
inc x = inject $ Inc x return

handleA :: Functor sig => Free (Arith + sig) Int -> Free sig Int
handleA = fold gen (alg # fwd)
  where
    gen x = return x
    alg (Add (x, y) k) = k (x + y)
    alg (Inc x k) = k (x + 1)

expr :: (Arith < sig) => Free sig Int
expr = do x <- inc 3; add 3 x

runExpr :: Free (Arith + Void) Int -> Int
runExpr = handleV . handleA

----------------------------------------------------------------

data STLC v r = Var String (v -> r)
              | App (v, v) (v -> r) 
              --  | Abs (String, M v) (v -> r)
              --  | Let (String, v, M v) (v -> r)
-- NOTE: abs and let cannot be implemented because of they use `M v`

instance Functor (STLC v) where
  fmap f (Var s g) = Var s (f . g)
  fmap f (App t g) = App t (f . g)

tvar :: (STLC v < sig) => String -> Free sig v
tvar s = inject $ Var s return

tapp :: (STLC v < sig) => v -> v -> Free sig v
tapp x y = inject $ App (x, y) return

-- tabs :: (STLC v < sig) => String -> Free sig v -> Free sig v
-- tabs s t = inject $ Abs (s, t) return

data Val = VVar String | VAbs String Val deriving Show

handleSTLC :: Functor sig => Free (STLC Val + sig) Val -> Free sig Val
handleSTLC = fold gen (alg # fwd)
  where
    gen x = return x
    alg (Var s k) = k (VVar s)
    alg (App (x, y) k) = k (VVar ("app(" ++ show x ++ ", " ++ show y ++ ")"))

term :: (STLC v < sig) => Free sig v
term = do
  x <- tvar "x"
  y <- tvar "y"
  tapp x y

runSTLC :: Free (STLC Val + Void) Val -> Val
runSTLC = handleV . handleSTLC

----------------------------------------------------------------
newtype Fix f = In {out :: f (Fix f)}

cata :: Functor f => (f a -> a) -> Fix f -> a
cata f = f . fmap (cata f) . out

class Monad m => LambdaM m v where
  fetch :: String -> m v
  apply :: v -> v -> m v
  -- abstr :: String -> m v -> m v
  -- letbind :: String -> v -> m v -> m v

instance LambdaM (Free (STLC v + Void)) v where
  fetch = tvar
  apply = tapp

data LambdaF v = Fetch String | Abstr String v | Apply v v
instance Functor LambdaF where
  fmap f (Fetch s) = Fetch s
  fmap f (Abstr s v) = Abstr s (f v)
  fmap f (Apply x y) = Apply (f x) (f y)

lambdaTrans :: Fix LambdaF -> Free (STLC v + Void) v
lambdaTrans = cata alg
  where
    alg (Fetch s) = fetch s
    alg (Apply x y) = do
      x' <- x;
      y' <- y;
      apply x' y'
    -- alg (Abstr s v) = abstr s v

lambdaProg :: Fix LambdaF
lambdaProg = In (Apply (In (Fetch "x")) (In (Fetch "y")))

t :: Free (STLC Val + Void) Val
t = lambdaTrans lambdaProg