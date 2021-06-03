{-# LANGUAGE TypeOperators,
             RankNTypes,
             FlexibleContexts,
             MultiParamTypeClasses,
             FunctionalDependencies,
             FlexibleInstances #-}

-- Using free monads to implement syntax trees.
-- Meaningless.

module SyntaxTree where

import AlgebraicEffects

-- view it as a syntax tree, instead of a sequence of computations
data Arith r = Add (Bool -> r) | Inc (() -> r)

instance Functor Arith where
  fmap f (Add g) = Add (f . g)
  fmap f (Inc g) = Inc (f . g)

add :: (Arith < sig) => Free sig a -> Free sig a -> Free sig a
add x y = inject $ Add (\b -> if b then x else y)

inc :: (Arith < sig) => Free sig a -> Free sig a
inc x = inject $ Inc (\() -> x)

handleA :: Functor sig => Free (Arith + sig) Int -> Free sig Int
handleA = fold gen (alg # fwd)
  where
    gen x = return x
    alg (Add k) = do x <- k True; y <- k False; return (x + y)
    alg (Inc k) = do x <- k (); return (x + 1)

expr :: (Arith < sig) => Free sig Int
expr = add (return 3) (inc (return 3))

runExpr :: Free (Arith + Void) Int -> Int
runExpr = handleV . handleA

----------------------------------------------------------------

data STLC r = Var String | Abs String (() -> r) | App (Bool -> r)

instance Functor STLC where
  fmap f (Var s) = Var s
  fmap f (Abs s k) = Abs s (f . k)
  fmap f (App k) = App (f . k)

tvar :: (STLC < sig) => String -> Free sig a
tvar s = inject $ Var s

tabs :: (STLC < sig) => String -> Free sig a -> Free sig a
tabs s x = inject $ Abs s (\() -> x)

tapp :: (STLC < sig) => Free sig a -> Free sig a -> Free sig a
tapp x y = inject $ App (\b -> if b then x else y)

tapp' :: (STLC < sig) => a -> a -> Free sig a
tapp' x y = inject $ App (\b -> if b then return x else return y)

data Val = VVar String | VAbs String Val deriving Show

-- In fact, it is just a fold on the syntax tree of STLC
-- Is there any difference between it and a EDSL implementation of STLC?
-- easier to add new syntax?
handleSTLC :: Functor sig => Free (STLC + sig) a -> Free sig Val
handleSTLC = fold gen (alg # fwd)
  where
    gen x = undefined
    alg (Var s) = return (VVar s)
    alg (App k) = do
      f <- k True
      t <- k False
      let (VAbs x y) = f
      return $ subst x t y
    alg (Abs s k) = do t <- k (); return (VAbs s t)
    subst x t (VVar s) | x == s = t
    subst x t (VAbs s k) | x /= s = VAbs s (subst x t k)

term :: (STLC < sig) => Free sig a
term = tapp (tabs "x" (tvar "x")) (tvar "y")

term' :: (STLC < sig) => Free sig a
term' = tabs "x" (tvar "x")

runSTLC :: Free (STLC + Void) a -> Val
runSTLC = handleV . handleSTLC