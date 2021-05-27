{-# LANGUAGE TypeOperators,
             RankNTypes,
             FlexibleContexts,
             GADTs #-}

-- The Evil example from the paper: N. Xie, “Effect handlers, evidently,”, ICFP20

module Evil where

import AlgebraicEffects

--------------------------------

data One k = One (Int -> k)
instance Functor One where
  fmap f (One g) = One (f . g)

one :: (One < sig) => Free sig Int
one = inject (One return)

h1 :: Functor sig => Free (One + sig) a -> Free sig a
h1 = fold gen (alg # fwd)
  where
    gen = return
    alg (One k) = k 1

h2 :: Functor sig => Free (One + sig) a -> Free sig a
h2 = fold gen (alg # fwd)
  where
    gen = return
    alg (One k) = k 2

data Res where
  Done :: Int -> Res
  Again :: (() -> Free (One + Void) Res) -> Res

data Evil k = Evil (() -> k)
instance Functor Evil where
  fmap f (Evil g) = Evil (f . g)

evil :: (Evil < sig) => Free sig ()
evil = inject (Evil return)

hevil :: Free (Evil + (One + Void)) Res -> Free (One + Void) Res
hevil = fold gen (alg # fwd)
  where
    gen = return
    alg (Evil k) = return (Again k)
    -- 并没有使用resumption，而是直接把resumption传出去
    -- 下一个handler就handle不了他了
    -- 把这个节点变成一个return。并没有破坏homomorphism性质。

f :: Res -> Free Void Int
f (Again k) = do
  res <- h2 (k ())
  case res of
    Done x -> return x
f (Done x) = return x

body :: (One < sig, Evil < sig) => Free sig Res
body = do
  x <- one
  evil
  y <- one
  return (Done (x + y))

-- t :: Res
t :: Int
t = handleV $ f (handleV $ h1 (hevil body))
