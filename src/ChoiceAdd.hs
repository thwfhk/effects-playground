{-# LANGUAGE StandaloneDeriving, UndecidableInstances,
    TypeOperators, EmptyCase, InstanceSigs, DeriveFunctor #-}

module FreeMonad2 where

import Control.Monad (liftM, liftM2, ap)
import FreeMonad hiding (Fail)
import Prelude hiding (fail, or)

data Choice a = Fail | Or a a deriving (Functor, Show)

handleChoice :: Functor f => Free (Choice + f) a -> Free f [a]
handleChoice = fold gen (alg # fwd)
  where
    gen x = return [x]
    alg Fail = return []
    alg (Or px py) = do x <- px; y <- py; return (x ++ y)

data Add a = Add a a deriving (Functor, Show)
handleAdd :: (Functor f, Num a) => Free (Add + f) a -> Free f a
handleAdd = fold return (alg # fwd)
  where
    alg (Add px py) = do x <- px; y <- py; return (x + y)

addl x y = Op $ Inl $ Add x y
addr x y = Op $ (Inr . Inl) $ Add x y
faill = Op $ Inl $ Fail
failr = Op $ (Inr . Inl) $ Fail
orl x y = Op $ Inl $ Or x y
orr x y = Op $ (Inr . Inl) $ Or x y

test :: Free (Add + Choice) Int
test = addl (return 1) (return 2)

prog1 :: Free (Add + (Choice + Void)) Integer
prog1 = addl (orr (return 1) (return 2)) (orr (return 10) (return 20))
-- >>> (handleV . handleChoice . handleAdd) prog1
-- [11,21,12,22]

prog1' :: Free (Choice + (Add + Void)) Integer
prog1' = addr (orl (return 1) (return 2)) (orl (return 10) (return 20))
-- >>> (handleV . handleAdd . handleChoice) prog1'
-- No instance for (Num [Integer]) arising from a use of ‘handleAdd’

-- Op (Inl (Add (Op (Inr (Inl (Or (Return 1) (Return 2))))) (Op (Inr (Inl (Or (Return 10) (Return 20)))))))

-- Op (Inl (Or 
--     (Op (Inl (Or (Return 11) (Return 21)))) 
--     (Op (Inl (Or (Return 12) (Return 22))))))