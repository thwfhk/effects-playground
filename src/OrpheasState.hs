{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}

module OrpheasState where

import FreeMonad (Free(..), fold, fwdPP, type (+)(..), Void, run, (#))

newtype Get s k = Get (s -> k)
data    Put s k = Put s (() -> k)

instance Functor (Get s) where
  fmap f (Get g) = Get (f . g)

instance Functor (Put s) where
  fmap f (Put s g) = Put s (f . g)

hState :: Functor f => Free (Get s + Put s + f) a -> (s -> Free f a)
hState = hPut . hGet
  where
    hGet :: Functor f => Free (Get s + Put s + f) a -> Free (Put s + f) (s -> Free f a)
    hGet = fold genGet (algGet # Op)
      where
        genGet :: Functor f => a -> Free (Put s + f) (s -> Free f a)
        genGet x = return (\s -> return x)
        algGet :: Functor f => Get s (Free (Put s + f) (s -> Free f a))
                            -> Free (Put s + f) (s -> Free f a)
        algGet (Get k) = return (\s -> hPut (k s) s)
    hPut :: Functor f => Free (Put s + f) (s -> Free f a) -> (s -> Free f a)
    hPut = fold genPut (algPut # fwdPP)
      where
        genPut :: Functor f => (s -> Free f a) -> s -> Free f a
        genPut x = x
        algPut :: Functor f => Put s (s -> Free f a) -> s -> Free f a
        algPut (Put s k) = \_ -> k () s

get :: Functor f => Free (Get s + Put s + f) s
get = Op (Inl $ Get return)

put :: Functor f => s -> Free (Get s + Put s + f) ()
put s = Op (Inr . Inl $ Put s return)

evalState :: s -> Free (Get s + Put s + Void) a -> a
evalState s x = run (hState x s)

prog1 :: Free (Get Int + Put Int + Void) Int
prog1 = do
  s <- get
  put (s+1)
  get

-- >>> evalState 0 prog1
-- 1

prog2 :: Free (Get Int + Put Int + Void) Int
prog2 = do
  put 42
  s <- get
  put (s+42)
  get

-- >>> evalState 0 prog2
-- 84
