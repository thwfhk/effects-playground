{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, FlexibleContexts, UndecidableInstances #-}

-- Implementation of Monad Transformers
-- From the paper: N. Wu and T. Schrijvers, “Efficient Algebraic Effect Handlers,”

module MonadTransformer where

import Control.Monad.Trans (MonadTrans, lift)
import Control.Monad (liftM, liftM2, ap)
import Data.Char (isAlpha, isNumber)
import Prelude hiding (MonadFail, fail)

----------------------------------------------------------------
-- Id Monad
newtype Id a = Id {runId :: a}
instance Functor Id where
  fmap = liftM
instance Applicative Id where
  pure = return
  (<*>) = ap
instance Monad Id where
  return = Id
  Id x >>= f = f x


-- | The Operations of State Monad
class Monad m => MonadState s m | m -> s where
  get :: m s
  put :: s -> m ()
  -- some laws are required (omitted here)

-- | State Monad Transformer
newtype StateT s m a = StateT { runStateT :: s -> m (a, s) }

-- The lift function just preserves the state.
instance MonadTrans (StateT s) where
  lift m = StateT $ \s -> do {x <- m; return (x, s)}

-- The monadic effects of m are threaded through the computation.
instance Monad m => Functor (StateT s m) where
  fmap = liftM
instance Monad m => Applicative (StateT s m) where
  pure = return
  (<*>) = ap
instance Monad m => Monad (StateT s m) where
  return x = StateT $ \s -> return (x, s)
  StateT p >>= f = StateT $ \s -> do {(x, s') <- p s; runStateT (f x) s'}

-- Now we can affirm that StateT s m supports the operations in MonadState.
instance Monad m => MonadState s (StateT s m) where
  get = StateT $ \s -> return (s, s)
  put s' = StateT $ \s -> return ((), s')

-- Reconstruct State Monad from State Transformer Monad
type State s a = StateT s Id a

state :: (s -> (a, s)) -> State s a
state f = StateT $ Id . f

runState :: State s a -> s -> (a, s)
runState m = runId . runStateT m

-- Example
incr :: MonadState Int m => m ()
incr = do
  s <- get;
  put (s + 1);

test :: StateT Int IO ()
test = do
  incr;
  s <- get;
  lift (print s);

-- | Operations of Maybe Monad
class Monad m => MonadFail m where
  fail :: m a
  -- law: fail >>= f = fail

instance MonadFail Maybe where
  fail = Nothing

-- | Maybe Monad Transformer
-- It wraps the value of a monad m with Maybe.
newtype MaybeT m a = MaybeT { runMaybeT :: m (Maybe a) }

-- The lift function wrap all values of x with Just.
instance MonadTrans MaybeT where
  lift x = MaybeT $ fmap Just x

instance Monad m => Functor (MaybeT m) where
  fmap = liftM
instance Monad m => Applicative (MaybeT m) where
  pure = return
  (<*>) = ap
instance Monad m => Monad (MaybeT m) where
  return = lift . return
  MaybeT x >>= f = MaybeT $ do
    v <- x
    case v of
      Nothing -> return Nothing
      Just y  -> runMaybeT (f y)

instance Monad m => MonadFail (MaybeT m) where
  fail = MaybeT $ return Nothing

-- Example
-- Now we give an example of composition of monad transformers.
prog :: (MonadFail m, MonadState Int m) => m ()
prog = do
  incr;
  fail;
  incr;

-- Their are two orders to interpret m.
-- The interesting thing is that *different orders lead to different semantics*.
-- (*More left, the wrapper is more outer* (but to some extent the actual monad is more "inner").
--  And we can use "lift" to lift inner monad.)
-- (The main reason is that we have abstracted the operations as a typeclass.
--  Different instances lead to different interpretations.)

-- First, we define some instances to make them a "qualified monad".
-- (They can also avoid explict use of "lift".)
instance MonadFail m => MonadFail (StateT s m) where
  fail = lift fail
instance MonadState s m => MonadState s (MaybeT m) where
  get = lift get
  put = lift . put

-- For example, one semantic is to explain prog as having type StateT Int (MaybeT Id)
runProg1 :: StateT Int (MaybeT Id) a -> Maybe (a, Int)
runProg1 = runId . runMaybeT . flip runStateT 0

-- Another semantic is to explain prog as having type MaybeT (StateT Int Id)
-- In this way, the state will be preserved even if we failed.
runProg2 :: MaybeT (StateT Int Id) a -> (Maybe a, Int)
runProg2 = runId . flip runStateT 0 . runMaybeT

-- What's more, we can replace Id with other monads like IO monad.
-- Operations of IO Monad
class MonadIO m where
  readl :: m String
  printl :: String -> m ()

instance MonadIO IO where
  readl = getLine
  printl s = putStrLn s

instance (Monad m, MonadIO m) => MonadIO (MaybeT m) where
  readl = lift readl
  printl = lift . printl

instance (Monad m, MonadIO m) => MonadIO (StateT s m) where
  readl = lift readl
  printl = lift . printl

-- prog2 :: (MonadFail m, MonadState Int m, MonadIO m) => m ()
-- prog2 = do
--   printl "Please enter your name";
--   name <- readl;
--   if not (all isAlpha name) then fail else
--     printl "Please enter your addr";
--     addr <- readl;
--     if not (all isNumber addr) then fail else
--       incr;
--       printl ("Hi " ++ name ++ " from " ++ addr);

-- We can record the information about where the program failed in the state.

readUserName :: (MonadFail m, MonadState String m, MonadIO m) => m String
readUserName = do
  printl "Please enter your name:"
  name <- readl
  -- put "Hi"
  if not (all isAlpha name)
    then put "It seems that you have a strange name :(" >> fail
    else return name

readPhoneNumber :: (MonadFail m, MonadState String m, MonadIO m) => m String
readPhoneNumber = do
  printl "Please enter your phone number:"
  number <- readl
  if not (all isNumber number)
    then put "Sorry, I don't understand your numbers :(" >> fail
    else return number

sayHello :: (MonadFail m, MonadState String m, MonadIO m) => m ()
sayHello = do
  name <- readUserName
  number <- readPhoneNumber
  printl $ "SUCCESS: Hello " ++ name ++ ", your phone number is " ++ number ++ "."
-- An interesting fact: when it failed, the program immediately terminated
-- (because of the implementation of Maybe Monad)

runProg :: Monad m => StateT String (MaybeT m) a -> m (Maybe (a, String))
runProg = runMaybeT . flip runStateT ""

-- If we place MaybeT at the left of StateT, we can still know the state even if it fails.
runProg' :: Monad m => MaybeT (StateT String m) a -> m (Maybe a, String)
runProg' = flip runStateT "" . runMaybeT

-- And we can explicitly print the state message
runProgFinal :: (Monad m, MonadIO m) => MaybeT (StateT String m) a -> m ()
runProgFinal prog = do
  t <- (flip runStateT "" . runMaybeT) prog
  if snd t /= "" then printl $ "ERROR: " ++ snd t else return ()