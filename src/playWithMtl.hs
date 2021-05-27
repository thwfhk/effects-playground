{-# LANGUAGE FlexibleContexts #-}

-- Play with the mtl package
-- Reference: https://cseweb.ucsd.edu/classes/wi14/cse230-a/lectures/lec-transformers.html

import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.IO.Class
import Control.Monad.Writer

incur :: (MonadState Int m) => m ()
incur = do
  n <- get
  put (n + 1)

data Expr
  = Val Int
  | Add Expr Expr
  | Div Expr Expr
  deriving Show

msg :: (Show a1, Show a2) => a1 -> a2 -> [Char]
msg t r = "term: " ++ show t ++ ", yields " ++ show r ++ "\n"

eval :: (MonadWriter String m, MonadError String m, MonadState Int m, MonadIO m) => Expr -> m Int
eval v@(Val n) = tell (msg v n) >> return n
eval v@(Add x y) = do
  n <- eval x
  m <- eval y
  tell $ msg v (n + m)
  return $ n + m
eval v@(Div x y) = do
  n <- eval x
  m <- eval y
  if m == 0
    then throwError $ "invalid zero"
    else do
      incur
      liftIO $ putStrLn "[incur]"
      tell $ msg v (n + m)
      return $ n `div` m

runEval :: Show a => ExceptT e (StateT Int (WriterT w IO)) a -> IO ((Either e a, Int), w)
runEval = runWriterT . flip runStateT (0 :: Int) . runExceptT

pretty :: Show a => IO (a, String) -> IO ()
pretty input = do
  (t, s) <- input
  print t
  putStrLn s

-- final :: Show a => ExceptT String (StateT Int (WriterT String IO)) a -> IO ()
final :: Expr -> IO ()
final = pretty . runEval . eval

prog :: Expr
prog = Add (Div (Val 3) (Val 1)) (Div (Val 3) (Val 0))

prog' :: Expr
prog' = Add (Div (Val 3) (Val 1)) (Div (Val 3) (Val 3))