{-# LANGUAGE TypeOperators,
             RankNTypes,
             FlexibleContexts #-}


-- The Grammar Example from the paper: T. Schrijvers, “Effect Handlers in Scope.” 
module Grammar where

import AlgebraicEffects

-- | Symbol: matches c with the current input and passes c to g if it succeeds.
-- It can be used to implement parsers.
-- a little like State s
data Symbol k = Symbol Char (Char -> k)
instance Functor Symbol where
  fmap f (Symbol c g) = Symbol c (f . g)

symbol :: (Symbol < sig) => Char -> Free sig Char
symbol c = inject (Symbol c return)

-- a dummy handler
handleSy :: Functor sig => Free (Symbol + sig) a -> Free sig a
handleSy = fold genS (algS # fwd)
  where
    genS = return
    algS (Symbol c g) = g c

parse :: (Nondet < sig) => Free (Symbol + sig) a -> (String -> Free sig a)
parse = fold gen (alg # fwdPP)
  where
    gen x = \s -> case s of
      [] -> return x
      _  -> end
    alg (Symbol c g) = \s -> case s of
      (x:xs) -> if x == c then g c xs else end
      []     -> end


solve :: (forall sig . Nondet < sig => Free (Symbol + sig) a -> (String -> Free sig a))
      -> Free (Symbol + (Nondet + Void)) a -> String -> [a]
solve h p s = handleV . handleN . h p $ s

-- A parser for arithmetic expressions
digit :: (Nondet < sig, Symbol < sig) => Free sig Char
digit = foldr (|>) end (fmap symbol ['0'..'9'])

many, many1 :: (Nondet < sig) => Free sig a -> Free sig [a]
many p  = many1 p |> return []
many1 p = do a <- p; as <- many p; return (a:as)

expr :: (Nondet < sig, Symbol < sig) => Free sig Int
expr = do i <- term; symbol '+'; j <- expr; return (i+j)
    |> do i <- term; return i

term :: (Nondet < sig, Symbol < sig) => Free sig Int
term = do i <- factor; symbol '*'; j <- term; return (i*j)
    |> do i <- factor; return i

factor :: (Nondet < sig, Symbol < sig) => Free sig Int
factor = do ds <- many1 digit; return (read ds)
      |> do symbol '('; i <- expr; symbol ')'; return i

