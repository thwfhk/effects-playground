{-# LANGUAGE TypeOperators, RankNTypes, GADTs, KindSignatures, RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables, QuantifiedConstraints, MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies, FlexibleInstances, ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor, InstanceSigs, UndecidableInstances, FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}

module ModScopeOps where

import Prelude hiding (or, LT)
import Control.Monad (join, ap, liftM)
import Control.Monad.Trans.Class
import Control.Monad.Trans.State (StateT(..))
import Union 


-- This file shows how scoped operation can be handled modularly.


-- * Programs with algebraic and scoped operations

data Prog f g a
  = Return a
  | Call (f (Prog f g a))
  | Enter (g (Prog f g (Prog f g a)))


instance (Functor f , Functor g) => Functor (Prog f g) where 
    fmap f (Return x) = Return (f x)
    fmap f (Call t)   = Call (fmap (fmap f ) t)
    fmap f (Enter t)  = Enter (fmap (fmap (fmap f )) t)

instance (Functor f , Functor g) => Applicative (Prog f g) where 
    pure  = return
    (<*>) = ap

instance (Functor f, Functor g) => Monad (Prog f g) where
    return = Return
    Return x >>= f = f x
    Call op  >>= f = Call (fmap (>>= f) op)
    Enter sc >>= f = Enter (fmap (fmap (>>= f)) sc)

deriving instance (Show a, forall x . Show x => Show (f x),
    forall x . Show x => Show (g x)) => Show (Prog f g a)

-- * First-order modular carriers and handlers

type Signature f g = (Functor f, Functor g)

data Alg f g c = Alg 
  { call  :: forall x . f (c x) -> c x
  , enter :: forall x . g (c (c x)) -> c x
  }

initialAlg :: Alg f g (Prog f g)
initialAlg = Alg Call Enter

-- For a full subcategory S of Endo(Endo(C)), an S-modular carrier c 
-- is a functor Mnd(C) -> Endo(C) with 
--   1. fwd, a functor from the (dependent) product category 
--        (m : Mnd(C), s : S, op : s m -> m) 
--      to 
--        (c m : Endo(C), s : S, op' : s (c m) -> c m )
--
--   2. liftC, a natural transformation from m to (c m) such that
--      it is an homomorphism from <m, s, op> to (fwd <m, s, op>)
--
-- Questions: how does it relate to modular carrier in the old sense
-- and monad transformers.
--


class MCarrier (c :: (* -> *) -> (* -> *)) where
  fwd   :: (Monad m, Signature f g) => Alg f g m -> Alg f g (c m)
  liftC :: Monad m => m x -> c m x
  -- Law : liftC should be an algebra homomorphism from m to (c m)

-- TODO: probably it's better to make |fwd| a part of MHandler
-- instead of a typeclass itself since there isn't a canonical |fwd|
-- for a |c :: (* -> *) -> (* -> *)|.
data MHandler f g c a b = MHandler 
  { alg :: forall m . Monad m => Alg f g (c m)
  , run :: forall m . Monad m => c m a -> m b
  }

-- * Handle with modular handlers

data Empty k deriving Functor

handle :: forall f g f' g' a b c . (Signature f g, Signature f' g', MCarrier c)
       => MHandler f g c a b
       -> Prog (f :+: f') (g :+: g') a -> Prog f' g' b

handle (MHandler {..}) = run . fold where
  -- Note: this |fold| ought to be implemented with the |eval| in our ICFP submission
  fold :: forall x . Prog (f :+: f') (g :+: g') x -> c (Prog f' g') x

  fold (Return x) = liftC (Return x)

  fold (Call (Inl op)) = (call alg              . fmap fold) op
  fold (Call (Inr op)) = (call (fwd initialAlg) . fmap fold) op

  fold (Enter (Inl sc)) = (enter alg              . fmap fold . fmap (fmap fold)) sc
  fold (Enter (Inr sc)) = (enter (fwd initialAlg) . fmap fold . fmap (fmap fold)) sc

---------------------------------------------------------------
-- Wenhao:
-- I think the core part for forwarding here is |fwd initialAlg :: Alg f' g' (c (Prog f' g'))|.
-- > call (fwd initialAlg)  :: f' (c (Prog f' g') x) -> c (Prog f' g') x
-- > enter (fwd initialAlg) :: g' (c (Prog f' g') (c (Prog f' g') x)) -> c (Prog f' g') x
-- What the |fwd| used in the calculus (which I call |fwdCal| here for disambiguation ) does
-- is exactly the same as |enter (fwd initialAlg)|
fwdCal :: (Signature f g, MCarrier c)
       => g (c (Prog f g) (c (Prog f g) x)) -> c (Prog f g) x
fwdCal = undefined
-- ( I use the free monad definition in this code file for consistency. 
--   In the Haskell implementation of the calculus, the |Enter| has type 
--   |g (Prog f g y) -> (y -> Prog f g x) -> Prog f g x|, which looks equivalent to
--   |g (Prog f g (Prog f g x)) -> Prog f g x| )

-- The |lift| used in the calculus which I call |liftCal| here is more like a syntactic sugar,
-- which deals with a sepcial form of modular carriers |c m a = m (m' a)|.
liftCal :: (Signature f g, Monad m)
        => m (Prog f g (m a)) -> Prog f g (m a)
liftCal = undefined
-- With |liftCal|, the |fwdCal| can be defined as follows:
fwdCal' :: (Signature f g, Monad m)
        => g (Prog f g (m (Prog f g (m x)))) -> Prog f g (m x)
fwdCal' = Enter . fmap (fmap liftCal)
-- It is easy to see that if |m| is traversable, then one implementation of |liftCal| is
liftCal' :: (Signature f g, Monad m, Traversable m)
         => m (Prog f g (m a)) -> Prog f g (m a)
liftCal' = fmap join . sequence
-- But the semantics it gives may not be what we want. I think the semantics of forwarding
-- given by the functorial monad transformer is in a similar situation.

-- The |liftp| deals with another special form of modular carriers |c m a = s -> m (m' a)|
liftpCal :: (Signature f g, Monad m)
         => m (s -> Prog f g (m a)) -> Prog f g (m a)
liftpCal = undefined
-- With |liftpCal|, the |fwdCal| can be defined as follows:
fwdCal'' :: (Signature f g, Monad m)
         => g (s -> Prog f g (m (s -> Prog f g (m x)))) -> s -> Prog f g (m x)
fwdCal'' t = \ s -> Enter . fmap (fmap liftpCal) . fmap ($s) $ t
---------------------------------------------------------------


runEmpty :: Prog Empty Empty a -> a
runEmpty (Return x) = x


-- When the argument is algebraic, it is an isomorphism with inverse tau0'
tau0 :: (Monad m, Functor f) => (forall x . f (m x) -> m x)  -- algebraic
                             -> (forall x . f x -> m x)
tau0 alg = alg . fmap return

tau0' :: (Monad m, Functor f) => (forall x . f x -> m x)
                              -> (forall x . f (m x) -> m x) -- algebraic
tau0' op = join . op

-- When the argument is algebraic in the second m, it is an isomorphism
-- with inverse tau1'
tau1 :: (Monad m, Functor g) => (forall x . g (m (m x)) -> m x)  -- algebraic
                             -> (forall x . g (m x) -> m x)
tau1 alg = alg . fmap (fmap return)

tau1' :: (Monad m, Functor g) => (forall x . g (m x) -> m x)
                              -> (forall x . g (m (m x)) -> m x) -- algebraic
tau1' op = join . op


-- * Exceptions with catch

data Throw e k = Throw e deriving (Functor, Show)
data Catch e k = Catch k (e -> k) deriving Functor

instance Show k => Show (Catch () k) where
  show (Catch e k) = "(Catch { " ++ show e ++ " }" ++ " by { " ++ show (k ()) ++ "})"

newtype EitherC e m x = EC { unEC :: m (Either e x) }

joinEC :: Monad m => m (Either e (m (Either e x))) -> m (Either e x)
joinEC c = do e <- c
              case e of
                (Left e)   -> return (Left e)
                (Right c') -> c'

instance MCarrier (EitherC e) where
  fwd :: forall m f g e . (Monad m, Signature f g) => Alg f g m -> Alg f g (EitherC e m)
  fwd (Alg {..}) = Alg call' enter' where
    call' :: forall x . f (EitherC e m x) -> EitherC e m x
    call' = EC . call . fmap unEC

    enter' :: forall x . g (EitherC e m (EitherC e m x)) -> EitherC e m x
    enter' = EC . joinEC . tau1 enter . fmap (fmap (fmap unEC)) . fmap unEC

  liftC = EC . fmap Right

hEx :: MHandler (Throw e) (Catch e) (EitherC e) a (Either e a)
hEx = MHandler {..} where
  run = unEC

  alg :: Monad m => Alg (Throw e) (Catch e) (EitherC e m)
  alg = Alg call enter

  call :: Monad m => Throw e (EitherC e m x) -> (EitherC e m x)
  call (Throw e) = EC $ return (Left e)

  enter :: Monad m => Catch e (EitherC e m (EitherC e m x)) -> EitherC e m x
  enter (Catch p h) = EC $
    do x <- unEC p
       case x of
         (Right c) -> unEC c
         (Left e)  -> joinEC (fmap (fmap unEC) (unEC (h e)))

-- Some example programs using exceptions

throw :: (In (Throw e) f) => e -> Prog f g x
throw e = Call (inj (Throw e))

catch :: (Signature f g, In (Catch e) g) 
      => Prog f g a -> (e -> Prog f g a) -> Prog f g a
catch p h = Enter (inj (Catch (fmap return p) (fmap return . h)))

prod :: (Signature f g, In (Throw ()) f, In (Catch ()) g) 
     => [Int] -> Prog f g Int
prod l = catch (go l) (\() -> return 0) where
  go []     = return 1
  go (0:xs) = throw ()
  go (x:xs) = do p <- go xs; return (p * x)

excHdl :: Prog (Throw () :+: Empty) (Catch () :+: Empty) Int -> Either () Int
excHdl = runEmpty . handle hEx

test1 = excHdl (prod [1,2,3]) == Right 6

test2 = excHdl (prod [0,undefined,2,3]) == Right 0

-- * Jaskeliof and Moggi showed how to lift any scoped operation (which they 
--   call first-order operation) along a functorial monad transformer using the codensity
--   monad, and thus every functorial monad transformer is a MCarrier.

type (f -.> g) = forall x . f x -> g x

class (forall x . Functor x => Functor (c x)) => HFunctor c where
  hmap :: (Functor f, Functor g) => (f -.> g) -> (c f -.> c g)

class (MonadTrans c, forall m . Monad m => Monad (c m)) => MonadTrans' c where
  -- Nothing

instance (MonadTrans c, forall m . Monad m => Monad (c m)) => MonadTrans' c
  -- Nothing

class (MonadTrans' c, HFunctor c) => FMonadTrans c where
  -- In Jaskeliof and Moggi's paper, a functorial monad transformer is required to
  -- be equipped with the following liftF and that it coincides with the lift of c from
  -- the MonadTrans class
  -- >  liftF :: Functor f => f -.> c f
  -- But it seems we don't need this requirement in our application.
  -- Consequently, the list transformer |ListT| (see below) is a functorial monad transformer
  -- in our sense too.
 
instance (MonadTrans' c, HFunctor c) => FMonadTrans c where
  -- Nothing

-- Codensity monads
newtype Cod f a = Cod { runCod :: forall x . (a -> f x) -> f x } deriving Functor

instance Functor f => Applicative (Cod f) where
  pure  = return
  (<*>) = ap

instance Functor f => Monad (Cod f) where
  return x = Cod $ \k -> k x
  m >>= f = Cod $ \k -> runCod m (\a -> runCod (f a) k)

toCod :: Monad m => m x -> Cod m x
toCod m = Cod $ \k -> join (fmap k m)

fromCod :: Monad m => Cod m x -> m x
fromCod c = runCod c return

ranIso :: Functor g => (forall x . g (m x) -> m x) -> (forall x . g x -> Cod m x)
ranIso op g = Cod $ \k -> op (fmap k g)

-- Turning a scoped operation on m to an algebraic operation on Cod m
codAlg :: (Monad m, Functor g) => (forall x . g (m (m x)) -> m x)              -- algebraic
                               -> (forall x . g (Cod m x) -> Cod m x)
codAlg f = tau0' (ranIso (tau1 f))

-- lift any algebraic operation along any monad transformer
liftAlg :: (MonadTrans' c, Functor f, Monad m) => (forall x . f (m x) -> m x)   -- algebraic
                                               -> (forall x . f (c m x) -> c m x)
liftAlg op = tau0' (lift . tau0 op)

instance {-# OVERLAPPABLE #-} FMonadTrans c => MCarrier c where
  fwd :: forall f g m . (Monad m, Signature f g) => Alg f g m -> Alg f g (c m)
  fwd (Alg {..}) = Alg call' enter' where
    call' :: forall x . f (c m x) -> c m x
    call' = liftAlg call

    enter' :: forall x . g (c m (c m x)) -> c m x
    enter' = tau1' (hmap fromCod . liftAlg (codAlg enter) . fmap (hmap toCod))

  liftC = lift

-- StateT is a functorial monad transformer and we can use it to handle
-- stateful operations

instance HFunctor (StateT s) where
  hmap tau c = StateT $ \s -> tau (runStateT c s)

data GetPut s k = Put s k | Get (s -> k) deriving Functor

data Local s k = Local (s -> s) k deriving Functor

hSt :: s -> MHandler (GetPut s) (Local s) (StateT s) a (a, s)
hSt s0 = MHandler (Alg call enter) (\c -> runStateT c s0) where
  call (Put s' k) = StateT $ \s -> runStateT k s'
  call (Get k) = StateT $ \s -> runStateT (k s) s

  enter :: Monad m => Local s (StateT s m (StateT s m x)) -> StateT s m x
  enter (Local f c) = StateT $ 
    \s -> do (a, s') <- runStateT c (f s)
             runStateT a s

get :: (Signature f g, In (GetPut s) f) => Prog f g s
get = Call (inj (Get return))

put :: (Signature f g, In (GetPut s) f) => s -> Prog f g ()
put s = Call (inj (Put s (return ())))

local :: (Signature f g, In (Local s) g) => (s -> s) -> Prog f g a -> Prog f g a
local f p = Enter (inj (Local f (fmap return p)))


-- Some examples involving state and exceptions

hdlStThenEx :: Prog (GetPut Int :+: (Throw () :+: Empty)) (Local Int :+: (Catch () :+: Empty)) a
            -> Either () (a, Int)
hdlStThenEx = runEmpty . handle hEx . handle (hSt (0 :: Int))

hdlExThenSt :: Prog (Throw () :+: (GetPut Int :+: Empty)) (Catch () :+: (Local Int :+: Empty)) a
            -> (Either () a, Int)
hdlExThenSt = runEmpty . handle (hSt (0 :: Int)) . handle hEx

progStEx, progStEx2
  :: ( Signature f g
     , In (GetPut Int) f, In (Local Int) g
     , In (Throw ()) f, In (Catch ()) g )
  => Prog f g Int

progStEx = do catch (do { put (1 :: Int); throw () }) 
                    (\() -> do { (x :: Int) <- get; put (x+1) })
              get

progStEx2 = do catch (local (id :: Int -> Int) (do { put (5 :: Int); throw () }))
                     (\() -> get)

-- Handling exception before state is the global state semantics:
-- when an exception is caught, the current state is kept.
test6 = hdlExThenSt progStEx  == (Right 2,2)

test7 = hdlExThenSt progStEx2  == (Right 0, 0)

-- Handling state before exception is rolling-back semantics:
-- if |p| throws an exception in |Catch p h|, then the state modification
-- in |p| will be discarded.
test8 = hdlStThenEx progStEx  == Right (1,1)

test9 = hdlStThenEx progStEx2 == Right (0,0)


-- * An example of an MCarrier that is not a functorial monad transformer
--

data Or k = Or k k deriving (Functor, Show)
data Once k = Once k deriving (Functor, Show)


-- This is a well-known non-example of a monad transformer
newtype ListC m a = LC { unLC :: m [a] }

instance MCarrier ListC where
  liftC :: Monad m => m x -> ListC m x
  liftC = LC . fmap (\x -> [x])

  fwd :: forall f g m . (Signature f g, Monad m) => Alg f g m -> Alg f g (ListC m)
  fwd (Alg {..}) = Alg call' enter' where
    call' :: forall x . f (ListC m x) -> ListC m x
    call' = LC . call . fmap unLC

    enter' :: forall x . g (ListC m (ListC m x)) -> ListC m x
    enter' = LC . seqL . tau1 enter . fmap (fmap (fmap unLC)) . fmap unLC
    -- Note that if we reverse the order of sequencing effects in |seqL|, |liftC| 
    -- is still a valid algebra homomorphism between |alg| and |fwd alg|.
    -- Thus there is no canonical instances of |MCarrier| in general.

seqL :: Monad m => m [m [a]] -> m [a]
seqL = fmap concat . join . fmap sequence

-- Note that seqL is not a valid |join| operation for monads to give a monadic
-- structure to |m [a]| since it is not associative, but it is not a problem
-- because the |handle| function has mandated the explicit substitutions in |Prog f g|
-- to be joined from bottom to up.

hNd :: MHandler Or Once ListC a [a]
hNd = MHandler (Alg call enter) unLC where
  call :: Monad m => Or (ListC m x) -> ListC m x
  call (Or l r) = LC $ 
    do x <- unLC l
       y <- unLC r
       return (x ++ y)

  enter :: Monad m => Once (ListC m (ListC m x)) -> ListC m x
  enter (Once c) = LC $
    do cs <- unLC c
       case cs of
         []     -> return []
         (c':_) -> unLC c'

-- Some tests

or :: (In Or f) => Prog f g x -> Prog f g x -> Prog f g x
or x y = Call (inj (Or x y))

once :: (Signature f g, In Once g) => Prog f g x -> Prog f g x
once p = Enter (inj (Once (fmap return p)))

pOnce :: (Signature f g, In Once g, In Or f) => Prog f g Int
pOnce = do x <- once (or (return 1) (return 5))
           or (return x) (return (x + 1))

test3 = (runEmpty (handle hNd pOnce)) == [1,2]

pOnceExc :: ( Signature f g, In Once g, In Or f
            , In (Throw ()) f, In (Catch ()) g)
         => Prog f g Int
pOnceExc = catch (do x <- once (or (return 1) (throw ()))
                     or (return x) (return (x + 1)))
                 (\() -> return 0)

hdlExThenNd :: Prog (Throw () :+: (Or :+: Empty)) (Catch () :+: (Once :+: Empty)) a
            -> [Either () a]
hdlExThenNd = runEmpty . handle hNd . handle hEx

hdlNdThenEx :: Prog (Or :+: (Throw () :+: Empty)) (Once :+: (Catch () :+: Empty)) a
            -> Either () [a]
hdlNdThenEx = runEmpty . handle hEx . handle hNd 

test4 = hdlExThenNd pOnceExc == [Right 1, Right 2]

-- If nondeterminism is handled first, then any effects handled afterwards
-- is global across nondeterministic branches, like nondeterminism is implemented
-- by backtracking.
test5 = hdlNdThenEx pOnceExc == Right [0]


-- * ListT done right vs ListC, aka ListT done wrong
--

-- ListT done right
newtype ListT m a = LT { unLT :: m (Maybe (a, ListT m a))} deriving Functor

deriving instance (Show a, forall x . Show x => Show (m x) ) => Show (ListT m a)

nilM :: Monad m => ListT m a
nilM = LT $ return Nothing

consM :: Monad m => a -> ListT m a -> ListT m a
consM x xs = LT $ return (Just (x, xs))

appM :: Monad m => ListT m a -> ListT m a -> ListT m a
appM (LT mxs) mys = LT $ mxs >>= (unLT . g) where
  g Nothing = mys
  g (Just (x, mxs')) = consM x (appM mxs' mys)

instance Monad m => Monad (ListT m) where
 return x = consM x nilM

 (LT m) >>= f = LT $ (m >>= g) where
   g Nothing = return Nothing
   g (Just (x, xs)) = unLT $ appM (f x) (xs >>= f)

  -- I hope I've done 'ListT done right' done right.
  
instance Monad m => Applicative (ListT m) where
  pure  = return
  (<*>) = ap

instance HFunctor ListT where
  hmap tau (LT m) = LT (fmap (fmap (fmap (hmap tau))) (tau m))

instance MonadTrans ListT where
  lift m = LT $ m >>= (\x -> unLT (consM x nilM))


runListT :: Monad m => ListT m a -> m [a]
runListT (LT m) = do x <- m
                     case x of
                       Nothing -> return []
                       (Just (x,m')) -> fmap (x:) (runListT m')

hNdLT :: MHandler Or Once ListT a [a]
hNdLT = MHandler (Alg call enter) runListT where

  call :: Monad m => Or (ListT m x) -> ListT m x
  call (Or l r) = appM l r

  enter :: Monad m => Once (ListT m (ListT m x)) -> ListT m x
  enter (Once c) = LT $
    do xs <- unLT c
       case xs of
         Nothing -> return Nothing
         (Just (x,_)) -> unLT x


-- Some tests. 

-- I expect |handle hNdLT| and |handle hNd| to have the exactly
-- same behaviour when nondeterminism is the *last* effect.

test3' = (runEmpty (handle hNdLT pOnce)) == [1,2]

hdlExThenNd' :: Prog (Throw () :+: (Or :+: Empty)) (Catch () :+: (Once :+: Empty)) a
             -> [Either () a]
hdlExThenNd' = runEmpty . handle hNdLT . handle hEx

hdlNdThenEx' :: Prog (Or :+: (Throw () :+: Empty)) (Once :+: (Catch () :+: Empty)) a
             -> Either () [a]
hdlNdThenEx' = runEmpty . handle hEx . handle hNdLT

-- pOnceExc = catch (do x <- once (or (return 1) (throw ()))
--                      or (return x) (return (x + 1)))
--                  (\() -> return 0)

test4' = hdlExThenNd' pOnceExc == [Right 1, Right 2]


-- In this case hNdLT and hNd behave differently.
-- With hNd, the result would be |Right [0]|
test5' = hdlNdThenEx' pOnceExc == Right [1,2]


-- |hdlNdThenEx'| results in a rather strange semantics of the interaction
-- between nondeterminism and other scoped operations: 
-- For example, if |scope| is a unary scoped operation handled after 
-- hNdLT, then
--   scope (a `or` b) == scope a `or` b
--
-- The cause of the problem is that the MCarrier instance of ListT
-- from FMonadTrans forwards a scoped operation in this way:
--     g' (ListT m (ListT m a)) 
--  ~= g' (m (Maybe (ListT m a, ListT m (ListT m a))))
--    fmap (fmap return)
--  -> g' (m (m (Maybe (ListT m a, ListT m (ListT m a)))))
--    enter
--  -> m (Maybe (ListT m a, ListT m (ListT m a)))
--  ~= ListT m (ListT m a)
--

pOrLocal ::  ( Signature f g, In Once g, In Or f
             , In (GetPut Integer) f, In (Local Integer) g )
          => Prog f g Integer
pOrLocal = do local (const 5) (or (put 1) (put 2))
              get
test10 = runEmpty (handle (hSt (0 :: Integer)) (handle hNdLT 
  pOrLocal))  == ([0,2],2)


pOnceExc' :: ( Signature f g, In Once g, In Or f
             , In (Throw ()) f, In (Catch ()) g )
          => Prog f g Int
pOnceExc' = catch (or (return 1) (throw ()))
                  (\() -> return 0)

test11 = hdlNdThenEx' pOnceExc' == Left ()

pOnceExc'' :: ( Signature f g, In Once g, In Or f
             , In (Throw ()) f, In (Catch ()) g )
           => Prog f g Int
pOnceExc'' = catch (or  (throw ()) (return 1) )
                   (\() -> return 0)

test12 = hdlNdThenEx' pOnceExc'' == Right [0]


-- * ListT done right done right:
-- The following we define a more natural MCarrier instance for 
-- ListT.

newtype ListT' m a = LT' { unLT' :: ListT m a } deriving Functor


-- unrunListT constructs a trivial |ListT| from a |m [a]| so 
-- runListT . unrunListT = id

unrunListT :: Monad m => m [a] -> ListT m a
unrunListT m = LT $ m >>= (foldr (\a as -> return (Just (a, LT as))) (return Nothing))

instance MCarrier ListT' where
  liftC :: Monad m => m a -> ListT' m a
  liftC x = LT' . LT $ fmap (\a -> Just (a, nilM)) x

  fwd   :: forall f g m . (Monad m, Signature f g) => Alg f g m -> Alg f g (ListT' m)
  fwd (Alg {..}) = Alg call' enter' where
    call' :: f (ListT' m a) -> ListT' m a
    call' = LT' . LT . call . fmap (unLT . unLT')

    enter' :: g (ListT' m (ListT' m a)) -> ListT' m a
    enter' = (LT' . join . fmap unLT') . unrunListT . tau1 enter . fmap (runListT . unLT')

-- The algebra of hNdLT' is the same as hNdLT
hNdLT' :: MHandler Or Once ListT' a [a]
hNdLT' = MHandler (Alg call enter) (runListT . unLT') where
  call (Or l r) = LT' (appM (unLT' l) (unLT' r))

  enter (Once c) = LT' . LT $
    do xs <- unLT (unLT' c)
       case xs of
         Nothing -> return Nothing
         (Just (x,_)) -> unLT (unLT' x)

-- Tests

hdlExThenNd'' :: Prog (Throw () :+: (Or :+: Empty)) (Catch () :+: (Once :+: Empty)) a
              -> [Either () a]
hdlExThenNd'' = runEmpty . handle hNdLT' . handle hEx

hdlNdThenEx'' :: Prog (Or :+: (Throw () :+: Empty)) (Once :+: (Catch () :+: Empty)) a
              -> Either () [a]
hdlNdThenEx'' = runEmpty . handle hEx . handle hNdLT'

test3'' = (runEmpty (handle hNdLT' pOnce)) == [1,2]

test4'' = hdlExThenNd' pOnceExc == [Right 1, Right 2]

test5'' = hdlNdThenEx' pOnceExc == Right [1,2]

-- This test case is different from hNdLT
test11' = hdlNdThenEx'' pOnceExc'  == Right [0]

test12' = hdlNdThenEx'' pOnceExc'' == Right [0]

-- In summary: 
--  * hNd sequences nonderministic branches inside all scoped operations including
--      thoses unhandled and |once|
--  * hNdLT' sequences nondeterministic branches insides unhandled operations but
--      keeps the branching structure in |once|
--  * hNdLT always keeps the branching structure but an unhandled scoped operation 
--      encloses only the first branch of nondeterminism
--
-- The following program highlights the differences of these handlers.

pOnceCatch :: ( Signature f g, In Once g, In Or f
              , In (Throw ()) f, In (Catch ()) g )
           => Prog f g (Integer, Integer)
pOnceCatch = 
 do x <- once (catch (or (return 1) (throw ())) 
                     (\() -> return 2))
    y <- catch (or (return 3) (throw ())) 
               (\() -> return 4)
    return (x, y)

test13 = (hdlNdThenEx pOnceCatch == Right [(2, 4)])          
             -- the first throw is executed
 
           && (hdlNdThenEx' pOnceCatch == Left ())          
             -- the second throw isn't caught

           && (hdlNdThenEx'' pOnceCatch == Right [(2,4)])    
             -- the first throw is executed

           && (hdlExThenNd pOnceCatch == [Right (1,3), Right (1,4)]) 
              -- the first throw isn't executed and the second throw is caught,
              -- which I think is the most intuitive semantics.

mytest :: ( Signature f g, In Once g, In Or f , In (Throw ()) f, In (Catch ()) g )
           => Prog f g Integer
mytest = do y <- catch (or (return 3) (throw ()))
                       (\() -> return 4)
            return y

t = hdlNdThenEx mytest

-- * Another example: concurrency with asynchronous message passing.
-- The idea of encoding concurrency with scoped operations are examined in Nick
-- and Tom's Haskell14 and LICS18 papers.
-- Danel Ahman and Matija Pretnar's paper _Asynchronous Effects_ further identifies
-- asynchronous message passing as scoped operations.

data Send k = Send Integer k | Kill deriving Functor
data Con k = Spawn k k | Receive (Integer -> k) deriving Functor

-- Terminating the current processing
kill :: (Signature f g, In Send f) => Prog f g a
kill = Call (inj Kill)

-- Broadcasting an integer to all other processes
send :: (Signature f g, In Send f) => Integer -> Prog f g ()
send i = Call (inj (Send i (return ())))

-- Creating a new process that runs the second argument concurrently
spawn :: (Signature f g, In Con g, In Send f) => Prog f g a -> Prog f g b -> Prog f g a
spawn p q = Enter (inj (fmap (fmap return) (Spawn p (q >> kill))))

{- Not working yet: what is |Promise|?

-- Installing an asynchronous message handler |hdl| and runs |p| (non-blockingly).
recv :: (Signature f g, In Con g) => (Integer -> Prog f g a) -> (Promise a -> Prog f g b) -> Prog f g b
recv hdl p = Enter (inj (Receive (fmap p . hdl)))

await :: (Signature f g, In Con g) => Promise a -> (a -> Prog f g b) -> Prog f g b
await = undefined
-}

{-
-- If we try to eliminate the |Promise| type (and |await|) then we obtain an operation that
-- isn't an scoped operations.

-- The |Prog f g a| argument to |p| stands for forcing the promise and awaiting |hdl| to complete.

recv :: (Signature f g, In Con g) => (Integer -> Prog f g a) -> (Prog f g a -> Prog f g b) -> Prog f g b
recv hdl p = undefined
-}


-- * Connections with |weave|
--
-- So far we have only considered signatures of algebraic and scoped operations, 
-- but the approach of modular carriers is not limited to them. 
-- In the following we reformulate the techniques in the Effect Handlers in Scope
-- paper (Haskell 14) as a 'generalised state monad transformer' that can
-- forward any higher-order signature functors with |weave|. 


type Kl m a b = a -> m b

type Distr s m n = forall x . s (m x) -> n (s x)

class HFunctor sig => Weavable (sig :: (* -> *) -> (* -> *)) where
  emap :: Monad m => Kl m a b -> sig m a -> sig m b
  
  weave :: (Monad m, Monad n, Functor s) => s () -> Distr s m n -> (sig m a -> sig n (s a))


-- Generalised state monad transformer: the mutable state is generalised from a 
-- fixed type to a functor |s :: * -> *| that allows a stateful computation
-- to be run in a |s|-context by the |feed| function.
--
-- It's still unclear to me what's the best categorical interpretation for this.
-- 
newtype GStateT s m a = GST { runGST :: s () -> m (s a) }

-- c :: (* -> *) -> (* -> *)
-- fwd :: ... => (sig m -.> m) -> (sig (c m) -.> c m)
-- Goal: find |s| s.t. GStateT s ~= c
--
-- StateT st m a ~= st -> m (st, a)
-- fwd = ...
--   Let s = (st, )
--
-- 

-- When |s| is |(st, )| this instantiates to the standard state monad transformer
class Functor s => StateLike s where
  feed :: Monad m => s (GStateT s m a) -> m (s a)
    -- s (s () -> m (s a)) -> m (s a)
    --
    -- F = s . (s () -> _)

-- The Haskell 14 paper 
instance StateLike ((,) st) where
  -- feed :: (st, (st, ()) -> m (st, a)) -> m (st, a)
  feed (st, c) = runGST c (st, ())

-- The exception handler in the Haskell 14 paper uses the GStateT from 
-- |Either e|.
instance StateLike (Either e) where
  feed :: Monad m => Either e (GStateT (Either e) m a) -> m (Either e a)
  feed (Left e)  = return (Left e)
  feed (Right c) = runGST c (Right ())

-- The familiar MonadTrans instance of StateT generalises to GStateT
instance (StateLike s) => MonadTrans (GStateT s) where
  lift m = GST (\s -> m >>= (\x -> return (fmap (const x) s)))

instance (StateLike s, Monad m) => Monad (GStateT s m) where
  return x = GST (\s -> return (fmap (const x) s))

  c >>= f = GST $ \s ->
    do x <- runGST c s
       feed (fmap f x)

instance (StateLike s, Monad m) => Applicative (GStateT s m) where 
  pure  = return
  (<*>) = ap

instance (StateLike s, Monad m) => Functor (GStateT s m) where 
  fmap = liftM

-- |GStateT s| can forward any weavable higher-order signature 

liftCGStateT :: (StateLike s, Monad m) => m x -> GStateT s m x
liftCGStateT = lift

--  weave :: (Monad m, Monad n, Functor s) => s () -> Distr s m n -> (sig m a -> sig n (s a))

fwdGStateT :: forall sig m s . (Weavable sig, Monad m, StateLike s) 
           => (sig m -.> m) -> (sig (GStateT s m) -.> GStateT s m)
fwdGStateT alg op = GST $ \ (s0 :: s ()) -> alg (weave s0 distr op) where
  distr :: forall x . s (GStateT s m x) -> m (s x)
  distr = feed
  
-- Question: under what conditions |liftCGStateT| is an |sig|-algebra homomorphism
-- between |alg| and |fwdGStateT alg|.

