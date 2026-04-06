{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wall -Wno-name-shadowing #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  LinearContinuationMonad
--
-- Linear continuation monads.
--
-- Delimited continuation operators are taken from Kenichi Asai and Oleg
-- Kiselyov's tutorial at CW 2011, \"Introduction to programming with
-- shift and reset\" (<http://okmij.org/ftp/continuations/#tutorial>).
--
-- Most of the code is copied and modified from Control.Monad.Trans.Cont
-- module of transformers-0.6.3.0.
--
-----------------------------------------------------------------------------
module LinearContinuationMonad (
    -- * The Cont monad
    Cont,
    cont,
    runCont,
    evalCont,
    mapCont,
    withCont,
    -- ** Delimited continuations
    reset, shift,
    -- * The ContT monad transformer
    ContT(..),
    runContT,
    evalContT,
    mapContT,
    withContT,
    -- ** Delimited continuations
    resetT, shiftT,
  ) where

import Prelude.Linear
import Control.Functor.Linear
import Control.Monad.IO.Class.Linear
import Data.Functor.Identity hiding (runIdentity)
import qualified Data.Functor.Linear as Data
import GHC.Generics

runIdentity :: Identity x %1 -> x
runIdentity (Identity x) = x
{-# INLINE runIdentity #-}

{- |
The continuation monad, which is non-strict.
@Cont r a@ is a CPS ("continuation-passing style") computation that produces an
intermediate result of type @a@ within a CPS computation whose final result type
is @r@.

The @return@ function simply creates a continuation which passes the value on.

The @>>=@ operator adds the bound function into the continuation chain.
-}
type Cont r = ContT r Identity

-- | Construct a continuation-passing computation from a function.
-- (The inverse of 'runCont')
cont :: ((a %1 -> r) %1 -> r) %1 -> Cont r a
cont f = ContT (\ c -> Identity (f (runIdentity . c)))
{-# INLINE cont #-}

-- | The result of running a CPS computation with a given final continuation.
-- (The inverse of 'cont')
runCont
    :: Cont r a         -- ^ continuation computation (@Cont@).
    %1 -> (a %1 -> r)   -- ^ the final continuation, which produces
                        -- the final result (often 'id').
    %1 -> r
runCont m k = runIdentity (runContT m (Identity . k))
{-# INLINE runCont #-}

-- | The result of running a CPS computation with the identity as the
-- final continuation.
--
-- * @'evalCont' ('return' x) = x@
evalCont :: Cont r r %1 -> r
evalCont m = runIdentity (evalContT m)
{-# INLINE evalCont #-}

-- | Apply a function to transform the result of a continuation-passing
-- computation.
--
-- * @'runCont' ('mapCont' f m) = f . 'runCont' m@
mapCont :: (r %1 -> r) %1 -> Cont r a %1 -> Cont r a
mapCont f = mapContT (Identity . f . runIdentity)
{-# INLINE mapCont #-}

-- | Apply a function to transform the continuation passed to a CPS
-- computation.
--
-- * @'runCont' ('withCont' f m) = 'runCont' m . f@
withCont :: ((b %1 -> r) %1 -> (a %1 -> r)) %1 -> Cont r a %1 -> Cont r b
withCont f = withContT ((Identity .) . f . (runIdentity .))
{-# INLINE withCont #-}

-- | @'reset' m@ delimits the continuation of any 'shift' inside @m@.
--
-- * @'reset' ('return' m) = 'return' m@
--
reset :: Cont r r %1 -> Cont r' r
reset = resetT
{-# INLINE reset #-}

-- | @'shift' f@ captures the continuation up to the nearest enclosing
-- 'reset' and passes it to @f@:
--
-- * @'reset' ('shift' f >>= k) = 'reset' (f ('evalCont' . k))@
--
shift :: ((a %1 -> r) %1 -> Cont r r) %1 -> Cont r a
shift f = shiftT (f . (runIdentity .))
{-# INLINE shift #-}

-- | The continuation monad transformer.
-- Can be used to add continuation handling to any type constructor:
-- the 'Monad' instance and most of the operations do not require @m@
-- to be a monad.
--
-- 'ContT' is not a functor on the category of monads, and many operations
-- cannot be lifted through it.
--
-- @ContT r m@ is strict if and only if @m@ is.
newtype ContT r m a = ContT ((a %1 -> m r) %1 -> m r)
    deriving (Generic)

runContT :: ContT r m a %1 -> (a %1 -> m r) %1 -> m r
runContT (ContT m) = m
{-# INLINE runContT #-}

-- | The result of running a CPS computation with 'return' as the
-- final continuation.
--
-- * @'evalContT' ('lift' m) = m@
evalContT :: (Monad m) => ContT r m r %1 -> m r
evalContT m = runContT m return
{-# INLINE evalContT #-}

-- | Apply a function to transform the result of a continuation-passing
-- computation.  This has a more restricted type than the @map@ operations
-- for other monad transformers, because 'ContT' does not define a functor
-- in the category of monads.
--
-- * @'runContT' ('mapContT' f m) = f . 'runContT' m@
mapContT :: (m r %1 -> m r) %1 -> ContT r m a %1 -> ContT r m a
mapContT f m = ContT $ f . runContT m
{-# INLINE mapContT #-}

-- | Apply a function to transform the continuation passed to a CPS
-- computation.
--
-- * @'runContT' ('withContT' f m) = 'runContT' m . f@
withContT :: ((b %1 -> m r) %1 -> (a %1 -> m r)) %1 -> ContT r m a %1 -> ContT r m b
withContT f m = ContT $ runContT m . f
{-# INLINE withContT #-}

instance Data.Functor (ContT r m) where
  fmap f m = ContT $ \ c -> runContT m (c . f)
  {-# INLINE fmap #-}

instance Functor (ContT r m) where
  fmap f m = ContT $ \ c -> runContT m (c . f)
  {-# INLINE fmap #-}

instance Data.Applicative (ContT r m) where
  pure x  = ContT ($ x)
  {-# INLINE pure #-}
  f <*> v = ContT $ \ c -> runContT f $ \ g -> runContT v (c . g)
  {-# INLINE (<*>) #-}

instance Applicative (ContT r m) where
  pure x  = ContT ($ x)
  {-# INLINE pure #-}
  f <*> v = ContT $ \ c -> runContT f $ \ g -> runContT v (c . g)
  {-# INLINE (<*>) #-}

instance Monad (ContT r m) where
  m >>= k  = ContT $ \ c -> runContT m (\ x -> runContT (k x) c)
  {-# INLINE (>>=) #-}

instance MonadTrans (ContT r) where
  lift m = ContT (\k -> m >>= k)
  {-# INLINE lift #-}

instance (MonadIO m) => MonadIO (ContT r m) where
    liftIO = lift . liftIO
    {-# INLINE liftIO #-}

-- | @'resetT' m@ delimits the continuation of any 'shiftT' inside @m@.
--
-- * @'resetT' ('lift' m) = 'lift' m@
--
resetT :: (Monad m) => ContT r m r %1 -> ContT r' m r
resetT = lift . evalContT

-- | @'shiftT' f@ captures the continuation up to the nearest enclosing
-- 'resetT' and passes it to @f@:
--
-- * @'resetT' ('shiftT' f >>= k) = 'resetT' (f ('evalContT' . k))@
--
shiftT :: (Monad m) => ((a %1 -> m r) %1 -> ContT r m r) %1 -> ContT r m a
shiftT f = ContT (evalContT . f)
