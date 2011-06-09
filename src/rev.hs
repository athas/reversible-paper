{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}

import Debug.Trace

import Control.Applicative
import Control.Monad
import Control.Monad.ST
import Data.STRef
import Data.Monoid as Monoid
import Complex


data RV s a = RV (STRef s a)
            | Con a

con :: a -> RV s a
con = Con

mkV :: a -> RIO s (RV s a)
mkV v = RV <$> newSTRef v

peekV :: RV s a -> RIO s a
peekV (RV v) = readSTRef v
peekV (Con a) = return a

writeV :: RV s a -> a -> RIO s ()
writeV (RV v) = writeSTRef v

newtype RC s a = RC { unRC :: RIO s a } deriving (Functor)

instance Applicative (RC s) where
  pure = RC . return
  RC f <*> RC b = RC $ f `ap` b

val :: RV s a -> RC s a
val = RC . peekV

-- QIO and U as traces
data R s = RReturn
         | forall a.Swap (RV s a) (RV s a) (R s)
         | Cond (RC s Bool) (R s) (R s) (RC s Bool) (R s)
         | Inc (RV s Integer) (RV s Integer) (R s)
         | Dec (RV s Integer) (RV s Integer) (R s)
--         | Rlet Bool (Qbit -> R) R

type RIO s = ST s

runRIO :: (forall s. ST s a) -> a
runRIO = runST

-- R functions
instance Monoid (R s) where
    mempty = RReturn
    mappend RReturn u = u
    mappend (Swap x y u) u' = Swap x y (mappend u u')
    mappend (Cond pre f1 f2 post u') u'' = Cond pre f1 f2 post (mappend u' u'')
    mappend (Inc v1 v2 u') u'' = Inc v1 v2 (mappend u' u'')
    mappend (Dec v1 v2 u') u'' = Dec v1 v2 (mappend u' u'')
--    mappend (Rlet b f u) u' = Rlet b f (mappend u u')

skip :: R s
skip = RReturn

swap :: (RV s a) -> (RV s a) -> R s
swap x y = Swap x y RReturn

cond :: RC s Bool -> R s -> R s -> RC s Bool -> R s
cond pre f1 f2 post = Cond pre f1 f2 post RReturn

inc :: RV s Integer -> RV s Integer -> R s
inc v1 v2 = Inc v1 v2 RReturn

dec :: RV s Integer -> RV s Integer -> R s
dec v1 v2 = Dec v1 v2 RReturn

--ulet :: Bool -> (Qbit -> R) -> R
--ulet b ux = Rlet b ux RReturn

urev :: R s -> R s
urev RReturn = RReturn
urev (Swap x y u) = urev u `mappend` swap x y
urev (Cond pre f1 f2 post u) = urev u `mappend` cond post (urev f1) (urev f2) pre
urev (Inc v1 v2 u) = urev u `mappend` dec v1 v2
urev (Dec v1 v2 u) = urev u `mappend` inc v1 v2
--urev (Rlet b xu u) = urev u `mappend` ulet b (urev.xu)

applyR :: R s -> RIO s ()
applyR RReturn = return ()
applyR (Cond pre f1 f2 _ u) = do pre' <- unRC pre
                                 applyR $ if pre' then f1 else f2
                                 applyR u
applyR (Swap rx ry u) = do x <- peekV rx
                           y <- peekV ry
                           writeV rx y
                           writeV ry x
                           applyR u
applyR (Inc v1 v2 u) = do v1' <- peekV v1
                          v2' <- peekV v2
                          writeV v1 (v1'+v2')
                          applyR u
applyR (Dec v1 v2 u) = do v1' <- peekV v1
                          v2' <- peekV v2
                          writeV v1 (v1'-v2')
                          applyR u

fibf :: RV s Integer -> RV s Integer -> RV s Integer -> R s
fibf rn rx1 rx2 =
  cond (pure (==0) <*> val rn)
  (inc rx1 (con 1) `mappend` inc rx2 (con 1))
  (dec rn (con 1) `mappend` fibf rn rx1 rx2
   `mappend` inc rx1 rx2 `mappend` swap rx1 rx2)
  (pure (==) <*> val rx1 <*> val rx2)

test :: Integer -> RIO s (Integer, Integer)
test n = do
  rn  <- mkV n
  rx1 <- mkV 0
  rx2 <- mkV 0
  applyR $ fibf rn rx1 rx2
  v1 <- peekV rx1
  v2 <- peekV rx2
  return (v1,v2)

test2 :: Integer -> Integer -> RIO s Integer
test2 x1 x2 = do
  rx1 <- mkV x1
  rx2 <- mkV x2
  rn <- mkV 0
  applyR $ urev $ fibf rn rx1 rx2
  peekV rn
