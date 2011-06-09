{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

import Control.Applicative
import Control.Monad
import Control.Monad.ST
import Data.STRef
import Data.Monoid as Monoid

data RVal s a = RVal (STRef s a)
              | Con a
              | Oper (RIO s a)

instance Functor (RVal s) where
  f `fmap` x = Oper $ do x' <- peekV x
                         return $ f x'

instance Applicative (RVal s) where
  pure = Con
  f <*> b = Oper $ do f' <- peekV f
                      b' <- peekV b
                      return $ f' b'

class RValue v s a where
  value :: v s a -> RIO s a

instance RValue RVal s a where
  value = peekV

con :: a -> RVal s a
con = Con

mkV :: a -> RIO s (RVal s a)
mkV v = RVal <$> newSTRef v

peekV :: RVal s a -> RIO s a
peekV (RVal v) = readSTRef v
peekV (Con a) = return a
peekV (Oper m) = m

writeV :: RVal s a -> a -> RIO s ()
writeV (RVal v) = writeSTRef v

data R s = RReturn
         | forall a.Swap (RVal s a) (RVal s a) (R s)
         | Cond (RVal s Bool) (R s) (R s) (RVal s Bool) (R s)
         | forall a b.Binop (a->b->a) (a->b->a) (RVal s a) (RVal s b) (R s)
         | forall a.Rlet a (RVal s a -> R s) (R s)

type RIO s = ST s

runRIO :: (forall s. ST s a) -> a
runRIO = runST

-- R functions
instance Monoid (R s) where
    mempty = RReturn
    mappend RReturn u = u
    mappend (Swap x y u) u' = Swap x y (mappend u u')
    mappend (Cond pre f1 f2 post u') u'' = Cond pre f1 f2 post (mappend u' u'')
    mappend (Binop f finv x y u') u'' = Binop f finv x y (mappend u' u'')
    mappend (Rlet x f u) u' = Rlet x f (mappend u u')

skip :: R s
skip = RReturn

infix 2 <=>
(<=>) :: (RVal s a) -> (RVal s a) -> R s
x <=> y = Swap x y RReturn

cond :: RVal s Bool -> R s -> R s -> RVal s Bool -> R s
cond pre f1 f2 post = Cond pre f1 f2 post RReturn

binop :: (a->b->a) -> (a->b->a) -> RVal s a -> RVal s b -> R s
binop f finv x y = Binop f finv x y RReturn

infix 2 +=
(+=) :: RVal s Integer -> RVal s Integer -> R s
v1 += v2 = binop (+) (-) v1 v2

infix 2 -=
(-=) :: RVal s Integer -> RVal s Integer -> R s
v1 -= v2 = binop (-) (+) v1 v2

infixr 1 !>
(!>) :: R s -> R s -> R s
(!>) = mappend

rlet :: a -> (RVal s a -> R s) -> R s
rlet x f = Rlet x f RReturn

rev :: R s -> R s
rev RReturn = RReturn
rev (Swap x y u) = rev u !> x <=> y
rev (Cond pre f1 f2 post u) = rev u !> cond post (rev f1) (rev f2) pre
rev (Binop f finv x y u) = rev u !> binop finv f x y
rev (Rlet x f u) = rev u !> rlet x (rev . f)

applyR :: R s -> RIO s ()
applyR RReturn = return ()
applyR (Cond pre f1 f2 _ u) = do pre' <- peekV pre
                                 applyR $ if pre' then f1 else f2
                                 applyR u
applyR (Swap rx ry u) = do x <- peekV rx
                           y <- peekV ry
                           writeV rx y
                           writeV ry x
                           applyR u
applyR (Binop f _ v1 v2 u) = do writeV v1 =<< liftM2 f (peekV v1) (peekV v2)
                                applyR u
applyR (Rlet x f u) = do applyR =<< (f <$> mkV x)
                         applyR u

fibf :: RVal s Integer -> RVal s Integer -> RVal s Integer -> R s
fibf rn rx1 rx2 =
  cond (liftA (==0) rn)
  (rx1 += con 1 !>
   rx2 += con 1)
  (rn -= con 1 !>
   fibf rn rx1 rx2 !>
   rx1 += rx2 !>
   rx1 <=> rx2)
  (liftA2 (==) rx1 rx2)

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
  applyR $ rev $ fibf rn rx1 rx2
  peekV rn
