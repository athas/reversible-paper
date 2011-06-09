{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Reversible ( RVar,
                    RVal(..),
                    RComp,
                    R,
                    RIO,
                    (!),
                    mkV,
                    con,
                    runRIO,
                    applyR,
                    rev,
                    (!>),
                    (+=),
                    (-=),
                    (^=),
                    cond,
                    rlet,
                    skip,
                    (<=>)
  )
  where

import Control.Applicative
import Control.Monad
import Control.Monad.ST
import Data.Bits
import Data.STRef
import Data.Monoid as Monoid

class RVal v s a where
  value :: v s a -> RIO s a

newtype RComp s a = RComp (RIO s a)

instance RVal RComp s a where
  value (RComp c) = c

infixl 1 !
(!) :: (RVal v1 s (a -> b), RVal v2 s a) => v1 s (a -> b) -> v2 s a -> RComp s b
a ! b = RComp $ value a `ap` value b

con :: a -> RComp s a
con = RComp . return

newtype RVar s a = RVar (STRef s a)

mkV :: a -> RIO s (RVar s a)
mkV v = RVar <$> newSTRef v

instance RVal RVar s a where
  value (RVar v) = readSTRef v

writeV :: RVar s a -> a -> RIO s ()
writeV (RVar v) = writeSTRef v

data R s = RReturn
         | forall a.Swap (RVar s a) (RVar s a) (R s)
         | forall v1 v2.(RVal v1 s Bool, RVal v2 s Bool) =>
           Cond (v1 s Bool) (R s) (R s) (v2 s Bool) (R s)
         | forall a b v.RVal v s b=>Binop (a->b->a) (a->b->a) (RVar s a) (v s b) (R s)
         | forall a.Rlet a (RVar s a -> R s) (R s)

type RIO s = ST s

runRIO :: (forall s. ST s a) -> a
runRIO = runST

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
(<=>) :: RVar s a -> RVar s a -> R s
x <=> y = Swap x y RReturn

cond :: forall s v1 v2.(RVal v1 s Bool, RVal v2 s Bool) =>
        v1 s Bool -> R s -> R s -> v2 s Bool -> R s
cond pre f1 f2 post = Cond pre f1 f2 post RReturn

binop :: forall a b v s.RVal v s b => (a->b->a) -> (a->b->a) -> RVar s a
      -> v s b -> R s
binop f finv x y = Binop f finv x y RReturn

infix 2 +=
(+=) :: forall v s a. Num a => RVal v s a => RVar s a -> v s a -> R s
v1 += v2 = binop (+) (-) v1 v2

infix 2 -=
(-=) :: forall v s a. Num a => RVal v s a => RVar s a -> v s a -> R s
v1 -= v2 = binop (-) (+) v1 v2

infix 2 ^=
(^=) :: forall v s a.Bits a => RVal v s a => RVar s a -> v s a -> R s
v1 ^= v2 = binop xor xor v1 v2

infixr 1 !>
(!>) :: R s -> R s -> R s
(!>) = mappend

rlet :: a -> (RVar s a -> R s) -> R s
rlet x f = Rlet x f RReturn

rev :: R s -> R s
rev RReturn = RReturn
rev (Swap x y u) = rev u !> x <=> y
rev (Cond pre f1 f2 post u) = rev u !> cond post (rev f1) (rev f2) pre
rev (Binop f finv x y u) = rev u !> binop finv f x y
rev (Rlet x f u) = rev u !> rlet x (rev . f)

applyR :: R s -> RIO s ()
applyR RReturn = return ()
applyR (Cond pre f1 f2 _ u) = do pre' <- value pre
                                 applyR $ if pre' then f1 else f2
                                 applyR u
applyR (Swap rx ry u) = do x <- value rx
                           y <- value ry
                           writeV rx y
                           writeV ry x
                           applyR u
applyR (Binop f _ v1 v2 u) = do writeV v1 =<< liftM2 f (value v1) (value v2)
                                applyR u
applyR (Rlet x f u) = do applyR =<< (f <$> mkV x)
                         applyR u
