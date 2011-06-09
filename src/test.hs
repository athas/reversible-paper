import Reversible

fibf :: RVar s Integer -> RVar s Integer -> RVar s Integer -> R s
fibf rn rx1 rx2 =
  cond (con (==0) ! rn)
  (rx1 += con 1 !> rx2 += con 1)
  (rn -= con 1 !>
   fibf rn rx1 rx2 !>
   rx1 += rx2 !>
   rx1 <=> rx2)
  (con (==) ! rx1 ! rx2)

test :: Integer -> RIO s (Integer, Integer)
test n = do
  rn  <- mkV n
  rx1 <- mkV 0
  rx2 <- mkV 0
  applyR $ fibf rn rx1 rx2
  v1 <- value rx1
  v2 <- value rx2
  return (v1,v2)

test2 :: Integer -> Integer -> RIO s Integer
test2 x1 x2 = do
  rx1 <- mkV x1
  rx2 <- mkV x2
  rn <- mkV 0
  applyR $ rev $ fibf rn rx1 rx2
  value rn
