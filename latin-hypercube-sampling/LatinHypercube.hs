{-# OPTIONS_GHC -Wall #-}
module LatinHypercube where

import Control.Monad
import Control.Monad.Primitive
import qualified Data.Vector as V
import qualified Data.Vector.Generic as VG
import qualified System.Random.MWC as MWC
import qualified System.Random.MWC.Distributions as MWC
import qualified System.Random.Stateful as Rand

-- | Latin hypercube sampling
--
-- References
--
-- * <https://en.m.wikipedia.org/wiki/Latin_hypercube_sampling>
--
-- * <https://github.com/uber-research/TuRBO/blob/de0db39f481d9505bb3610b7b7aa0ebf7702e4a5/turbo/utils.py>
latinHypercube
  :: forall g m v. (Rand.StatefulGen g m, PrimMonad m, VG.Vector v Double)
  => Int -- ^ Dimentions
  -> Int -- ^ Number of samples
  -> g   -- ^ Generator
  -> m [v Double]
latinHypercube dim m g = do
  let centers = VG.fromList $ map ((/ (2 * fromIntegral m)) . fromIntegral) [1, 3 .. 2*m-1]
  xss <- replicateM dim $ do
    xs <- MWC.uniformShuffle centers g
    ys <- VG.replicateM m $ Rand.uniformRM (- 1 / (2 * fromIntegral m), 1 / (2 * fromIntegral m)) g
    pure $ (VG.zipWith (+) xs ys :: v Double)
  pure [VG.fromListN dim [xs VG.! i | xs <- xss] | i <- [0..m-1]]


test :: IO ()
test = do
  g <- MWC.createSystemRandom
  xs <- latinHypercube 2 5 g
  print (xs :: [V.Vector Double])
