-- イロレーティング (Elo rating)
-- https://ja.wikipedia.org/wiki/%E3%82%A4%E3%83%AD%E3%83%AC%E3%83%BC%E3%83%86%E3%82%A3%E3%83%B3%E3%82%B0
module EloRating where

import Data.Default.Class

type Rating = Double

data Setting
  = Setting
  { averageRating :: Rating
  , scalingFactor :: Double
  , kFactor :: Double
  }

instance Default Setting where
  def = Setting
    { averageRating = 1500
    , scalingFactor = 400
    , kFactor = 32
    }

winProbability :: Setting -> Rating -> Rating -> Double
winProbability setting r1 r2 = recip $ 10 ** ((r2 - r1) / scalingFactor setting) + 1

updateRating :: Setting -> Rating -> Double -> Int -> Int -> Rating
updateRating setting r w numGames numWins = r + kFactor setting * (fromIntegral numWins - fromIntegral numGames * w)

updateRating1 :: Setting -> Rating -> Double -> Bool -> Rating
updateRating1 setting r w1 win = r + kFactor setting * (if win then w2 else - w1)
  where
    w2 = 1 - w1

_test1 = winProbability def 200 100
-- 0.6400649998028851

_test2 = updateRating1 setting r1 w1 True
-- 1524.3119016527346
  where
    setting = def
    r1 = 1500
    r2 = 1700
    w1 = winProbability setting r1 r2
    w2 = 1 - w1

_test2' = updateRating1 setting r2 w2 False
-- 1675.6880983472654
  where
    setting = def
    r1 = 1500
    r2 = 1700
    w1 = winProbability setting r1 r2
    w2 = 1 - w1
