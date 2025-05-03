import Control.Concurrent
import Control.Exception
import System.Process

main :: IO ()
main = do
  print =<< getCurrentPid
  handle (\(e :: AsyncException) -> print e) (threadDelay (maxBound :: Int))
