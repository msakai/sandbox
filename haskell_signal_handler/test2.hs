import Control.Concurrent
import Control.Exception
import System.Posix.Signals
import System.Process

main :: IO ()
main = do
  print =<< getCurrentPid
  mainThread <- myThreadId
  installHandler sigTERM (Catch (throwTo mainThread UserInterrupt)) Nothing
  handle (\(e :: AsyncException) -> print e) (threadDelay (maxBound :: Int))
