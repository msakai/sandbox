import Codec.Archive.Zip
import System.Environment (getArgs)
import qualified Data.Map as M

main :: IO ()
main = do
  [path]  <- getArgs
  entries <- withArchive path (M.keys <$> getEntries)
  mapM_ print entries
