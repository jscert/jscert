module ResultsDB where

import Database.HDBC.Sqlite3(connectSqlite3,Connection)
import System.Environment
import System.FilePath((</>),(<.>),takeDirectory)
import System.Directory

strPASS :: String
strPASS = "PASS"
strFAIL :: String
strFAIL = "FAIL"
strABORT :: String
strABORT = "ABORT"

dbPathFromQueries :: IO FilePath
dbPathFromQueries = do
  dir <- getCurrentDirectory
  username <- getEnv "USER"
  return $ (takeDirectory dir) </> username<.>"db"

dbPathFromTrunk :: IO FilePath
dbPathFromTrunk = do
  username <- getEnv "USER"
  return $ "test_data"</>username<.>"db"


getConnectionFromQueries :: IO Connection
getConnectionFromQueries = connectSqlite3 =<< dbPathFromQueries

getConnectionFromTrunk :: IO Connection
getConnectionFromTrunk = connectSqlite3 =<< dbPathFromTrunk
