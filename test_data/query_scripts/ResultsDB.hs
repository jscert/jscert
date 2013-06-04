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

dbPath :: IO FilePath
dbPath = do
  dir <- getCurrentDirectory
  username <- getEnv "USER"
  return $ (takeDirectory dir) </> username<.>"db"

getConnection :: IO Connection
getConnection = connectSqlite3 =<< dbPath
