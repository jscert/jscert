module ResultsDB where

import Database.HDBC.Sqlite3(connectSqlite3,Connection)
import System.Environment
import System.FilePath((</>),(<.>),takeDirectory)
import System.Directory

dbPath :: IO FilePath
dbPath = do
  dir <- getCurrentDirectory
  username <- getEnv "USER"
  return $ (takeDirectory dir) </> username<.>"db"

getConnection :: IO Connection
getConnection = connectSqlite3 =<< dbPath
