module ResultsDB where

import Database.HDBC.Sqlite3(connectSqlite3,Connection)
import System.Environment
import System.FilePath((</>),(<.>))

dbPath :: IO FilePath
dbPath = do
  username <- getEnv "USER"
  return $ "test_data"</>username<.>"db"

getConnection :: IO Connection
getConnection = connectSqlite3 =<< dbPath
