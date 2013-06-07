module ResultsDB where

import Database.HDBC.Sqlite3(connectSqlite3,Connection)
import Database.HDBC(prepare,toSql,execute,fromSql,fetchRow)
import Data.Maybe(fromJust)
import System.Environment
import System.FilePath((</>),(<.>),takeDirectory)
import System.Directory
import Data.List(transpose)

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

stmtMakeGroup :: String
stmtMakeGroup = "INSERT INTO test_groups (description) VALUES (?)"

stmtAddFileToGroup :: String
stmtAddFileToGroup = "INSERT INTO test_group_memberships (group_id,test_id) VALUES (?,?)"

stmtGetLatestGroup :: String
stmtGetLatestGroup = "SELECT id from test_groups ORDER BY id DESC"

-- Returns the ID of the group we created
makeGroup :: String -> Connection -> IO Int
makeGroup desc con = do
      mkstmt <- prepare con stmtMakeGroup
      execute mkstmt [toSql desc]
      getstmt <- prepare con stmtGetLatestGroup
      execute getstmt []
      fmap (fromSql.head.fromJust) $ fetchRow getstmt

addFilesToGroup :: Int -> [String] -> Connection -> IO ()
addFilesToGroup gid tids con = do
  stmt <- prepare con stmtAddFileToGroup
  let stmtargs = transpose [replicate (length tids) (toSql gid) , map toSql tids]
  mapM_ (execute stmt) stmtargs
