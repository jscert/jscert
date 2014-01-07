{-# LANGUAGE ScopedTypeVariables #-}

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
  return $ takeDirectory dir </> username<.>"db"

dbPathFromTrunk :: IO FilePath
dbPathFromTrunk = return $ "test_data" </> "test_results" <.> "db"

getConnectionFromQueries :: IO Connection
getConnectionFromQueries = connectSqlite3 =<< dbPathFromQueries

getConnectionFromTrunk :: IO Connection
getConnectionFromTrunk = connectSqlite3 =<< dbPathFromTrunk

stmtMakeGroup :: String
stmtMakeGroup = "INSERT INTO test_groups (description) VALUES (?)"

stmtMakeFailGroup :: String
stmtMakeFailGroup = "INSERT INTO fail_groups (batch_id,description,reason) VALUES (?,?,?)"

stmtAddFileToGroup :: String
stmtAddFileToGroup = "INSERT INTO test_group_memberships (group_id,test_id) VALUES (?,?)"

stmtAddFileToFailGroup :: String
stmtAddFileToFailGroup = "INSERT INTO fail_group_memberships (group_id,test_id) VALUES (?,?)"

stmtGetLatestGroup :: String
stmtGetLatestGroup = "SELECT id from test_groups ORDER BY id DESC"

stmtGetLatestTestBatch :: String
stmtGetLatestTestBatch = "SELECT id from test_batch_runs ORDER BY id DESC"

stmtGetLatestFailGroup :: String
stmtGetLatestFailGroup = "SELECT id from fail_groups ORDER BY id DESC"
                         

-- Returns the ID of the group we created
makeGroup :: String -> Connection -> IO Int
makeGroup desc con = do
      mkstmt <- prepare con stmtMakeGroup
      execute mkstmt [toSql desc]
      getstmt <- prepare con stmtGetLatestGroup
      execute getstmt []
      fmap (fromSql.head.fromJust) $ fetchRow getstmt

-- Returns the ID of the group we created
makeFailGLatest :: String -> String -> Connection -> IO Int
makeFailGLatest desc reason con = do
  getLatestBatch <- prepare con stmtGetLatestTestBatch
  execute getLatestBatch []
  (latestBatch :: Int) <- fmap (fromSql.head.fromJust) $ fetchRow getLatestBatch 
  mkFailGroup <- prepare con stmtMakeFailGroup
  execute mkFailGroup [toSql latestBatch, toSql desc, toSql reason]
  getLatestFailG <- prepare con stmtGetLatestFailGroup
  execute getLatestFailG []
  fmap (fromSql.head.fromJust) $ fetchRow getLatestFailG

addFilesToSomeGroup :: String -> Int -> [String] -> Connection -> IO ()
addFilesToSomeGroup stmtstr gid tids con = do
  stmt <- prepare con stmtstr
  let stmtargs = transpose [replicate (length tids) (toSql gid) , map toSql tids]
  mapM_ (execute stmt) stmtargs

addFilesToGroup :: Int -> [String] -> Connection -> IO ()
addFilesToGroup = addFilesToSomeGroup stmtAddFileToGroup

addFilesToFailGroup :: Int -> [String] -> Connection -> IO ()
addFilesToFailGroup = addFilesToSomeGroup stmtAddFileToFailGroup
