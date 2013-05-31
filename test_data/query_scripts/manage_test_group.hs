{-# LANGUAGE DeriveDataTypeable #-}

module Main where

import ResultsDB(getConnection)
import Database.HDBC(toSql,fromSql,withTransaction,prepare,execute,fetchRow)
import Database.HDBC.Sqlite3(Connection)
import System.Console.CmdArgs
import Data.Maybe
import Control.Monad(void)

-- data UpdateType = CreateGroup | AppendToGroup
--                 deriving (Data,Typeable,Enum,Eq,Show)

data ManageTestGroup = CreateGroup
                       { groupDescription :: String
                       , files :: [String]
                       } |
                       AppendByDesc
                       { groupDescription :: String
                       , files :: [String]
                       } |
                       AppendById
                       { groupId :: Int
                       , files :: [String]
                       } |
                       AmendDesc
                       { groupId :: Int
                       , groupDescription :: String
                       } deriving (Data,Typeable,Show)

createDefaults :: ManageTestGroup
createDefaults = CreateGroup
             { groupDescription  = "" &= help "A description of this test group"
             , files = [] &= help "The test files in this group"
             }

appendByDescDefaults :: ManageTestGroup
appendByDescDefaults = AppendByDesc
                       { groupDescription = "" &= help "The description of the group to update"
                       , files = [] &= help "The test files to add to this group"
                       }
appendByIdDefaults :: ManageTestGroup
appendByIdDefaults = AppendById
                       { groupId = 0 &= help "The id of the group to update"
                       , files = [] &= help "The test files to add to this group"
                       }
amendDescDefaults :: ManageTestGroup
amendDescDefaults = AmendDesc
                    { groupId = 0 &= help "The id of the group to amend"
                    , groupDescription = "" &= help "The new description"
                    }

stmtMakeGroup :: String
stmtMakeGroup = "INSERT INTO test_groups (description) VALUES (?)"

stmtAddFileToGroup :: String
stmtAddFileToGroup = "INSERT INTO test_group_memberships (group_id,test_id) VALUES (?,?)"

stmtUpdateDesc :: String
stmtUpdateDesc = "UPDATE test_groups SET description=? WHERE id=?"

stmtGetGroupId :: String
stmtGetGroupId = "SELECT id FROM test_groups WHERE description=?"

stmtGetLatestGroup :: String
stmtGetLatestGroup = "SELECT id from test_groups ORDER BY id DESC"

-- Returns the ID of the group we created
makeGroup :: String -> Connection -> IO Int
makeGroup desc connection =
  withTransaction connection (
    \con -> do
      mkstmt <- prepare con stmtMakeGroup
      execute mkstmt [toSql desc]
      getstmt <- prepare con stmtGetLatestGroup
      execute getstmt []
      fmap (fromSql.head.fromJust) $ fetchRow getstmt)

addFileToGroup :: Int -> String -> Connection -> IO ()
addFileToGroup gid tid con = do
  stmt <- prepare con stmtAddFileToGroup
  void $ execute stmt [toSql gid,toSql tid]

updateDesc :: Int -> String -> Connection -> IO ()
updateDesc gid desc con = do
  stmt <- prepare con stmtUpdateDesc
  void $ execute stmt [toSql desc, toSql gid]

getGroupId :: String -> Connection -> IO Int
getGroupId desc con = do
  stmt <- prepare con stmtGetGroupId
  execute stmt [toSql desc]
  fmap (fromSql.head.fromJust) $ fetchRow stmt

dispatch :: ManageTestGroup -> Connection -> IO ()
dispatch (CreateGroup desc filenames) con = do
  gid <- makeGroup desc con
  void $ mapM (flip (addFileToGroup gid) con) filenames
dispatch (AppendByDesc desc filenames) con = do
  gid <- getGroupId desc con
  void $ mapM (flip (addFileToGroup gid) con) filenames
  error ".."
dispatch (AppendById gid filenames) con = do
  void $ mapM (flip (addFileToGroup gid) con) filenames
  error ".."
dispatch (AmendDesc gid desc) con = updateDesc gid desc con

main :: IO ()
main = do
  opts <- cmdArgs (modes [createDefaults,appendByDescDefaults, appendByIdDefaults,amendDescDefaults])
  con <- getConnection
  withTransaction con $ dispatch opts
