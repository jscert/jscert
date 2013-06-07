{-# LANGUAGE DeriveDataTypeable #-}

module Main where

import ResultsDB(getConnectionFromTrunk)
import Database.HDBC(toSql,fromSql,withTransaction,prepare,execute,fetchRow,Statement,SqlValue)
import Database.HDBC.Sqlite3(Connection)
import System.Console.CmdArgs
import Data.Maybe
import Control.Monad(void)
import Data.List(transpose)

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
             , files = [] &= args
             }

appendByDescDefaults :: ManageTestGroup
appendByDescDefaults = AppendByDesc
                       { groupDescription = "" &= help "The description of the group to update"
                       , files = [] &= args
                       }
appendByIdDefaults :: ManageTestGroup
appendByIdDefaults = AppendById
                       { groupId = 0 &= help "The id of the group to update"
                       , files = [] &= args
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
  addFilesToGroup gid filenames con
dispatch (AppendByDesc desc filenames) con = do
  gid <- getGroupId desc con
  addFilesToGroup gid filenames con
dispatch (AppendById gid filenames) con = addFilesToGroup gid filenames con
dispatch (AmendDesc gid desc) con = updateDesc gid desc con

main :: IO ()
main = do
  opts <- cmdArgs (modes [createDefaults,appendByDescDefaults, appendByIdDefaults,amendDescDefaults])
  con <- getConnectionFromTrunk
  withTransaction con $ dispatch opts
