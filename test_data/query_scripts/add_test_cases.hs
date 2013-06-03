{-# LANGUAGE OverloadedStrings #-}

-- A good way to run this is:
-- runhaskell test_data/query_scripts/add_test_cases.hs `find tests/ -type f -name \*.js`

module Main where

import Database.HDBC(toSql,withTransaction,prepare,execute)
import Database.HDBC.Sqlite3(connectSqlite3)
import System.Environment
import Control.Monad(void)
import qualified Data.ByteString.Char8 as C
import Data.List(transpose)
import System.FilePath((</>),(<.>))

dbPath :: IO FilePath
dbPath = do
  username <- getEnv "USER"
  return $ "test_data"</>username<.>"db"

stmtAddCase :: String
stmtAddCase = "INSERT INTO test_cases (filepath,negative) VALUES (?,?)"

isNegative :: FilePath -> IO Bool
isNegative path = do
  file <- C.readFile path
  return $ "@negative" `C.isInfixOf` file

addCases :: [FilePath] -> [Bool] -> IO ([Integer])
addCases files negs = do
  conn <- connectSqlite3 =<< dbPath
  stmt <- prepare conn stmtAddCase
  let testcases = transpose $ [map toSql files, map toSql negs]
  withTransaction conn (const $ mapM (execute stmt) testcases)

main :: IO ()
main = do
  error "Hm"
  files <- getArgs
  putStrLn "I have these files:"
  mapM putStrLn files
  negs <- mapM isNegative files
  void $ addCases files negs
