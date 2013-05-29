module Main where

import ResultsDB(getConnection)
import Database.HDBC(toSql,withTransaction,prepare,execute)
import Control.Monad(void)
import System.Console.GetOpt
import Text.Hastache
import Text.Hastache.Context
import qualified Data.ByteString.Lazy.Char8 as C
import System.FilePath((</>),(<.>),takeDirectory)
import System.Directory

stmtGetTestRunByID :: String
stmtGetTestRunByID = "SELECT * from test_batch_runs where id=?"

stmtGetSTRsByBatch :: String
stmtGetSTRsByBatch = "SELECT * from single_test_runs where batch_id=?"

stmtGetSTRsByBatchStdOut :: String
stmtGetSTRsByBatchStdOut = "SELECT * from single_test_runs where stdout LIKE ? AND batch_id=?;"

-- This one is particularly useful with LIKE "%Not implemented code in file%"
-- which gets us all tests that fail for not-implemented-yet reasons.
stmtGetSTRsByBatchStdErr :: String
stmtGetSTRsByBatchStdErr = "SELECT * from single_test_runs where stdout LIKE ? AND batch_id=?;"

reportDir :: IO FilePath
reportDir = fmap (runNTimes 5 takeDirectory) getCurrentDirectory
  where runNTimes n f x = iterate f x !! n

reportTemplate :: IO FilePath
reportTemplate = do
  dir <- reportDir
  return $ dir</>"test_results"<.>"tmpl"

main :: IO ()
main = error "Woo!"
-- Get all tests of some query
--      - Default to latest test run for particular implementation?
--      - Default to latest test run for JSRef?
-- Make HTML report of those tests.
