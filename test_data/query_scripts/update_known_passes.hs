{-# LANGUAGE DeriveDataTypeable #-}

module Main where

import ResultsDB(getConnection,strPASS,strFAIL,strABORT)
import Database.HDBC(toSql,withTransaction,prepare,execute,fetchAllRows,SqlValue,fromSql)
import Database.HDBC.Sqlite3(Connection)
import System.Console.CmdArgs
import Data.Time.Clock(getCurrentTime,UTCTime)
import System.Locale(defaultTimeLocale)
import Data.Time.Format(formatTime)
import System.FilePath((<.>))
import Data.Maybe(fromMaybe)

data UpdateKnownPasses = UpdateKnownPasses { oldTestID :: Maybe Int
                                           , newTestID :: Maybe Int
                                           } deriving (Data,Typeable,Show)

progOpts :: UpdateKnownPasses
progOpts = UpdateKnownPasses { oldTestID = Nothing
                                           &= help "The ID of the older test batch we're comparing"
                             , newTestID = Nothing
                                           &= help "the ID of the newer test batch we're comparing"}
           &= help ("Find out the regressions between the last two test batch runs in the DB. "
                    ++"Or you can specify which runs to compare. Writes the most recent pass set to a dated file.")

stmtGetBatchIDs :: String
stmtGetBatchIDs = "SELECT id from test_batch_runs ORDER BY id DESC"

getBatchIDs :: Connection -> IO [Int]
getBatchIDs con = do
  stmt <- prepare con stmtGetBatchIDs
  execute stmt []
  rows <- fetchAllRows stmt
  return $ map (\[bid] -> fromSql bid) rows

getLastTwoIDs :: Maybe Int -> Maybe Int -> Connection -> IO (Int,Int)
getLastTwoIDs (Just oldID) (Just newID) _ = return (oldID,newID)
getLastTwoIDs old new con = do
  ids <- getBatchIDs con
  return (fromMaybe (ids!!1) old,fromMaybe (head ids) new)

stmtGetPasses :: String
stmtGetPasses = "SELECT test_id from single_test_runs where status=? AND batch_id=?;"

getPasses :: Int -> Connection -> IO [String]
getPasses bid con = do
  stmt <- prepare con stmtGetPasses
  execute stmt [toSql strPASS, toSql bid]
  rows <- fetchAllRows stmt
  return $ map (\[fileName] -> fromSql fileName) rows

getRegressions :: [String] -> [String] -> [String]
getRegressions oldPasses newPasses = filter (not . (`elem` newPasses)) oldPasses

outputFileName :: UTCTime ->  FilePath
outputFileName time =
    ("passed_tests_"++ formatTime defaultTimeLocale "%_y-%m-%dT%H:%M:%S" time) <.> "txt"

main :: IO ()
main = do
  con <- getConnection
  opts <- cmdArgs progOpts
  (oldID,newID) <- getLastTwoIDs (oldTestID opts) (newTestID opts) con
  newPassSet <- getPasses newID con
  oldPassSet <- getPasses oldID con
  let regressions = getRegressions oldPassSet newPassSet
  putStrLn $ "There were "++(show $ length regressions)++" regressions. They were:"
  mapM putStrLn regressions
  putStrLn $ "Those were the "++(show $ length regressions)++" regressions."
  time <- getCurrentTime
  let outfile = outputFileName time
  writeFile outfile $ unlines newPassSet
