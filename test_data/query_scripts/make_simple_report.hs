{-# LANGUAGE DeriveDataTypeable, RecordWildCards #-}

module Main where

import ResultsDB(getConnection)
import Database.HDBC(toSql,withTransaction,prepare,execute,sFetchAllRows)
import Database.HDBC.Sqlite3(Connection)
import Text.Hastache
import Text.Hastache.Context(mkStrContext)
import qualified Data.ByteString.Lazy.Char8 as L
import System.FilePath((</>),(<.>),takeDirectory,takeFileName)
import System.Directory
import System.Console.CmdArgs
import System.Environment
import Data.Time.Clock(getCurrentTime,UTCTime)
import System.Locale(defaultTimeLocale)
import Data.Time.Format(formatTime)
import Data.Maybe
import Control.Monad.IO.Class

data Options = Options
               { reportName :: String
               , reportComment :: String
               , query :: String
               } deriving (Data,Typeable,Show)

progOpts :: Options
progOpts = Options
           { reportName  = "query" &= help "The name of this report"
           , reportComment = "" &= help "additional comments"
           , query = "%Not implemented code in file%" &= help "The query to perform over stderr"}

data Batch = Batch
             { b_id :: Int
             , b_time :: Int
             , b_implementation :: String
             , b_impl_path :: String
             , b_impl_version :: String
             , b_title :: String
             , b_notes :: String
             , b_timestamp :: Int
             , b_system :: String
             , b_osnodename :: String
             , b_osrelease :: String
             , b_osversion :: String
             , b_hardware :: String
             } deriving Show

data SingleTestRun = SingleTestRun
                     { str_id :: Int
                     , str_test_id :: String
                     , str_batch_id :: Int
                     , str_status :: String
                     , str_stdout :: String
                     , str_stderr :: String
                     } deriving Show

strPASS :: String
strPASS = "PASS"
strFAIL :: String
strFAIL = "FAIL"
strABORT :: String
strABORT = "ABORT"

stmtGetTestRunByID :: String
stmtGetTestRunByID = "SELECT * from test_batch_runs where id=?"

stmtGetBatchIDs :: String
stmtGetBatchIDs = "SELECT id from test_batch_runs ORDER BY id DESC"

stmtGetLatestBatch :: String
stmtGetLatestBatch = "select id,"++
                     "time,"++
                     "implementation,"++
                     "impl_path,"++
                     "impl_version,"++
                     "title,"++
                     "notes,"++
                     "timestamp,"++
                     "system,"++
                     "osnodename,"++
                     "osrelease,"++
                     "osversion,"++
                     "hardware from test_batch_runs where id=("++
                     "select max(id) from ("++
                     "(select * from test_batch_runs where "++
                     "implementation='JSRef')))"

dbToBatch :: [Maybe String] -> Batch
dbToBatch res = Batch
                     { b_id = read.fromJust $ res!!0
                     , b_time = read.fromJust $ res!!1
                     , b_implementation = fromJust $ res!!2
                     , b_impl_path = fromJust $ res!!3
                     , b_impl_version = fromJust $ res!!4
                     , b_title = fromJust $ res!!5
                     , b_notes = fromJust $ res!!6
                     , b_timestamp = read.fromJust $ res!!7
                     , b_system = fromJust $ res!!8
                     , b_osnodename = fromJust $ res!!9
                     , b_osrelease = fromJust $ res!!10
                     , b_osversion = fromJust $ res!!11
                     , b_hardware = fromJust $ res!!12}

stmtGetSTRsByBatch :: String
stmtGetSTRsByBatch = "SELECT * from single_test_runs where batch_id=?"

stmtGetSTRsByBatchStdOut :: String
stmtGetSTRsByBatchStdOut = "SELECT * from single_test_runs where stdout LIKE ? AND batch_id=?;"

-- This one is particularly useful with LIKE "%Not implemented code in file%"
-- which gets us all tests that fail for not-implemented-yet reasons.
stmtGetSTRsByBatchStdErr :: String
stmtGetSTRsByBatchStdErr = "SELECT id,test_id,batch_id,status,stdout,stderr from single_test_runs where stdout LIKE ? AND batch_id=?;"

dbToSTR :: [Maybe String] -> SingleTestRun
dbToSTR res = SingleTestRun
                     { str_id = read.fromJust $ res!!0
                     , str_test_id = fromJust $ res!!1
                     , str_batch_id = read.fromJust $ res!!2
                     , str_status = fromJust $ res!!3
                     , str_stdout = fromJust $ res!!4
                     , str_stderr = fromJust $ res!!5
                     }

reportDir :: IO FilePath
reportDir = do
  dir <- getCurrentDirectory
  return $ runNTimes 5 takeDirectory dir </> "web" </> "test_results"
  where runNTimes n f x = iterate f x !! n

outerTemplate :: IO FilePath
outerTemplate = do
  dir <- reportDir
  return $ dir</>"template"<.>"tmpl"

reportTemplate :: IO FilePath
reportTemplate = do
  dir <- reportDir
  return $ dir</>"test_results"<.>"tmpl"

outputFileName :: String -> UTCTime -> String -> IO FilePath
outputFileName username time tname = do
  dir <- reportDir
  return $
    dir </> ("query_"++username++"_"++tname++"_"++
             (formatTime defaultTimeLocale "%_y-%m-%dT%H:%M:%S" time)) <.> "html"

reportContext :: Monad m => String -> String -> String -> UTCTime -> Batch -> [SingleTestRun] -> MuContext m
reportContext qname comment user time batch results = mkStrContext context
  where
    passes = filter ((strPASS==). str_status ) results
    fails = filter ((strFAIL==). str_status ) results
    aborts = filter ((strABORT==). str_status ) results
    context "implementation" = MuVariable $ b_implementation batch
    context "testtitle" = MuVariable $ qname
    context "testnote" = MuVariable $ comment ++ " -- " ++ b_title batch ++ ": " ++ b_notes batch
    context "time" = MuVariable $ (formatTime defaultTimeLocale "%_y-%m-%dT%H:%M:%S" time)
    context "user" = MuVariable user
    context "system" = MuVariable $ b_system batch
    context "osnodename" = MuVariable $ b_osnodename batch
    context "osrelease" = MuVariable $ b_osrelease batch
    context "osversion" = MuVariable $ b_osversion batch
    context "hardware" = MuVariable $ b_hardware batch
    context "numpasses" = MuVariable $ length passes
    context "numfails" = MuVariable $ length fails
    context "numaborts" = MuVariable $ length aborts
    context "aborts" = MuList $ map (mkStrContext . resContext) aborts
    context "failures" = MuList $ map (mkStrContext . resContext) fails
    context "passes" = MuList $ map (mkStrContext . resContext) passes
    context _ = error "I forgot a case from my template"
    resContext res "testname" = MuVariable . takeFileName $ str_test_id res
    resContext res "filename" = MuVariable $ str_test_id res
    resContext res "stdout" = MuVariable $ str_stdout res
    resContext res "stderr" = MuVariable $ str_stderr res
    resContext _ _ = error "I forgot an inner case from my template"

getLatestBatch :: Connection -> IO Batch
getLatestBatch con = do
  stmt <- prepare con stmtGetLatestBatch
  execute stmt []
  dat <- fmap head $ sFetchAllRows stmt
  return $ dbToBatch dat

getTestsByErrQuery :: Int -> String -> Connection -> IO [SingleTestRun]
getTestsByErrQuery batch query con = do
  stmt <- prepare con stmtGetSTRsByBatchStdErr
  execute stmt [toSql query, toSql batch]
  dat <- sFetchAllRows stmt
  return $ map dbToSTR dat

escapelessConfig :: MonadIO m => MuConfig m
escapelessConfig = defaultConfig {muEscapeFunc = emptyEscape}


main :: IO ()
main = do
  opts <- cmdArgs progOpts
  con <- getConnection
  latestBatch <- withTransaction con getLatestBatch
  strs <- withTransaction con $ getTestsByErrQuery (b_id latestBatch) (query opts)
  outertemp <- outerTemplate
  template <- reportTemplate
  username <- getEnv "USER"
  time <- getCurrentTime
  report <- hastacheFile defaultConfig template (reportContext (reportName opts) (reportComment opts) username time latestBatch strs)
  outfile <- outputFileName username time (reportName opts)
  L.writeFile outfile =<< hastacheFile escapelessConfig outertemp (mkStrContext (\_ -> MuVariable $ report))
