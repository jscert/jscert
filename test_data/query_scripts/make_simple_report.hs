{-# LANGUAGE DeriveDataTypeable #-}

module Main where

import ResultsDB(getConnection)
import Database.HDBC(toSql,withTransaction,prepare,execute,fetchAllRows,SqlValue,fromSql)
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
import Control.Monad.IO.Class

data QueryType = StmtGetTestRunByID | StmtGetBatchIDs | GetLatestBatch
               | StmtGetSTRsByBatch | StmtGetSTRsByBatchStdOut
               | StdOutLike | StdOutNotLike | StdOutNotLikeEither
                              deriving (Data,Typeable,Enum,Eq,Show)

data Options = Options
               { reportName :: String
               , reportComment :: String
               , queryType :: QueryType
               , query :: String
               , query2 :: String
               } deriving (Data,Typeable,Show)

progOpts :: Options
progOpts = Options
           { reportName  = "query" &= help "The name of this report"
           , reportComment = "" &= help "additional comments"
           , queryType = StdOutLike &= help "Which sort of query should we do? Default=StdOutLike"
           , query = "%Not implemented code%" &= help "The query to perform over stderr"
           , query2 = "%Translation of Javascript syntax does not support%" &= help "Sometimes we want more than one argument in a query"
           }

data Batch = Batch
             { bId :: Int
             , bTime :: Int
             , bImplementation :: String
             , bImplPath :: String
             , bImplVersion :: String
             , bTitle :: String
             , bNotes :: String
             , bTimestamp :: Int
             , bSystem :: String
             , bOsnodename :: String
             , bOsrelease :: String
             , bOsversion :: String
             , bHardware :: String
             } deriving Show

data SingleTestRun = SingleTestRun
                     { strId :: Int
                     , strTestId :: String
                     , strBatchId :: Int
                     , strStatus :: String
                     , strStdout :: String
                     , strStderr :: String
                     } deriving Show

strPASS :: String
strPASS = "PASS"
strFAIL :: String
strFAIL = "FAIL"
strABORT :: String
strABORT = "ABORT"

stmts :: QueryType -> String
stmts StmtGetTestRunByID       = "SELECT * from test_batch_runs where id=?"
stmts StmtGetBatchIDs          = "SELECT id from test_batch_runs ORDER BY id DESC"
stmts GetLatestBatch           = "select id,"++
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
stmts StmtGetSTRsByBatchStdOut = "SELECT * from single_test_runs where stdout LIKE ? AND batch_id=?;"
stmts StmtGetSTRsByBatch       = "SELECT * from single_test_runs where batch_id=?"
stmts StdOutLike               = "SELECT id,test_id,batch_id,status,stdout,stderr from single_test_runs where stdout LIKE ? AND batch_id=?;"
stmts StdOutNotLike            = "SELECT id,test_id,batch_id,status,stdout,stderr from single_test_runs where "++
                                 "batch_id = ? AND "++
                                 "id NOT IN (select id from single_test_runs where stdout LIKE ? AND batch_id=?)"
stmts StdOutNotLikeEither      = "SELECT id,test_id,batch_id,status,stdout,stderr from single_test_runs where "++
                                 "batch_id = ? AND "++
                                 "id NOT IN (select id from single_test_runs where stdout LIKE ? AND batch_id=?) AND "++
                                 "id NOT IN (select id from single_test_runs where stdout LIKE ? AND batch_id=?)"

dbToBatch :: [SqlValue] -> Batch
dbToBatch res = Batch
                     { bId = fromSql $ head res
                     , bTime = fromSql $ res!!1
                     , bImplementation = fromSql $ res!!2
                     , bImplPath = fromSql $ res!!3
                     , bImplVersion = fromSql $ res!!4
                     , bTitle = fromSql $ res!!5
                     , bNotes = fromSql $ res!!6
                     , bTimestamp = fromSql $ res!!7
                     , bSystem = fromSql $ res!!8
                     , bOsnodename = fromSql $ res!!9
                     , bOsrelease = fromSql $ res!!10
                     , bOsversion = fromSql $ res!!11
                     , bHardware = fromSql $ res!!12}


dbToSTR :: [SqlValue] -> SingleTestRun
dbToSTR res = SingleTestRun
                     { strId = fromSql $ head res
                     , strTestId = fromSql $ res!!1
                     , strBatchId = fromSql $ res!!2
                     , strStatus = fromSql $ res!!3
                     , strStdout = fromSql $ res!!4
                     , strStderr = fromSql $ res!!5
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
             formatTime defaultTimeLocale "%_y-%m-%dT%H:%M:%S" time) <.> "html"

reportContext :: Monad m => String -> String -> String -> UTCTime -> Batch -> [SingleTestRun] -> MuContext m
reportContext qname comment user time batch results = mkStrContext context
  where
    passes = filter ((strPASS==). strStatus ) results
    fails = filter ((strFAIL==). strStatus ) results
    aborts = filter ((strABORT==). strStatus ) results
    context "implementation" = MuVariable $ bImplementation batch
    context "testtitle" = MuVariable qname
    context "testnote" = MuVariable $ comment ++ " -- " ++ bTitle batch ++ ": " ++ bNotes batch
    context "time" = MuVariable $ formatTime defaultTimeLocale "%_y-%m-%dT%H:%M:%S" time
    context "user" = MuVariable user
    context "system" = MuVariable $ bSystem batch
    context "osnodename" = MuVariable $ bOsnodename batch
    context "osrelease" = MuVariable $ bOsrelease batch
    context "osversion" = MuVariable $ bOsversion batch
    context "hardware" = MuVariable $ bHardware batch
    context "numpasses" = MuVariable $ length passes
    context "numfails" = MuVariable $ length fails
    context "numaborts" = MuVariable $ length aborts
    context "aborts" = MuList $ map (mkStrContext . resContext) aborts
    context "failures" = MuList $ map (mkStrContext . resContext) fails
    context "passes" = MuList $ map (mkStrContext . resContext) passes
    context _ = error "I forgot a case from my template"
    resContext res "testname" = MuVariable . takeFileName $ strTestId res
    resContext res "filename" = MuVariable $ strTestId res
    resContext res "stdout" = MuVariable $ strStdout res
    resContext res "stderr" = MuVariable $ strStderr res
    resContext _ _ = error "I forgot an inner case from my template"

getLatestBatch :: Connection -> IO Batch
getLatestBatch con = do
  stmt <- prepare con (stmts GetLatestBatch)
  execute stmt []
  dat <- fmap head $ fetchAllRows stmt
  return $ dbToBatch dat

makeQueryArgs :: QueryType -> Int -> String -> String -> [SqlValue]
makeQueryArgs StdOutLike batch querystr1 _ = [toSql querystr1, toSql batch]
makeQueryArgs StdOutNotLike batch querystr1 _ = [toSql batch, toSql querystr1, toSql batch]
makeQueryArgs StdOutNotLikeEither batch querystr1 querystr2 = [toSql batch, toSql querystr1, toSql batch, toSql querystr2, toSql batch]
makeQueryArgs StmtGetTestRunByID rId _ _ = [toSql rId]
makeQueryArgs StmtGetBatchIDs _ _ _ = []
makeQueryArgs GetLatestBatch _ _ _ = []
makeQueryArgs StmtGetSTRsByBatchStdOut batchId stdout _ = [toSql stdout, toSql batchId]
makeQueryArgs StmtGetSTRsByBatch batchId _ _ = [toSql batchId]

getTestsBySomeQuery :: QueryType -> Int -> String -> String  -> Connection -> IO [SingleTestRun]
getTestsBySomeQuery querytype batch querystr1 querystr2 con = do
  stmt <- prepare con (stmts querytype )
  execute stmt $ makeQueryArgs querytype batch querystr1 querystr2
  dat <- fetchAllRows stmt
  return $ map dbToSTR dat

escapelessConfig :: MonadIO m => MuConfig m
escapelessConfig = defaultConfig {muEscapeFunc = emptyEscape}


main :: IO ()
main = do
  opts <- cmdArgs progOpts
  con <- getConnection
  latestBatch <- withTransaction con getLatestBatch
  strs <- withTransaction con $
          getTestsBySomeQuery (queryType opts) (bId latestBatch) (query opts) (query2 opts)
  outertemp <- outerTemplate
  template <- reportTemplate
  username <- getEnv "USER"
  time <- getCurrentTime
  report <- hastacheFile defaultConfig template (reportContext (reportName opts) (reportComment opts) username time latestBatch strs)
  outfile <- outputFileName username time (reportName opts)
  L.writeFile outfile =<< hastacheFile escapelessConfig outertemp (mkStrContext (\_ -> MuVariable report))
