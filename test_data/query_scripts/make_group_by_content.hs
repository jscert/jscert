{-# LANGUAGE OverloadedStrings #-}

-- Find all files that contain some pattern, and stick them in a test group. The
-- first argument is the sort of group we're making. Valid first arguments are:

-- arith: Find all files that contain "<< 0", ">>> 0" or /\~\d/

-- number: Find all files that contain "Number."

module Main where

import Prelude hiding (readFile)
import System.Environment
import ResultsDB(getConnectionFromTrunk,addFilesToGroup,makeGroup)
import Database.HDBC(withTransaction)
import Data.ByteString.Char8(ByteString,readFile,isInfixOf)
import Text.Regex.PCRE((=~))


isMathFile :: ByteString -> Bool
isMathFile content = ("<< 0" `isInfixOf` content)
                     || (">>> 0" `isInfixOf` content)
                     || content =~ ("~\\d"::ByteString)

grouptypes :: String -> (String, ByteString -> Bool)
grouptypes "arith" = ("Arithmetic error tests", isMathFile)

main :: IO ()
main = do
  args <- getArgs
  let (name,query) = grouptypes $ head args
  con <- getConnectionFromTrunk
  gid <- withTransaction con $ makeGroup name
  files <- mapM (\path -> (\content -> return (path,content)) =<< readFile path) $ tail args
  withTransaction con $ addFilesToGroup gid $ map fst $ filter (query.snd) files
