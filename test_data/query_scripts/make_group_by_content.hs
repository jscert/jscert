{-# LANGUAGE OverloadedStrings #-}

-- Find all files that contain some pattern, and stick them in a test group. The
-- first argument is the sort of group we're making. Valid first arguments are:

-- arith: Find all files that contain "<< 0", ">>> 0" or /\~\d/

-- number: Find all files that contain "Number."

-- A good way to run this is:
-- ./test_data/query_scripts/make_group_by_content number `find tests/ -type f -name \*.js`


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

isNumFile :: ByteString -> Bool
isNumFile = ("Number." `isInfixOf`)

isNumConstructorFile :: ByteString -> Bool
isNumConstructorFile = ("Number(" `isInfixOf`)

isBoolConstructorFile :: ByteString -> Bool
isBoolConstructorFile = ("Boolean(" `isInfixOf`)

isStringConstructorFile :: ByteString -> Bool
isStringConstructorFile = ("String(" `isInfixOf`)

isStringFile :: ByteString -> Bool
isStringFile = ("String." `isInfixOf`)

isToNumberTest :: ByteString -> Bool
isToNumberTest = (" * Operator uses ToNumber" `isInfixOf`)

grouptypes :: String -> (String, ByteString -> Bool)
grouptypes "arith" = ("Arithmetic error tests", isMathFile)
grouptypes "number" = ("Number object tests", isNumFile)
grouptypes "numconstructor" = ("Number constructor object tests", isNumConstructorFile)
grouptypes "boolconstructor" = ("Boolean constructor object tests", isBoolConstructorFile)
grouptypes "stringconstructor" = ("String constructor object tests", isStringConstructorFile)
grouptypes "string" = ("String object tests", isStringFile)
grouptypes "tonumber" = ("ToNumber conversion tests", isToNumberTest)

main :: IO ()
main = do
  args <- getArgs
  let (name,query) = grouptypes $ head args
  con <- getConnectionFromTrunk
  gid <- withTransaction con $ makeGroup name
  files <- mapM (\path -> (\content -> return (path,content)) =<< readFile path) $ tail args
  withTransaction con $ addFilesToGroup gid $ map fst $ filter (query.snd) files
