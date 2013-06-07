{-# LANGUAGE OverloadedStrings #-}

-- Find all files that contain "<< 0", ">>> 0" or /\~\d/ and stick them in a
-- test group.

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

main :: IO ()
main = do
  args <- getArgs
  con <- getConnectionFromTrunk
  gid <- withTransaction con $ makeGroup "Arithmetic error tests"
  files <- mapM (\path -> (\content -> return (path,content)) =<< readFile path) args
  withTransaction con $ addFilesToGroup gid $ map fst $ filter (isMathFile.snd) files
