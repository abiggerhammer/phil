{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString as ByteString
import SteveUserFile (replaceFilePreservingFailure)
import System.Environment (getArgs)
import System.Exit (exitFailure)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [destination, payloadPath] -> do
      payload <- ByteString.readFile payloadPath
      published <- replaceFilePreservingFailure destination payload
      putStrLn (if published then "published" else "preserved")
    _ -> do
      putStrLn "usage: phase1-audit-steve-replace-worker DESTINATION PAYLOAD"
      exitFailure
