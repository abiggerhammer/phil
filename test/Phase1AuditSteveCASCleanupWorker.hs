{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (forM, unless)
import qualified Data.ByteString as ByteString
import Data.List (isInfixOf)
import Phil.Compiler.SteveCAS
  ( InstallResult (..), SteveCASError (..), computeContentId, installBlob )
import System.Directory (listDirectory)
import System.Environment (getArgs)
import System.Exit (die)
import System.IO.Error (catchIOError)
import System.Posix.Files (readSymbolicLink)

-- Executed with RLIMIT_FSIZE=0, SIGXFSZ ignored, and a large RTS nursery.
-- Inspect the same process's descriptors before GC or process exit.
main :: IO ()
main = do
  args <- getArgs
  root <- case args of
    [path] -> pure path
    _ -> die "usage: steve-cas-cleanup-worker <absolute-store-directory>"

  before <- stagedDescriptors
  unless (null before) $
    die ("unexpected temporary descriptors before install: " ++ show before)

  let payload = ByteString.replicate 131072 65
      digest = computeContentId payload
  failed <- installBlob root digest payload
  case failed of
    Left (StoreIOError _) -> pure ()
    other -> die ("expected OS write failure, got: " ++ show other)

  after <- stagedDescriptors
  unless (null after) $
    die ("temporary CAS handle survived failed hPut: " ++ show after)
  entries <- listDirectory root
  unless (null entries) $
    die ("temporary name or published object survived failure: " ++ show entries)
  putStrLn "PASS: E-STEVE-CLEANUP-01 failed hPut closes the live temp descriptor"

  -- Retry in the same process and preserve hard-link no-replace behavior.
  let emptyId = computeContentId ByteString.empty
  first <- installBlob root emptyId ByteString.empty
  second <- installBlob root emptyId ByteString.empty
  unless (first == Right Installed && second == Right AlreadyExists) $
    die ("CAS retry after failure is incorrect: " ++ show (first, second))
  remaining <- listDirectory root
  unless (length remaining == 1) $
    die ("CAS retry left unexpected temporary objects: " ++ show remaining)
  putStrLn "PASS: E-STEVE-CLEANUP-01 same-process CAS retry succeeds"

stagedDescriptors :: IO [FilePath]
stagedDescriptors = do
  entries <- listDirectory "/proc/self/fd"
  targets <- forM entries $ \name ->
    catchIOError
      (Just <$> readSymbolicLink ("/proc/self/fd/" ++ name))
      (const (pure Nothing))
  pure [target | Just target <- targets, isInfixOf ".phil-steve-cas.tmp" target]
