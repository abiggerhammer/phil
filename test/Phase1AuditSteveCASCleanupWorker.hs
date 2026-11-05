{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (forM, unless)
import qualified Data.ByteString as ByteString
import Data.List (isInfixOf)
import qualified Data.Text as Text
import Phil.Compiler.SteveCAS
  ( InstallResult (..), SteveCASError (..), computeContentId, installBlob )
import System.Directory (listDirectory)
import System.Environment (getArgs)
import System.Exit (die)
import System.IO.Error (catchIOError)
import System.Posix.Files (readSymbolicLink)

#ifdef TEST_CAS_PRE_CLOSE
import Phil.Compiler.SteveCAS (testStagedHandleClosed)
#endif

-- Injected mode verifies a specific pre-close exception; real mode probes
-- RLIMIT_FSIZE but does not attribute the error to hPut versus hClose.
-- Inspect the same process's descriptors before GC or process exit.
main :: IO ()
main = do
  args <- getArgs
  (root, injected) <- case args of
    [path, "injected"] -> pure (path, True)
    [path, "real"] -> pure (path, False)
    _ -> die "usage: steve-cas-cleanup-worker <store-dir> (injected|real)"

  before <- stagedDescriptors
  unless (null before) $
    die ("unexpected temporary descriptors before install: " ++ show before)

  let payload = ByteString.replicate 131072 65
      digest = computeContentId payload
  failed <- installBlob root digest payload
  case failed of
    Left (StoreIOError message)
      | injected && not (Text.isInfixOf
          "E-STEVE-CLEANUP-01-injected-preclose-failure" message) ->
            die ("wrong injected exception: " ++ Text.unpack message)
      | otherwise -> pure ()
    other -> die ("expected CAS write failure, got: " ++ show other)

  after <- stagedDescriptors
  unless (null after) $
    die ("temporary CAS handle survived failed hPut: " ++ show after)
#ifdef TEST_CAS_PRE_CLOSE
  -- Keep the acquired Handle reachable through an imported test-only anchor.
  -- A GC finalizer must not mask a missing close before this observation.
  closed <- testStagedHandleClosed
  unless closed $
    die "temporary CAS handle survived failed hPut: anchored handle remains open"
#endif
  entries <- listDirectory root
  unless (null entries) $
    die ("temporary name or published object survived failure: " ++ show entries)
  putStrLn ("PASS: E-STEVE-CLEANUP-01 no live temp FD after " ++
    if injected then "injected pre-close failure" else "filesystem failure")

  -- In injected mode every staged write has been replaced with an exception.
  -- Only the separate uninstrumented real-failure mode tests normal retry.
  unless injected $ do
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
