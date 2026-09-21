{-# LANGUAGE ScopedTypeVariables #-}

module SteveUserFile
  ( replaceFilePreservingFailure
  ) where

import Control.Exception (IOException, mask, onException, throwIO, try)
import qualified Data.ByteString as ByteString
import Data.ByteString (ByteString)
import System.Directory (removeFile, renameFile)
import System.FilePath (takeDirectory, takeFileName)
import System.IO (hClose, openBinaryTempFileWithDefaultPermissions)
import System.IO.Error (isDoesNotExistError)
import System.Posix.Files (FileStatus, fileMode, getFileStatus, setFileMode)

-- | Replace one host file without modifying the destination before the new
-- bytes have been written and closed successfully.
--
-- The publication point is the final rename in the destination directory.
-- Any IOException before that point closes/unlinks the staged file and returns
-- False. Once the rename succeeds, this function returns True; it does not
-- perform any later fallible operation that could misreport the published
-- state as an unchanged-state failure.
--
-- This is process-observable failure preservation, not crash durability.
replaceFilePreservingFailure :: FilePath -> ByteString -> IO Bool
replaceFilePreservingFailure destination bytes = do
  result <- try (stageAndPublish destination bytes)
    :: IO (Either IOException ())
  pure (either (const False) (const True) result)

stageAndPublish :: FilePath -> ByteString -> IO ()
stageAndPublish destination bytes =
  mask $ \restore -> do
    let directory = takeDirectory destination
        template = "." <> takeFileName destination <> ".steve-replace."
    (temporary, handle) <- openBinaryTempFileWithDefaultPermissions directory template
    let cleanup = do
          ignoreIOException (hClose handle)
          ignoreIOException (removeFile temporary)
        prepare = do
          preserveExistingMode destination temporary
          restore (ByteString.hPut handle bytes)
          restore (hClose handle)
        publish = renameFile temporary destination

    prepare `onException` cleanup
    publish `onException` cleanup

ignoreIOException :: IO () -> IO ()
ignoreIOException action = do
  _ <- try action :: IO (Either IOException ())
  pure ()

preserveExistingMode :: FilePath -> FilePath -> IO ()
preserveExistingMode destination temporary = do
  status <- try (getFileStatus destination)
    :: IO (Either IOException FileStatus)
  case status of
    Right existing -> setFileMode temporary (fileMode existing)
    Left errorValue
      | isDoesNotExistError errorValue -> pure ()
      | otherwise -> throwIO errorValue
