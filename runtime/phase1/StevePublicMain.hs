{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (IOException, finally, try)
import qualified Data.ByteString as ByteString
import Data.ByteString (ByteString)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Foreign.C.Types (CInt (..))
import Foreign.Ptr (Ptr)
import Phil.Compiler.SteveCAS
  ( ContentId
  , ReadResult (..)
  , parseContentId
  , renderContentId
  )
import Phil.Systems
  ( ProviderRelativePath
  , checkProviderRelativePath
  , fileSystemOccurrence
  , providerRelativePathSegments
  )
import SteveProviderBridge
  ( freeContentIdHandle
  , freeOwnedBytesHandle
  , newContentIdHandle
  , newOwnedBytesHandle
  , providerCheckContentId
  , providerComputeContentId
  , providerReadBlob
  )
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.FilePath ((</>))
import System.IO (hIsEOF, hPutStrLn, stderr, stdin)

foreign import ccall "StevePut"
  nativeStevePut :: Ptr () -> IO CInt

foreign import ccall "SteveGet"
  nativeSteveGet :: Ptr () -> IO CInt

-- | Public Phase-1 Steve launcher. The roots are host bootstrap configuration:
-- they select the concrete user-filesystem and CAS provider occurrences before
-- control enters the checked StevePutCLI / SteveGetCLI behavior.
main :: IO ()
main = do
  args <- getArgs
  case args of
    ["put", storeRoot, fileRoot] -> runPut storeRoot fileRoot
    ["get", storeRoot, fileRoot] -> runGet storeRoot fileRoot
    _ -> usage

usage :: IO a
usage = do
  hPutStrLn stderr "usage: steve (put|get) STORE_ROOT FILE_ROOT"
  exitFailure

runPut :: FilePath -> FilePath -> IO ()
runPut storeRoot fileRoot = do
  input <- readConsoleLine
  case input >>= parseUserPath of
    Nothing -> pure ()
    Just path -> do
      candidate <- readUserFile fileRoot path
      case candidate of
        Nothing -> pure ()
        Just bytes -> do
          -- put-cli.phil computes the printable ID before invoking StevePut.
          -- The helper is the Haskell face of the same provider realization
          -- exported to compiled Phil through the provider ABI.
          let contentId = providerComputeContentId bytes
          invokeStevePut storeRoot bytes
          writeConsole (renderContentId contentId)

runGet :: FilePath -> FilePath -> IO ()
runGet storeRoot fileRoot = do
  input <- readConsoleLine
  case input >>= eitherToMaybe . parseContentId of
    Nothing -> pure ()
    Just contentId -> do
      outputInput <- readConsoleLine
      case outputInput >>= parseUserPath of
        Nothing -> pure ()
        Just outputPath -> do
          -- The source-level invoke has no returned branch to inspect, so the
          -- host launcher deliberately ignores the native outcome code.
          invokeSteveGet storeRoot contentId

          -- get-cli.phil intentionally performs this second read/check after
          -- SteveGet before publishing bytes into the user filesystem.
          readResult <- providerReadBlob storeRoot contentId
          case readResult of
            Right (BlobFound bytes)
              | providerCheckContentId contentId bytes ->
                  replaceUserFile fileRoot outputPath bytes
            _ -> pure ()

invokeStevePut :: FilePath -> ByteString -> IO ()
invokeStevePut storeRoot bytes = do
  candidate <- newOwnedBytesHandle storeRoot bytes
  _ <- nativeStevePut candidate `finally` freeOwnedBytesHandle candidate
  pure ()

invokeSteveGet :: FilePath -> ContentId -> IO ()
invokeSteveGet storeRoot contentId = do
  content <- newContentIdHandle storeRoot contentId
  _ <- nativeSteveGet content `finally` freeContentIdHandle content
  pure ()

readConsoleLine :: IO (Maybe Text)
readConsoleLine = do
  eofResult <- try (hIsEOF stdin) :: IO (Either IOException Bool)
  case eofResult of
    Left _ -> pure Nothing
    Right True -> pure Nothing
    Right False -> do
      lineResult <- try TextIO.getLine :: IO (Either IOException Text)
      pure (either (const Nothing) Just lineResult)

writeConsole :: Text -> IO ()
writeConsole text = do
  _ <- try (TextIO.putStr text) :: IO (Either IOException ())
  pure ()

parseUserPath :: Text -> Maybe ProviderRelativePath
parseUserPath raw = do
  occurrence <- eitherToMaybe (fileSystemOccurrence "steve.user.fs")
  eitherToMaybe (checkProviderRelativePath occurrence raw)

readUserFile :: FilePath -> ProviderRelativePath -> IO (Maybe ByteString)
readUserFile root path = do
  result <- try (ByteString.readFile (resolveUserPath root path))
    :: IO (Either IOException ByteString)
  pure (either (const Nothing) Just result)

replaceUserFile :: FilePath -> ProviderRelativePath -> ByteString -> IO ()
replaceUserFile root path bytes = do
  _ <- try (ByteString.writeFile (resolveUserPath root path) bytes)
    :: IO (Either IOException ())
  pure ()

resolveUserPath :: FilePath -> ProviderRelativePath -> FilePath
resolveUserPath root path =
  foldl (</>) root (map Text.unpack (providerRelativePathSegments path))

eitherToMaybe :: Either a b -> Maybe b
eitherToMaybe = either (const Nothing) Just
