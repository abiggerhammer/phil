{-# LANGUAGE OverloadedStrings #-}

module Phil.Compiler.SteveCAS
  ( ContentId
  , InstallResult (..)
  , ReadResult (..)
  , SteveCASError (..)
  , computeContentId
  , checkContentId
  , renderContentId
  , parseContentId
  , installBlob
  , readBlob
  ) where

import Control.Exception (IOException, try)
import qualified Crypto.Hash.SHA256 as SHA256
import Data.Bits ((.&.), shiftR)
import qualified Data.ByteString as ByteString
import Data.ByteString (ByteString)
import Data.Char (digitToInt, isHexDigit, toLower)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import System.Directory
  ( createDirectoryIfMissing
  , doesFileExist
  , removeFile
  )
import System.FilePath ((</>))
import System.IO (hClose, openBinaryTempFile)
import System.IO.Error (isAlreadyExistsError, isDoesNotExistError)
import System.Posix.Files (createLink)

newtype ContentId = ContentId ByteString
  deriving (Eq, Ord)

instance Show ContentId where
  show = Text.unpack . renderContentId

data InstallResult
  = Installed
  | AlreadyExists
  deriving (Eq, Ord, Show)

data ReadResult
  = BlobFound ByteString
  | BlobNotFound
  deriving (Eq, Show)

data SteveCASError
  = InvalidContentId Text
  | InstallContentDigestMismatch ContentId ContentId
  | StoreIOError Text
  deriving (Eq, Show)

computeContentId :: ByteString -> ContentId
computeContentId = ContentId . SHA256.hash

checkContentId :: ContentId -> ByteString -> Bool
checkContentId expected bytes = computeContentId bytes == expected

renderContentId :: ContentId -> Text
renderContentId (ContentId bytes) = Text.decodeUtf8 (ByteString.concatMap hexByte bytes)
  where
    hexByte byte = ByteString.pack
      [ hexDigit (byte `shiftR` 4)
      , hexDigit (byte .&. 0x0f)
      ]
    hexDigit nibble
      | nibble < 10 = 48 + nibble
      | otherwise = 87 + nibble

parseContentId :: Text -> Either SteveCASError ContentId
parseContentId raw
  | Text.length normalized /= 64 = Left (InvalidContentId raw)
  | not (Text.all isHexDigit normalized) = Left (InvalidContentId raw)
  | otherwise = Right (ContentId (ByteString.pack (pairs (Text.unpack normalized))))
  where
    normalized = Text.map toLower raw
    pairs [] = []
    pairs (high : low : rest) =
      fromIntegral (digitToInt high * 16 + digitToInt low) : pairs rest
    pairs _ = []

installBlob
  :: FilePath
  -> ContentId
  -> ByteString
  -> IO (Either SteveCASError InstallResult)
installBlob root contentId bytes
  | actualId /= contentId =
      pure (Left (InstallContentDigestMismatch contentId actualId))
  | otherwise = do
      createResult <- try (createDirectoryIfMissing True root)
      case createResult of
        Left err -> pure (Left (ioErrorText err))
        Right () -> publish
  where
    actualId = computeContentId bytes
    target = blobPath root contentId
    publish = do
      tempResult <- try (openBinaryTempFile root ".phil-steve-cas.tmp")
      case tempResult of
        Left err -> pure (Left (ioErrorText err))
        Right (tempPath, handle) -> do
          writeResult <- try (ByteString.hPut handle bytes >> hClose handle)
          case writeResult of
            Left err -> do
              _ <- tryRemove tempPath
              pure (Left (ioErrorText err))
            Right () -> do
              linkResult <- try (createLink tempPath target)
              _ <- tryRemove tempPath
              case linkResult of
                Right () -> pure (Right Installed)
                Left err
                  | isAlreadyExistsError err -> pure (Right AlreadyExists)
                  | otherwise -> pure (Left (ioErrorText err))

readBlob :: FilePath -> ContentId -> IO (Either SteveCASError ReadResult)
readBlob root contentId = do
  let path = blobPath root contentId
  existsResult <- try (doesFileExist path)
  case existsResult of
    Left err -> pure (Left (ioErrorText err))
    Right False -> pure (Right BlobNotFound)
    Right True -> do
      readResult <- try (ByteString.readFile path)
      case readResult of
        Right bytes -> pure (Right (BlobFound bytes))
        Left err
          | isDoesNotExistError err -> pure (Right BlobNotFound)
          | otherwise -> pure (Left (ioErrorText err))

blobPath :: FilePath -> ContentId -> FilePath
blobPath root = (root </>) . Text.unpack . renderContentId

tryRemove :: FilePath -> IO (Either IOException ())
tryRemove = try . removeFile

ioErrorText :: IOException -> SteveCASError
ioErrorText = StoreIOError . Text.pack . show
