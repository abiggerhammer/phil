{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString.Char8 as ByteString
import qualified Data.Text as Text
import Phil.Compiler.SteveCAS
import System.Directory
  ( listDirectory
  , removePathForcibly
  )
import System.Exit (exitFailure)
import System.IO.Error (catchIOError)

main :: IO ()
main = do
  cleanRoot
  checks <- sequence
    [ pure ("SHA-256 known vector", knownVector)
    , pure ("content-id text round trip", contentIdRoundTrip)
    , installAndRead
    ]
  cleanRoot
  mapM_ report checks
  if all snd checks then pure () else exitFailure

report :: (String, Bool) -> IO ()
report (label, ok) =
  putStrLn ((if ok then "PASS: " else "FAIL: ") <> "INT-006 " <> label)

knownVector :: Bool
knownVector =
  renderContentId (computeContentId "abc")
    == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"

contentIdRoundTrip :: Bool
contentIdRoundTrip =
  let contentId = computeContentId "round-trip"
  in parseContentId (Text.toUpper (renderContentId contentId)) == Right contentId
      && case parseContentId "not-a-content-id" of
        Left InvalidContentId {} -> True
        _ -> False

installAndRead :: IO (String, Bool)
installAndRead = do
  let payload = ByteString.pack "Steve CAS real artifact\n"
      altered = ByteString.pack "different bytes\n"
      contentId = computeContentId payload
      missingId = computeContentId "missing"
  first <- installBlob storeRoot contentId payload
  second <- installBlob storeRoot contentId payload
  mismatch <- installBlob storeRoot contentId altered
  readBack <- readBlob storeRoot contentId
  missing <- readBlob storeRoot missingId
  entries <- listDirectory storeRoot
  let stored = case readBack of
        Right (BlobFound bytes) ->
          bytes == payload && checkContentId contentId bytes
        _ -> False
      mismatchRejected = case mismatch of
        Left InstallContentDigestMismatch {} -> True
        _ -> False
      onlyPublishedObject = entries == [Text.unpack (renderContentId contentId)]
      ok = first == Right Installed
        && second == Right AlreadyExists
        && mismatchRejected
        && stored
        && missing == Right BlobNotFound
        && onlyPublishedObject
  pure ("real CAS install/read/no-replace lifecycle", ok)

storeRoot :: FilePath
storeRoot = "/tmp/phil-int006-steve-cas"

cleanRoot :: IO ()
cleanRoot = catchIOError (removePathForcibly storeRoot) (const (pure ()))
