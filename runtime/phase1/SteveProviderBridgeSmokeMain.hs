{-# LANGUAGE ForeignFunctionInterface #-}

module Main (main) where

import qualified Data.ByteString as ByteString
import qualified Data.ByteString.Char8 as Char8
import Foreign.C.Types (CInt (..))
import Foreign.Ptr (Ptr)
import Phil.Compiler.SteveCAS (computeContentId)
import SteveProviderBridge
  ( freeContentIdHandle
  , freeOwnedBytesHandle
  , newContentIdHandle
  , newOwnedBytesHandle
  )
import System.Directory
  ( createDirectoryIfMissing
  , doesFileExist
  , removePathForcibly
  )
import System.Exit (exitFailure)
import System.FilePath ((</>))
import System.IO.Error (catchIOError)

foreign import ccall "StevePut"
  nativeStevePut :: Ptr () -> IO CInt

foreign import ccall "SteveGet"
  nativeSteveGet :: Ptr () -> IO CInt

main :: IO ()
main = do
  cleanRoot
  createDirectoryIfMissing True storeRoot
  checks <- nativeLifecycle
  cleanRoot
  mapM_ report checks
  if all snd checks then pure () else exitFailure

nativeLifecycle :: IO [(String, Bool)]
nativeLifecycle = do
  let payload = Char8.pack "Steve native provider bridge artifact\n"
      contentId = computeContentId payload
      objectPath = storeRoot </> show contentId
  candidate <- newOwnedBytesHandle storeRoot payload
  firstPut <- nativeStevePut candidate
  secondPut <- nativeStevePut candidate
  freeOwnedBytesHandle candidate

  published <- doesFileExist objectPath
  storedBytes <- if published then ByteString.readFile objectPath else pure ByteString.empty

  contentHandle <- newContentIdHandle storeRoot contentId
  successfulGet <- nativeSteveGet contentHandle
  freeContentIdHandle contentHandle

  let missingId = computeContentId (Char8.pack "definitely absent")
  missingHandle <- newContentIdHandle storeRoot missingId
  missingGet <- nativeSteveGet missingHandle
  freeContentIdHandle missingHandle

  ByteString.writeFile objectPath (Char8.pack "tampered bytes")
  corruptHandle <- newContentIdHandle storeRoot contentId
  corruptGet <- nativeSteveGet corruptHandle
  freeContentIdHandle corruptHandle

  pure
    [ ("native StevePut publishes the exact CAS object", firstPut == 0 && published && storedBytes == payload)
    , ("native StevePut accepts idempotent no-replace reinstall", secondPut == 0)
    , ("native SteveGet reads and verifies the published object", successfulGet == 0)
    , ("native SteveGet reports a missing content ID as non-success", missingGet /= 0)
    , ("native SteveGet rejects content whose bytes no longer match its ID", corruptGet /= 0)
    ]

report :: (String, Bool) -> IO ()
report (label, ok) =
  putStrLn ((if ok then "PASS: " else "FAIL: ") <> "INT-006 " <> label)

storeRoot :: FilePath
storeRoot = "/tmp/phil-int006-steve-native-provider-bridge"

cleanRoot :: IO ()
cleanRoot = removePathForcibly storeRoot `catchIOError` const (pure ())
