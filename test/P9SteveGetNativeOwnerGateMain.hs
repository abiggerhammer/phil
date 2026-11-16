{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Exception (bracket)
import Control.Monad (unless)
import qualified Data.ByteString.Char8 as Bytes
import Foreign (Ptr, alloca, peek)
import Foreign.C.Types (CInt (..))
import Phil.Compiler.SteveCAS (InstallResult (..), installBlob)
import SteveProviderBridge
  ( freeContentIdHandle, freeOwnedBytesHandle
  , newContentIdHandle, newOwnedBytesHandle, providerComputeContentId
  )
import System.Directory
  ( createDirectory, getTemporaryDirectory, removeFile, removePathForcibly )
import System.IO (hClose, openTempFile)

foreign import ccall unsafe
  "phil_runtime_choice_SteveGet_get_entry_BlobProvider_read"
  readCall :: Ptr () -> Ptr (Ptr ()) -> IO CInt
foreign import ccall unsafe
  "phil_runtime_choice_SteveGet_get_check_DigestProvider_check"
  checkCall :: Ptr () -> Ptr () -> IO CInt

main :: IO ()
main = tempRoot $ \root -> do
  let bytes = Bytes.pack "same bytes from distinct read results"
      contentId = providerComputeContentId bytes
  result <- installBlob root contentId bytes
  case result of
    Right Installed -> pure ()
    other -> fail ("install failed: " <> show other)
  idA <- newContentIdHandle root contentId
  idB <- newContentIdHandle root contentId
  ownerA <- found idA
  ownerB <- found idB
  expect "selected owner A" 0 =<< checkCall idA ownerA
  expect "selected owner B" 0 =<< checkCall idB ownerB
  expect "B swapped for A" 1 =<< checkCall idA ownerB
  expect "A swapped for B" 1 =<< checkCall idB ownerA
  unrelated <- newOwnedBytesHandle root bytes
  expect "same-content unselected allocation" 1 =<< checkCall idA unrelated
  freeOwnedBytesHandle unrelated
  ownerA2 <- found idA
  expect "previous result after new read" 1 =<< checkCall idA ownerA
  expect "new result after new read" 0 =<< checkCall idA ownerA2
  freeOwnedBytesHandle ownerA
  freeOwnedBytesHandle ownerA2
  freeOwnedBytesHandle ownerB
  freeContentIdHandle idA
  freeContentIdHandle idB
  putStrLn "native Steve owner substitution rejected"

expect :: String -> CInt -> CInt -> IO ()
expect label expected actual =
  unless (expected == actual) $
    fail (label <> ": " <> show expected <> " /= " <> show actual)

found :: Ptr () -> IO (Ptr ())
found content = alloca $ \slot -> do
  tag <- readCall content slot
  expect "read.found tag" 0 tag
  peek slot

tempRoot :: (FilePath -> IO a) -> IO a
tempRoot = bracket make removePathForcibly
  where
    make = do
      tmp <- getTemporaryDirectory
      (path, h) <- openTempFile tmp "phil-p9-owner-"
      hClose h
      removeFile path
      createDirectory path
      pure path
