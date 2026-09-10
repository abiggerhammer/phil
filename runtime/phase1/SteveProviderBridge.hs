{-# LANGUAGE ForeignFunctionInterface #-}

module SteveProviderBridge
  ( newOwnedBytesHandle
  , newContentIdHandle
  , freeOwnedBytesHandle
  , freeContentIdHandle
  ) where

import qualified Data.ByteString as ByteString
import Data.ByteString (ByteString)
import Foreign.C.Types (CInt)
import Foreign.Ptr (Ptr)
import Foreign.StablePtr
  ( StablePtr
  , castPtrToStablePtr
  , castStablePtrToPtr
  , deRefStablePtr
  , freeStablePtr
  , newStablePtr
  )
import Foreign.Storable (poke)
import Phil.Compiler.SteveCAS
  ( ContentId
  , InstallResult (..)
  , ReadResult (..)
  , checkContentId
  , computeContentId
  , installBlob
  , readBlob
  )

-- | Host representation for Phil's OwnedBytes value at the Steve provider ABI.
-- The store root is capability context carried by the opaque handle, rather
-- than ambient mutable provider state. Provider calls therefore remain fully
-- determined by their explicit ABI arguments.
data NativeOwnedBytes = NativeOwnedBytes
  { nativeBytesRoot :: FilePath
  , nativeBytesPayload :: ByteString
  }

-- | Host representation for ContentId[SHA256]. The same provider capability
-- context follows values produced by DigestProvider.compute and supplied to
-- BlobProvider/read/check operations.
data NativeContentId = NativeContentId
  { nativeContentRoot :: FilePath
  , nativeContentId :: ContentId
  }

newOwnedBytesHandle :: FilePath -> ByteString -> IO (Ptr ())
newOwnedBytesHandle root bytes =
  castStablePtrToPtr <$> newStablePtr (NativeOwnedBytes root bytes)

newContentIdHandle :: FilePath -> ContentId -> IO (Ptr ())
newContentIdHandle root contentId =
  castStablePtrToPtr <$> newStablePtr (NativeContentId root contentId)

freeOwnedBytesHandle :: Ptr () -> IO ()
freeOwnedBytesHandle = freeStablePtr . ownedBytesStablePtr

freeContentIdHandle :: Ptr () -> IO ()
freeContentIdHandle = freeStablePtr . contentIdStablePtr

foreign export ccall
  "phil_runtime_choice_StevePut_put_entry_DigestProvider_compute"
  steveDigestCompute
    :: Ptr () -> Ptr (Ptr ()) -> IO CInt

steveDigestCompute :: Ptr () -> Ptr (Ptr ()) -> IO CInt
steveDigestCompute candidatePtr resultSlot = do
  candidate <- deRefStablePtr (ownedBytesStablePtr candidatePtr)
  let contentId = computeContentId (nativeBytesPayload candidate)
  resultPtr <- newContentIdHandle (nativeBytesRoot candidate) contentId
  poke resultSlot resultPtr
  pure digestComputedTag

foreign export ccall
  "phil_runtime_choice_StevePut_put_install_BlobProvider_install_if_absent"
  steveBlobInstallIfAbsent
    :: Ptr () -> Ptr () -> IO CInt

steveBlobInstallIfAbsent :: Ptr () -> Ptr () -> IO CInt
steveBlobInstallIfAbsent contentIdPtr candidatePtr = do
  content <- deRefStablePtr (contentIdStablePtr contentIdPtr)
  candidate <- deRefStablePtr (ownedBytesStablePtr candidatePtr)
  if nativeContentRoot content /= nativeBytesRoot candidate
    then pure installStorageFailureTag
    else do
      result <- installBlob
        (nativeContentRoot content)
        (nativeContentId content)
        (nativeBytesPayload candidate)
      case result of
        Right AlreadyExists -> pure installAlreadyExistsTag
        Right Installed -> pure installInstalledTag
        Left _ -> pure installStorageFailureTag

foreign export ccall
  "phil_runtime_choice_SteveGet_get_entry_BlobProvider_read"
  steveBlobRead
    :: Ptr () -> Ptr (Ptr ()) -> IO CInt

steveBlobRead :: Ptr () -> Ptr (Ptr ()) -> IO CInt
steveBlobRead contentIdPtr resultSlot = do
  content <- deRefStablePtr (contentIdStablePtr contentIdPtr)
  result <- readBlob (nativeContentRoot content) (nativeContentId content)
  case result of
    Right (BlobFound bytes) -> do
      resultPtr <- newOwnedBytesHandle (nativeContentRoot content) bytes
      poke resultSlot resultPtr
      pure readFoundTag
    Right BlobNotFound -> pure readNotFoundTag
    Left _ -> pure readStorageFailureTag

foreign export ccall
  "phil_runtime_choice_SteveGet_get_check_DigestProvider_check"
  steveDigestCheck
    :: Ptr () -> Ptr () -> IO CInt

steveDigestCheck :: Ptr () -> Ptr () -> IO CInt
steveDigestCheck contentIdPtr bytesPtr = do
  content <- deRefStablePtr (contentIdStablePtr contentIdPtr)
  bytes <- deRefStablePtr (ownedBytesStablePtr bytesPtr)
  if nativeContentRoot content == nativeBytesRoot bytes
      && checkContentId (nativeContentId content) (nativeBytesPayload bytes)
    then pure digestAcceptedTag
    else pure digestRejectedTag

foreign export ccall "phil_runtime_release"
  steveReleaseOwnedBytes :: Ptr () -> IO ()

steveReleaseOwnedBytes :: Ptr () -> IO ()
steveReleaseOwnedBytes = freeOwnedBytesHandle

ownedBytesStablePtr :: Ptr () -> StablePtr NativeOwnedBytes
ownedBytesStablePtr = castPtrToStablePtr

contentIdStablePtr :: Ptr () -> StablePtr NativeContentId
contentIdStablePtr = castPtrToStablePtr

-- Canonical tags are fixed by the certified ascending-label ABI plan from #888.
digestComputedTag :: CInt
digestComputedTag = 0

installAlreadyExistsTag, installInstalledTag, installStorageFailureTag :: CInt
installAlreadyExistsTag = 0
installInstalledTag = 1
installStorageFailureTag = 2

readFoundTag, readNotFoundTag, readStorageFailureTag :: CInt
readFoundTag = 0
readNotFoundTag = 1
readStorageFailureTag = 2

digestAcceptedTag, digestRejectedTag :: CInt
digestAcceptedTag = 0
digestRejectedTag = 1
