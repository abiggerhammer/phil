{-# LANGUAGE ForeignFunctionInterface #-}

module SteveProviderBridge
  ( newOwnedBytesHandle
  , newContentIdHandle
  , freeOwnedBytesHandle
  , freeContentIdHandle
  , providerComputeContentId
  , providerReadBlob
  , providerCheckContentId
  ) where

import Control.Concurrent.MVar (MVar, modifyMVar_, newMVar, withMVar)
import Data.ByteString (ByteString)
import Data.IORef (IORef, atomicModifyIORef', newIORef, writeIORef)
import Foreign.C.Types (CInt (..))
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
  , SteveCASError
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
  , nativeOwnerLive :: MVar Bool
  }

-- | Host representation for ContentId[SHA256]. The same provider capability
-- context follows values produced by DigestProvider.compute and supplied to
-- BlobProvider/read/check operations.
data NativeContentId = NativeContentId
  { nativeContentRoot :: FilePath
  , nativeContentId :: ContentId
  , nativeSelectedOwner :: IORef (Maybe (Ptr (), NativeOwnedBytes))
  }

newOwnedBytesHandle :: FilePath -> ByteString -> IO (Ptr ())
newOwnedBytesHandle root bytes = do
  live <- newMVar True
  castStablePtrToPtr <$> newStablePtr (NativeOwnedBytes root bytes live)

newContentIdHandle :: FilePath -> ContentId -> IO (Ptr ())
newContentIdHandle root contentId = do
  selected <- newIORef Nothing
  castStablePtrToPtr <$> newStablePtr (NativeContentId root contentId selected)

freeOwnedBytesHandle :: Ptr () -> IO ()
freeOwnedBytesHandle ptr = do
  owner <- deRefStablePtr (ownedBytesStablePtr ptr)
  modifyMVar_ (nativeOwnerLive owner) (const (pure False))
  freeStablePtr (ownedBytesStablePtr ptr)

freeContentIdHandle :: Ptr () -> IO ()
freeContentIdHandle = freeStablePtr . contentIdStablePtr

-- | Haskell-side entry points for the same conventional provider realization
-- exported below through the qualified Phase-1 C ABI. The public Steve shell
-- uses these for its source-level digest/read/check primitives so the command
-- path and the compiled Steve callables do not silently select different
-- provider implementations.
providerComputeContentId :: ByteString -> ContentId
providerComputeContentId = computeContentId

providerReadBlob
  :: FilePath
  -> ContentId
  -> IO (Either SteveCASError ReadResult)
providerReadBlob = readBlob

providerCheckContentId :: ContentId -> ByteString -> Bool
providerCheckContentId = checkContentId

foreign export ccall
  "phil_runtime_choice_StevePut_put_entry_DigestProvider_compute"
  steveDigestCompute
    :: Ptr () -> Ptr (Ptr ()) -> IO CInt

steveDigestCompute :: Ptr () -> Ptr (Ptr ()) -> IO CInt
steveDigestCompute candidatePtr resultSlot = do
  candidate <- deRefStablePtr (ownedBytesStablePtr candidatePtr)
  let contentId = providerComputeContentId (nativeBytesPayload candidate)
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
  writeIORef (nativeSelectedOwner content) Nothing
  result <- providerReadBlob (nativeContentRoot content) (nativeContentId content)
  case result of
    Right (BlobFound bytes) -> do
      resultPtr <- newOwnedBytesHandle (nativeContentRoot content) bytes
      owner <- deRefStablePtr (ownedBytesStablePtr resultPtr)
      writeIORef (nativeSelectedOwner content) (Just (resultPtr, owner))
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
  -- The selected pointer and owned record come ONLY from the actual native
  -- read.found producer. Do not dereference caller-supplied bytesPtr: a
  -- swapped, null, released or foreign pointer must be rejected as a value,
  -- not interpreted as an arbitrary StablePtr before identity checking.
  -- A mismatch leaves the rightful selection available; a match consumes
  -- it atomically even if the digest itself rejects.
  selected <- atomicModifyIORef' (nativeSelectedOwner content) $ \current ->
    case current of
      Just (selectedPtr, owner) | selectedPtr == bytesPtr ->
        (Nothing, Just owner)
      _ -> (current, Nothing)
  case selected of
    Nothing -> pure digestRejectedTag
    Just bytes ->
      -- Release takes the same owner lock, so the selected byte object
      -- cannot become released between the live check and digest invocation.
      -- This is a native lifetime gate, not source-loan/linked-build proof.
      withMVar (nativeOwnerLive bytes) $ \live ->
        pure $ if live
          && nativeContentRoot content == nativeBytesRoot bytes
          && providerCheckContentId (nativeContentId content) (nativeBytesPayload bytes)
          then digestAcceptedTag
          else digestRejectedTag

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
