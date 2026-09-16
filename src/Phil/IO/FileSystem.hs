{-# LANGUAGE OverloadedStrings #-}

module Phil.IO.FileSystem
  ( FileSystemOperation (..)
  , FileSystemFailure (..)
  , FileReadOutcome (..)
  , FileReplaceOutcome (..)
  , FileSystemState
  , CheckedFileSystemRead (..)
  , CheckedFileSystemReplace (..)
  , FileSystemCheckError (..)
  , emptyFileSystemState
  , insertFileSystemBinding
  , lookupFileSystemBinding
  , makeFileSystemAuthorityCapability
  , fileSystemOperationEffect
  , checkFileSystemRead
  , checkFileSystemReplace
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified FileSystemKernel as Kernel
import Phil.Core.Authority
  ( AuthorityCapability (..)
  , AuthorityCheckError
  , AuthorityContractKey (..)
  , AuthorityExerciseSource
  , AuthorityOperationKey (..)
  , AuthorityRequirement (..)
  , AuthorityState
  , AuthoritySubjectKey (..)
  , CapabilityOccurrenceKey
  , checkAuthorityExercise
  )
import Phil.Core.Callable (SemanticEffect (..))
import Phil.Core.Syntax (Mode)
import Phil.IO.Bytes
  ( RuntimeBytes
  , runtimeBytesLength
  )
import Phil.Systems
  ( FileSystemOccurrence
  , ProviderRelativePath
  , providerRelativePathOccurrence
  , unFileSystemOccurrence
  )

data FileSystemOperation
  = FileSystemReadOp
  | FileSystemReplaceOp
  deriving (Eq, Ord, Show)

data FileSystemFailure
  = FileSystemNotFound
  | FileSystemDenied
  | FileSystemTooLarge
  | FileSystemExhausted
  | FileSystemNoSpace
  | FileSystemInvalid
  | FileSystemUnsupported
  | FileSystemUnavailable
  | FileSystemOther Text
  deriving (Eq, Ord, Show)

data FileReadOutcome
  = FileReadSucceeded RuntimeBytes
  | FileReadFailed FileSystemFailure
  deriving (Eq, Ord, Show)

data FileReplaceOutcome
  = FileReplaceSucceeded
  | FileReplaceFailed FileSystemFailure
  deriving (Eq, Ord, Show)

newtype FileSystemState = FileSystemState
  { fileSystemBindings :: Map ProviderRelativePath RuntimeBytes
  }
  deriving (Eq, Ord, Show)

data CheckedFileSystemRead = CheckedFileSystemRead
  { checkedFileSystemReadOccurrence :: FileSystemOccurrence
  , checkedFileSystemReadPath :: ProviderRelativePath
  , checkedFileSystemReadLimit :: Int
  , checkedFileSystemReadOutcome :: FileReadOutcome
  , checkedFileSystemReadEffect :: SemanticEffect
  , checkedFileSystemReadState :: FileSystemState
  }
  deriving (Eq, Ord, Show)

data CheckedFileSystemReplace = CheckedFileSystemReplace
  { checkedFileSystemReplaceOccurrence :: FileSystemOccurrence
  , checkedFileSystemReplacePath :: ProviderRelativePath
  , checkedFileSystemReplaceBytes :: RuntimeBytes
  , checkedFileSystemReplaceOutcome :: FileReplaceOutcome
  , checkedFileSystemReplaceEffect :: SemanticEffect
  , checkedFileSystemReplacePriorState :: FileSystemState
  , checkedFileSystemReplaceNextState :: FileSystemState
  }
  deriving (Eq, Ord, Show)

data FileSystemCheckError
  = FileSystemAuthorityError AuthorityCheckError
  | FileSystemPathOccurrenceMismatch FileSystemOccurrence FileSystemOccurrence
  | FileSystemNegativeReadLimit Int
  | FileSystemReadSuccessMissingBinding
  | FileSystemReadSuccessContentMismatch RuntimeBytes RuntimeBytes
  | FileSystemReadSuccessExceedsLimit Int Int
  | FileSystemReadTooLargeMismatch Int (Maybe Int)
  | FileSystemReadNotFoundMismatch
  | FileSystemKernelInvariantViolation Text
  deriving (Eq, Ord, Show)

emptyFileSystemState :: FileSystemState
emptyFileSystemState = FileSystemState Map.empty

insertFileSystemBinding
  :: ProviderRelativePath
  -> RuntimeBytes
  -> FileSystemState
  -> FileSystemState
insertFileSystemBinding path bytes (FileSystemState bindings) =
  FileSystemState (Map.insert path bytes bindings)

lookupFileSystemBinding
  :: ProviderRelativePath
  -> FileSystemState
  -> Maybe RuntimeBytes
lookupFileSystemBinding path = Map.lookup path . fileSystemBindings

makeFileSystemAuthorityCapability
  :: CapabilityOccurrenceKey
  -> Mode
  -> FileSystemOccurrence
  -> Set.Set FileSystemOperation
  -> AuthorityCapability
makeFileSystemAuthorityCapability capabilityKey mode occurrence operations =
  AuthorityCapability
    { authorityCapabilityOccurrence = capabilityKey
    , authorityCapabilityContract = fileSystemAuthorityContract
    , authorityCapabilitySubject = fileSystemAuthoritySubject occurrence
    , authorityCapabilityMode = mode
    , authorityCapabilityOperations = Set.map fileSystemAuthorityOperation operations
    }

fileSystemOperationEffect
  :: FileSystemOccurrence
  -> FileSystemOperation
  -> SemanticEffect
fileSystemOperationEffect occurrence operation = SemanticEffect
  ("phil.effect.filesystem.v1:"
    <> unFileSystemOccurrence occurrence
    <> ":"
    <> operationText operation)

checkFileSystemRead
  :: FileSystemOccurrence
  -> ProviderRelativePath
  -> Int
  -> AuthorityExerciseSource
  -> AuthorityState
  -> FileSystemState
  -> FileReadOutcome
  -> Either FileSystemCheckError CheckedFileSystemRead
checkFileSystemRead occurrence path limit authoritySource authorityState state observed =
  let actualOccurrence = providerRelativePathOccurrence path
      pathOccurrenceMatches = actualOccurrence == occurrence
      limitNonnegative = limit >= 0
      authorityResult =
        checkAuthorityExercise
          (fileSystemAuthorityRequirement occurrence FileSystemReadOp)
          authoritySource
          authorityState
      authorityAccepted = either (const False) (const True) authorityResult
      binding = lookupFileSystemBinding path state
      bindingPresent = maybe False (const True) binding
      contentMatches = case (observed, binding) of
        (FileReadSucceeded bytes, Just expected) -> bytes == expected
        _ -> False
      withinLimit = maybe False ((<= limit) . runtimeBytesLength) binding
      decision = Kernel.decideFileSystemReadByFacts
        pathOccurrenceMatches
        limitNonnegative
        authorityAccepted
        (kernelObservedReadKind observed)
        bindingPresent
        contentMatches
        withinLimit
  in case decision of
    Kernel.FileSystemReadPathOccurrenceMismatch ->
      Left (FileSystemPathOccurrenceMismatch occurrence actualOccurrence)
    Kernel.FileSystemReadNegativeLimit ->
      Left (FileSystemNegativeReadLimit limit)
    Kernel.FileSystemReadAuthorityRejected ->
      authorityFailure "read" authorityResult
    Kernel.FileSystemReadSuccessMissingBinding ->
      Left FileSystemReadSuccessMissingBinding
    Kernel.FileSystemReadSuccessContentMismatch ->
      case (binding, observed) of
        (Just expected, FileReadSucceeded bytes) ->
          Left (FileSystemReadSuccessContentMismatch expected bytes)
        _ -> kernelInvariant "content mismatch decision lacked concrete success/binding facts"
    Kernel.FileSystemReadSuccessExceedsLimit ->
      case observed of
        FileReadSucceeded bytes ->
          Left (FileSystemReadSuccessExceedsLimit limit (runtimeBytesLength bytes))
        _ -> kernelInvariant "success-exceeds-limit decision lacked a successful read"
    Kernel.FileSystemReadTooLargeMismatch ->
      Left (FileSystemReadTooLargeMismatch limit (runtimeBytesLength <$> binding))
    Kernel.FileSystemReadNotFoundMismatch ->
      Left FileSystemReadNotFoundMismatch
    Kernel.FileSystemReadAccepted ->
      case authorityResult of
        Left _ -> kernelInvariant "read accepted although native authority checker rejected"
        Right _ -> Right CheckedFileSystemRead
          { checkedFileSystemReadOccurrence = occurrence
          , checkedFileSystemReadPath = path
          , checkedFileSystemReadLimit = limit
          , checkedFileSystemReadOutcome = observed
          , checkedFileSystemReadEffect = fileSystemOperationEffect occurrence FileSystemReadOp
          , checkedFileSystemReadState = state
          }

checkFileSystemReplace
  :: FileSystemOccurrence
  -> ProviderRelativePath
  -> RuntimeBytes
  -> AuthorityExerciseSource
  -> AuthorityState
  -> FileSystemState
  -> FileReplaceOutcome
  -> Either FileSystemCheckError CheckedFileSystemReplace
checkFileSystemReplace occurrence path bytes authoritySource authorityState prior observed =
  let actualOccurrence = providerRelativePathOccurrence path
      pathOccurrenceMatches = actualOccurrence == occurrence
      authorityResult =
        checkAuthorityExercise
          (fileSystemAuthorityRequirement occurrence FileSystemReplaceOp)
          authoritySource
          authorityState
      authorityAccepted = either (const False) (const True) authorityResult
      decision = Kernel.decideFileSystemReplaceByFacts
        pathOccurrenceMatches
        authorityAccepted
  in case decision of
    Kernel.FileSystemReplacePathOccurrenceMismatch ->
      Left (FileSystemPathOccurrenceMismatch occurrence actualOccurrence)
    Kernel.FileSystemReplaceAuthorityRejected ->
      authorityFailure "replace" authorityResult
    Kernel.FileSystemReplaceAccepted ->
      case authorityResult of
        Left _ -> kernelInvariant "replace accepted although native authority checker rejected"
        Right _ ->
          let observedSuccess = case observed of
                FileReplaceSucceeded -> True
                FileReplaceFailed _ -> False
              next =
                if Kernel.replaceShouldInstallBinding observedSuccess
                  then insertFileSystemBinding path bytes prior
                  else prior
          in Right CheckedFileSystemReplace
            { checkedFileSystemReplaceOccurrence = occurrence
            , checkedFileSystemReplacePath = path
            , checkedFileSystemReplaceBytes = bytes
            , checkedFileSystemReplaceOutcome = observed
            , checkedFileSystemReplaceEffect = fileSystemOperationEffect occurrence FileSystemReplaceOp
            , checkedFileSystemReplacePriorState = prior
            , checkedFileSystemReplaceNextState = next
            }

kernelObservedReadKind :: FileReadOutcome -> Kernel.FileSystemObservedReadKind
kernelObservedReadKind observed = case observed of
  FileReadSucceeded _ -> Kernel.ObservedReadSuccess
  FileReadFailed FileSystemTooLarge -> Kernel.ObservedReadTooLarge
  FileReadFailed FileSystemNotFound -> Kernel.ObservedReadNotFound
  FileReadFailed _ -> Kernel.ObservedReadPortableNegative

authorityFailure
  :: Text
  -> Either AuthorityCheckError a
  -> Either FileSystemCheckError b
authorityFailure operation result = case result of
  Left detail -> Left (FileSystemAuthorityError detail)
  Right _ -> kernelInvariant
    ("kernel rejected " <> operation <> " authority although native authority checker accepted")

kernelInvariant :: Text -> Either FileSystemCheckError a
kernelInvariant = Left . FileSystemKernelInvariantViolation

fileSystemAuthorityContract :: AuthorityContractKey
fileSystemAuthorityContract = AuthorityContractKey "phil.io.filesystem.v1"

fileSystemAuthoritySubject :: FileSystemOccurrence -> AuthoritySubjectKey
fileSystemAuthoritySubject = AuthoritySubjectKey . unFileSystemOccurrence

fileSystemAuthorityOperation :: FileSystemOperation -> AuthorityOperationKey
fileSystemAuthorityOperation = AuthorityOperationKey . operationText

fileSystemAuthorityRequirement
  :: FileSystemOccurrence
  -> FileSystemOperation
  -> AuthorityRequirement
fileSystemAuthorityRequirement occurrence operation = AuthorityRequirement
  { requiredAuthorityContract = fileSystemAuthorityContract
  , requiredAuthoritySubject = fileSystemAuthoritySubject occurrence
  , requiredAuthorityOperation = fileSystemAuthorityOperation operation
  }

operationText :: FileSystemOperation -> Text
operationText operation = case operation of
  FileSystemReadOp -> "read"
  FileSystemReplaceOp -> "replace"
