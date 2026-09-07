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
checkFileSystemRead occurrence path limit authoritySource authorityState state observed = do
  requirePathOccurrence occurrence path
  if limit < 0
    then Left (FileSystemNegativeReadLimit limit)
    else pure ()
  _ <- mapLeft FileSystemAuthorityError $
    checkAuthorityExercise
      (fileSystemAuthorityRequirement occurrence FileSystemReadOp)
      authoritySource
      authorityState
  checkReadOutcome limit state path observed
  Right CheckedFileSystemRead
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
checkFileSystemReplace occurrence path bytes authoritySource authorityState prior observed = do
  requirePathOccurrence occurrence path
  _ <- mapLeft FileSystemAuthorityError $
    checkAuthorityExercise
      (fileSystemAuthorityRequirement occurrence FileSystemReplaceOp)
      authoritySource
      authorityState
  let next = case observed of
        FileReplaceSucceeded -> insertFileSystemBinding path bytes prior
        FileReplaceFailed _ -> prior
  Right CheckedFileSystemReplace
    { checkedFileSystemReplaceOccurrence = occurrence
    , checkedFileSystemReplacePath = path
    , checkedFileSystemReplaceBytes = bytes
    , checkedFileSystemReplaceOutcome = observed
    , checkedFileSystemReplaceEffect = fileSystemOperationEffect occurrence FileSystemReplaceOp
    , checkedFileSystemReplacePriorState = prior
    , checkedFileSystemReplaceNextState = next
    }

checkReadOutcome
  :: Int
  -> FileSystemState
  -> ProviderRelativePath
  -> FileReadOutcome
  -> Either FileSystemCheckError ()
checkReadOutcome limit state path observed =
  case observed of
    FileReadSucceeded bytes ->
      case lookupFileSystemBinding path state of
        Nothing -> Left FileSystemReadSuccessMissingBinding
        Just expected
          | bytes /= expected -> Left (FileSystemReadSuccessContentMismatch expected bytes)
          | runtimeBytesLength bytes > limit ->
              Left (FileSystemReadSuccessExceedsLimit limit (runtimeBytesLength bytes))
          | otherwise -> Right ()
    FileReadFailed FileSystemTooLarge ->
      case lookupFileSystemBinding path state of
        Just bytes
          | runtimeBytesLength bytes > limit -> Right ()
          | otherwise -> Left (FileSystemReadTooLargeMismatch limit (Just (runtimeBytesLength bytes)))
        Nothing -> Left (FileSystemReadTooLargeMismatch limit Nothing)
    FileReadFailed FileSystemNotFound ->
      case lookupFileSystemBinding path state of
        Nothing -> Right ()
        Just _ -> Left FileSystemReadNotFoundMismatch
    FileReadFailed _ -> Right ()

requirePathOccurrence
  :: FileSystemOccurrence
  -> ProviderRelativePath
  -> Either FileSystemCheckError ()
requirePathOccurrence expected path
  | providerRelativePathOccurrence path == expected = Right ()
  | otherwise = Left
      (FileSystemPathOccurrenceMismatch expected (providerRelativePathOccurrence path))

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

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
