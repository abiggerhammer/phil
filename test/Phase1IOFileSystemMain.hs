{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import Phil.Core.Authority
  ( AuthorityCheckError (..)
  , AuthorityExerciseSource (..)
  , AuthorityState
  , CapabilityOccurrenceKey (..)
  , emptyAuthorityState
  , insertAuthorityCapability
  )
import Phil.Core.Syntax (Mode (..), runtimeBytesType)
import Phil.IO.Bytes
import Phil.IO.FileSystem
import Phil.Systems
  ( FileSystemOccurrence
  , ProviderRelativePath
  , checkProviderRelativePath
  , fileSystemOccurrence
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  let checks =
        [ ("bounded read returns exact runtime Bytes", boundedReadSucceeds)
        , ("oversized read reports TooLarge instead of returning bytes", boundedReadRejectsOversize)
        , ("missing path reports explicit NotFound", missingPathIsExplicit)
        , ("portable negative read leaves semantic state unchanged", negativeReadPreservesState)
        , ("path from another FileSystem occurrence rejects", crossNamespacePathRejects)
        , ("read authority does not grant replace authority", readAuthorityDoesNotWrite)
        , ("replace authority does not grant read authority", writeAuthorityDoesNotRead)
        , ("successful replace is observable by subsequent read", replaceSuccessIsProcessObservable)
        , ("failed replace preserves previous binding exactly", replaceFailurePreservesBinding)
        , ("filesystem effects are indexed by exact occurrence and operation", effectsAreOccurrenceIndexed)
        , ("filesystem byte carrier inhabits bare runtime-sized Bytes", byteCarrierMatchesIOBytes)
        ]
  mapM_ report checks
  if all (either (const False) (const True) . snd) checks
    then pure ()
    else exitFailure
  where
    report (label, Right ()) = putStrLn ("PASS: IO-FS-001 " <> label)
    report (label, Left detail) = putStrLn ("FAIL: IO-FS-001 " <> label <> " -- " <> detail)

boundedReadSucceeds :: Either String ()
boundedReadSucceeds = do
  occurrence <- workspaceOccurrence
  path <- workspacePath occurrence
  let bytes = makeRuntimeBytes [1, 2, 3]
      state = insertFileSystemBinding path bytes emptyFileSystemState
  authority <- authorityState occurrence readCapability (Set.singleton FileSystemReadOp)
  checked <- mapLeft show $ checkFileSystemRead
    occurrence path 3 (PossessedCapability readCapability) authority state (FileReadSucceeded bytes)
  assert (checkedFileSystemReadOutcome checked == FileReadSucceeded bytes)
    "bounded read changed returned bytes"
  assert (checkedFileSystemReadState checked == state)
    "read mutated semantic filesystem state"

boundedReadRejectsOversize :: Either String ()
boundedReadRejectsOversize = do
  occurrence <- workspaceOccurrence
  path <- workspacePath occurrence
  let bytes = makeRuntimeBytes [1, 2, 3]
      state = insertFileSystemBinding path bytes emptyFileSystemState
  authority <- authorityState occurrence readCapability (Set.singleton FileSystemReadOp)
  _ <- mapLeft show $ checkFileSystemRead
    occurrence path 2 (PossessedCapability readCapability) authority state (FileReadFailed FileSystemTooLarge)
  case checkFileSystemRead
      occurrence path 2 (PossessedCapability readCapability) authority state (FileReadSucceeded bytes) of
    Left (FileSystemReadSuccessExceedsLimit 2 3) -> Right ()
    other -> Left ("oversized successful read was accepted: " <> show other)

missingPathIsExplicit :: Either String ()
missingPathIsExplicit = do
  occurrence <- workspaceOccurrence
  path <- workspacePath occurrence
  authority <- authorityState occurrence readCapability (Set.singleton FileSystemReadOp)
  checked <- mapLeft show $ checkFileSystemRead
    occurrence path 64 (PossessedCapability readCapability) authority emptyFileSystemState
    (FileReadFailed FileSystemNotFound)
  assert (checkedFileSystemReadOutcome checked == FileReadFailed FileSystemNotFound)
    "NotFound outcome changed"

negativeReadPreservesState :: Either String ()
negativeReadPreservesState = do
  occurrence <- workspaceOccurrence
  path <- workspacePath occurrence
  let bytes = makeRuntimeBytes [9, 8, 7]
      state = insertFileSystemBinding path bytes emptyFileSystemState
  authority <- authorityState occurrence readCapability (Set.singleton FileSystemReadOp)
  checked <- mapLeft show $ checkFileSystemRead
    occurrence path 64 (PossessedCapability readCapability) authority state
    (FileReadFailed FileSystemDenied)
  assert (checkedFileSystemReadState checked == state)
    "negative read mutated semantic filesystem state"
  assert (lookupFileSystemBinding path (checkedFileSystemReadState checked) == Just bytes)
    "negative read changed the existing binding"

crossNamespacePathRejects :: Either String ()
crossNamespacePathRejects = do
  left <- mapLeft show (fileSystemOccurrence "filesystem.left")
  right <- mapLeft show (fileSystemOccurrence "filesystem.right")
  path <- mapLeft show (checkProviderRelativePath left "shared/data.bin")
  authority <- authorityState right readCapability (Set.singleton FileSystemReadOp)
  case checkFileSystemRead right path 64 (PossessedCapability readCapability) authority
      emptyFileSystemState (FileReadFailed FileSystemNotFound) of
    Left (FileSystemPathOccurrenceMismatch expected actual) ->
      assert (expected == right && actual == left) "namespace mismatch named wrong occurrences"
    other -> Left ("cross-namespace path was accepted: " <> show other)

readAuthorityDoesNotWrite :: Either String ()
readAuthorityDoesNotWrite = do
  occurrence <- workspaceOccurrence
  path <- workspacePath occurrence
  authority <- authorityState occurrence readCapability (Set.singleton FileSystemReadOp)
  case checkFileSystemReplace occurrence path (makeRuntimeBytes [1])
      (PossessedCapability readCapability) authority emptyFileSystemState FileReplaceSucceeded of
    Left (FileSystemAuthorityError (AuthorityOperationNotPermitted _)) -> Right ()
    other -> Left ("read authority granted replace: " <> show other)

writeAuthorityDoesNotRead :: Either String ()
writeAuthorityDoesNotRead = do
  occurrence <- workspaceOccurrence
  path <- workspacePath occurrence
  authority <- authorityState occurrence writeCapability (Set.singleton FileSystemReplaceOp)
  case checkFileSystemRead occurrence path 64
      (PossessedCapability writeCapability) authority emptyFileSystemState
      (FileReadFailed FileSystemNotFound) of
    Left (FileSystemAuthorityError (AuthorityOperationNotPermitted _)) -> Right ()
    other -> Left ("replace authority granted read: " <> show other)

replaceSuccessIsProcessObservable :: Either String ()
replaceSuccessIsProcessObservable = do
  occurrence <- workspaceOccurrence
  path <- workspacePath occurrence
  let oldBytes = makeRuntimeBytes [1, 1]
      newBytes = makeRuntimeBytes [2, 2, 2]
      prior = insertFileSystemBinding path oldBytes emptyFileSystemState
  authority <- authorityState occurrence combinedCapability
    (Set.fromList [FileSystemReadOp, FileSystemReplaceOp])
  replaced <- mapLeft show $ checkFileSystemReplace
    occurrence path newBytes (PossessedCapability combinedCapability) authority prior
    FileReplaceSucceeded
  let next = checkedFileSystemReplaceNextState replaced
  assert (lookupFileSystemBinding path next == Just newBytes)
    "successful replace did not install supplied bytes"
  readBack <- mapLeft show $ checkFileSystemRead
    occurrence path 3 (PossessedCapability combinedCapability) authority next
    (FileReadSucceeded newBytes)
  assert (checkedFileSystemReadOutcome readBack == FileReadSucceeded newBytes)
    "subsequent read did not observe replacement"

replaceFailurePreservesBinding :: Either String ()
replaceFailurePreservesBinding = do
  occurrence <- workspaceOccurrence
  path <- workspacePath occurrence
  let oldBytes = makeRuntimeBytes [4, 5, 6]
      attempted = makeRuntimeBytes [7, 8, 9]
      prior = insertFileSystemBinding path oldBytes emptyFileSystemState
  authority <- authorityState occurrence writeCapability (Set.singleton FileSystemReplaceOp)
  checked <- mapLeft show $ checkFileSystemReplace
    occurrence path attempted (PossessedCapability writeCapability) authority prior
    (FileReplaceFailed FileSystemNoSpace)
  assert (checkedFileSystemReplaceNextState checked == prior)
    "failed replace changed semantic filesystem state"
  assert (lookupFileSystemBinding path (checkedFileSystemReplaceNextState checked) == Just oldBytes)
    "failed replace did not preserve previous binding"

effectsAreOccurrenceIndexed :: Either String ()
effectsAreOccurrenceIndexed = do
  left <- mapLeft show (fileSystemOccurrence "filesystem.left")
  right <- mapLeft show (fileSystemOccurrence "filesystem.right")
  let leftRead = fileSystemOperationEffect left FileSystemReadOp
      rightRead = fileSystemOperationEffect right FileSystemReadOp
      leftReplace = fileSystemOperationEffect left FileSystemReplaceOp
  assert (leftRead /= rightRead) "different filesystem occurrences shared one read effect"
  assert (leftRead /= leftReplace) "read and replace effects collapsed"

byteCarrierMatchesIOBytes :: Either String ()
byteCarrierMatchesIOBytes = do
  let bytes = makeRuntimeBytes [0, 255]
  assert (runtimeBytesSemanticType bytes == runtimeBytesType)
    "filesystem byte carrier does not inhabit runtime-sized Bytes"
  assert (runtimeBytesLength bytes == 2) "runtime byte length changed"

workspaceOccurrence :: Either String FileSystemOccurrence
workspaceOccurrence = mapLeft show (fileSystemOccurrence "filesystem.workspace")

workspacePath :: FileSystemOccurrence -> Either String ProviderRelativePath
workspacePath occurrence = mapLeft show (checkProviderRelativePath occurrence "data/blob.bin")

authorityState
  :: FileSystemOccurrence
  -> CapabilityOccurrenceKey
  -> Set.Set FileSystemOperation
  -> Either String AuthorityState
authorityState occurrence key operations =
  mapLeft show $ insertAuthorityCapability
    (makeFileSystemAuthorityCapability key Affine occurrence operations)
    emptyAuthorityState

readCapability :: CapabilityOccurrenceKey
readCapability = CapabilityOccurrenceKey "authority.filesystem.workspace.read"

writeCapability :: CapabilityOccurrenceKey
writeCapability = CapabilityOccurrenceKey "authority.filesystem.workspace.replace"

combinedCapability :: CapabilityOccurrenceKey
combinedCapability = CapabilityOccurrenceKey "authority.filesystem.workspace.read-replace"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
