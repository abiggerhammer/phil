{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Core.Authority
  ( AuthorityExerciseSource (..)
  , AuthorityState
  , CapabilityOccurrenceKey (..)
  , emptyAuthorityState
  , insertAuthorityCapability
  )
import Phil.Core.Syntax (Mode (..), runtimeBytesType)
import Phil.IO.Bytes
  ( makeRuntimeBytes
  , runtimeBytesSemanticType
  )
import Phil.IO.Console
  ( ConsoleEnvironment (..)
  , ConsoleFailure (..)
  , ConsoleWriteOutcome (..)
  , checkConsoleWrite
  , checkedConsoleWriteObservablePrefix
  , defaultConsoleAuthorityCapability
  , standardConsoleEnvironment
  )
import Phil.IO.FileSystem
  ( CheckedFileSystemReplace (..)
  , FileReadOutcome (..)
  , FileReplaceOutcome (..)
  , FileSystemFailure (..)
  , FileSystemOperation (..)
  , FileSystemState
  , checkFileSystemRead
  , checkFileSystemReplace
  , emptyFileSystemState
  , insertFileSystemBinding
  , makeFileSystemAuthorityCapability
  )
import Phil.IO.UTF8
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
        [ ("UTF-8 ASCII round-trip is exact", asciiRoundTrip)
        , ("UTF-8 multibyte round-trip is exact", multibyteRoundTrip)
        , ("UTF-8 preserves distinct Unicode scalar sequences", normalizationIsNotImplicit)
        , ("invalid UTF-8 rejects explicitly", invalidUTF8Rejects)
        , ("runtime UTF-8 bytes inhabit bare Bytes semantics", utf8BytesAreRuntimeBytes)
        , ("read_utf8 preserves the exact checked FileSystem.read", readUTF8PreservesProviderCall)
        , ("binary FileSystem.read does not silently decode", binaryReadDoesNotDecode)
        , ("read_utf8 preserves provider failures", readUTF8PreservesProviderFailure)
        , ("write_utf8 is exact encode plus FileSystem.replace", writeUTF8IsComposition)
        , ("write_utf8 success is process-observable on later binary read", writeUTF8IsObservable)
        , ("write_line is exact LF append plus ConsoleOutput.write", writeLineIsComposition)
        ]
  mapM_ report checks
  if all (either (const False) (const True) . snd) checks
    then pure ()
    else exitFailure
  where
    report (label, Right ()) = putStrLn ("PASS: IO-CODEC-001 " <> label)
    report (label, Left detail) = putStrLn ("FAIL: IO-CODEC-001 " <> label <> " -- " <> detail)

asciiRoundTrip :: Either String ()
asciiRoundTrip =
  assert (utf8Decode (utf8Encode "hello") == Right "hello")
    "ASCII UTF-8 round-trip changed text"

multibyteRoundTrip :: Either String ()
multibyteRoundTrip =
  let text = "λ Phil 🐿️"
  in assert (utf8Decode (utf8Encode text) == Right text)
      "multibyte UTF-8 round-trip changed text"

normalizationIsNotImplicit :: Either String ()
normalizationIsNotImplicit = do
  let composed = Text.pack ['c', 'a', 'f', '\x00e9']
      decomposed = Text.pack ['c', 'a', 'f', 'e', '\x0301']
      composedBytes = utf8Encode composed
      decomposedBytes = utf8Encode decomposed
  assert (composedBytes /= decomposedBytes)
    "distinct Unicode scalar sequences normalized during encode"
  assert (utf8Decode composedBytes == Right composed)
    "composed sequence changed during round-trip"
  assert (utf8Decode decomposedBytes == Right decomposed)
    "decomposed sequence changed during round-trip"

invalidUTF8Rejects :: Either String ()
invalidUTF8Rejects =
  assert (utf8Decode (makeRuntimeBytes [0xc3, 0x28]) == Left InvalidUTF8)
    "invalid UTF-8 did not return explicit DecodeError"

utf8BytesAreRuntimeBytes :: Either String ()
utf8BytesAreRuntimeBytes =
  assert (runtimeBytesSemanticType (utf8Encode "bytes") == runtimeBytesType)
    "UTF-8 encode escaped the bare runtime Bytes family"

readUTF8PreservesProviderCall :: Either String ()
readUTF8PreservesProviderCall = do
  (occurrence, path) <- workspacePath
  authority <- readAuthority occurrence
  let bytes = utf8Encode "hello λ"
      fsState = insertFileSystemBinding path bytes emptyFileSystemState
      observed = FileReadSucceeded bytes
  direct <- mapLeft show $ checkFileSystemRead
    occurrence path 64 (PossessedCapability fsReadCapability) authority fsState observed
  composed <- mapLeft show $ checkReadUTF8
    occurrence path 64 (PossessedCapability fsReadCapability) authority fsState observed
  assert (checkedReadUTF8FileRead composed == direct)
    "read_utf8 changed the checked provider call"
  assert (checkedReadUTF8Outcome composed == ReadUTF8Decoded "hello λ")
    "read_utf8 did not decode the successful binary result"

binaryReadDoesNotDecode :: Either String ()
binaryReadDoesNotDecode = do
  (occurrence, path) <- workspacePath
  authority <- readAuthority occurrence
  let invalid = makeRuntimeBytes [0xc3, 0x28]
      fsState = insertFileSystemBinding path invalid emptyFileSystemState
      observed = FileReadSucceeded invalid
  _ <- mapLeft show $ checkFileSystemRead
    occurrence path 8 (PossessedCapability fsReadCapability) authority fsState observed
  composed <- mapLeft show $ checkReadUTF8
    occurrence path 8 (PossessedCapability fsReadCapability) authority fsState observed
  assert (checkedReadUTF8Outcome composed == ReadUTF8DecodeFailed InvalidUTF8)
    "binary read acquired implicit text semantics"

readUTF8PreservesProviderFailure :: Either String ()
readUTF8PreservesProviderFailure = do
  (occurrence, path) <- workspacePath
  authority <- readAuthority occurrence
  composed <- mapLeft show $ checkReadUTF8
    occurrence path 8 (PossessedCapability fsReadCapability) authority emptyFileSystemState
    (FileReadFailed FileSystemNotFound)
  assert (checkedReadUTF8Outcome composed == ReadUTF8ProviderFailed FileSystemNotFound)
    "read_utf8 rewrote the provider failure"

writeUTF8IsComposition :: Either String ()
writeUTF8IsComposition = do
  (occurrence, path) <- workspacePath
  authority <- replaceAuthority occurrence
  let text = "write λ"
      bytes = utf8Encode text
      observed = FileReplaceFailed FileSystemDenied
  direct <- mapLeft show $ checkFileSystemReplace
    occurrence path bytes (PossessedCapability fsReplaceCapability)
    authority emptyFileSystemState observed
  composed <- mapLeft show $ checkWriteUTF8
    occurrence path (PossessedCapability fsReplaceCapability)
    authority emptyFileSystemState text observed
  assert (checkedWriteUTF8Bytes composed == bytes)
    "write_utf8 did not retain exact encoded bytes"
  assert (checkedWriteUTF8FileReplace composed == direct)
    "write_utf8 changed FileSystem.replace effect/authority/failure semantics"

writeUTF8IsObservable :: Either String ()
writeUTF8IsObservable = do
  (occurrence, path) <- workspacePath
  writeAuthority <- replaceAuthority occurrence
  readAuth <- readAuthority occurrence
  let text = "observable 🐿"
      bytes = utf8Encode text
  composed <- mapLeft show $ checkWriteUTF8
    occurrence path (PossessedCapability fsReplaceCapability)
    writeAuthority emptyFileSystemState text FileReplaceSucceeded
  let nextState = checkedFileSystemReplaceNextState
        (checkedWriteUTF8FileReplace composed)
  _ <- mapLeft show $ checkFileSystemRead
    occurrence path 128 (PossessedCapability fsReadCapability)
    readAuth nextState (FileReadSucceeded bytes)
  Right ()

writeLineIsComposition :: Either String ()
writeLineIsComposition = do
  let stdout = consoleEnvironmentStdout standardConsoleEnvironment
      observed = ConsoleWriteFailed ConsoleUnavailable 2
  capability <- mapLeft show $ defaultConsoleAuthorityCapability stdoutCapability stdout
  authority <- mapLeft show $ insertAuthorityCapability capability emptyAuthorityState
  direct <- mapLeft show $ checkConsoleWrite
    stdout (PossessedCapability stdoutCapability) authority "hi\n" observed
  composed <- mapLeft show $ checkWriteLine
    stdout (PossessedCapability stdoutCapability) authority "hi" observed
  assert (checkedWriteLineRequestedText composed == "hi\n")
    "write_line did not append exactly one LF"
  assert (checkedWriteLineConsoleWrite composed == direct)
    "write_line changed ConsoleOutput.write semantics"
  assert (checkedConsoleWriteObservablePrefix direct == "hi")
    "write_line lost partial-write progress"

workspacePath :: Either String (FileSystemOccurrence, ProviderRelativePath)
workspacePath = do
  occurrence <- mapLeft show (fileSystemOccurrence "filesystem.workspace")
  path <- mapLeft show (checkProviderRelativePath occurrence "text/message.txt")
  Right (occurrence, path)

readAuthority :: FileSystemOccurrence -> Either String AuthorityState
readAuthority occurrence =
  mapLeft show $ insertAuthorityCapability
    (makeFileSystemAuthorityCapability
      fsReadCapability Affine occurrence (Set.singleton FileSystemReadOp))
    emptyAuthorityState

replaceAuthority :: FileSystemOccurrence -> Either String AuthorityState
replaceAuthority occurrence =
  mapLeft show $ insertAuthorityCapability
    (makeFileSystemAuthorityCapability
      fsReplaceCapability Affine occurrence (Set.singleton FileSystemReplaceOp))
    emptyAuthorityState

fsReadCapability :: CapabilityOccurrenceKey
fsReadCapability = CapabilityOccurrenceKey "authority.fs.read"

fsReplaceCapability :: CapabilityOccurrenceKey
fsReplaceCapability = CapabilityOccurrenceKey "authority.fs.replace"

stdoutCapability :: CapabilityOccurrenceKey
stdoutCapability = CapabilityOccurrenceKey "authority.console.stdout"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
