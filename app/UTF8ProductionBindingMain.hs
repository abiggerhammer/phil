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
import Phil.Core.Syntax (Mode (..))
import Phil.IO.Bytes (makeRuntimeBytes)
import Phil.IO.Console
  ( ConsoleCheckError (..)
  , ConsoleProviderOccurrence
  , ConsoleEnvironment (..)
  , ConsoleWriteOutcome (..)
  , defaultConsoleAuthorityCapability
  , standardConsoleEnvironment
  )
import Phil.IO.FileSystem
  ( FileReadOutcome (..)
  , FileReplaceOutcome (..)
  , FileSystemCheckError (..)
  , FileSystemFailure (..)
  , FileSystemOperation (..)
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
import qualified UTF8ImplementationKernel as Kernel

main :: IO ()
main = do
  let results =
        [ ("production read_utf8 decodes accepted predecessor", readDecoded)
        , ("production read_utf8 preserves invalid-decode classification", readDecodeFailure)
        , ("production read_utf8 preserves provider failure", readProviderFailure)
        , ("production read_utf8 preserves FileSystem negative-limit error", readNativeError)
        , ("production write_utf8 accepts checked replace", writeAccepted)
        , ("production write_line accepts checked Console write", lineAccepted)
        , ("production write_line preserves Console authority error", lineNativeError)
        , ("checked-in kernel classifies successful decode",
            isReadDecoded (Kernel.decideReadUTF8ByFacts True True True))
        , ("checked-in kernel classifies invalid decode",
            isReadDecodeFailed (Kernel.decideReadUTF8ByFacts True True False))
        , ("checked-in kernel preserves provider failure",
            isReadProviderFailed (Kernel.decideReadUTF8ByFacts True False False))
        , ("checked-in kernel rejects rejected read predecessor",
            isReadPredecessorRejected (Kernel.decideReadUTF8ByFacts False True True))
        , ("checked-in kernel accepts write_utf8 predecessor",
            isCompositionAccepted (Kernel.decideWriteUTF8ByFacts True))
        , ("checked-in kernel accepts write_line predecessor",
            isCompositionAccepted (Kernel.decideWriteLineByFacts True))
        ]
  mapM_ report results
  if all snd results then pure () else exitFailure

readDecoded :: Bool
readDecoded =
  case workspacePath of
    Left _ -> False
    Right (occurrence, path) ->
      case readAuthority occurrence of
        Left _ -> False
        Right authority ->
          let bytes = utf8Encode "hello λ"
              state = insertFileSystemBinding path bytes emptyFileSystemState
          in case checkReadUTF8
              occurrence path 64
              (PossessedCapability fsReadCapability)
              authority state
              (FileReadSucceeded bytes) of
            Right checked ->
              checkedReadUTF8Outcome checked == ReadUTF8Decoded "hello λ"
            Left _ -> False

readDecodeFailure :: Bool
readDecodeFailure =
  case workspacePath of
    Left _ -> False
    Right (occurrence, path) ->
      case readAuthority occurrence of
        Left _ -> False
        Right authority ->
          let bytes = makeRuntimeBytes [0xc3, 0x28]
              state = insertFileSystemBinding path bytes emptyFileSystemState
          in case checkReadUTF8
              occurrence path 8
              (PossessedCapability fsReadCapability)
              authority state
              (FileReadSucceeded bytes) of
            Right checked ->
              checkedReadUTF8Outcome checked == ReadUTF8DecodeFailed InvalidUTF8
            Left _ -> False

readProviderFailure :: Bool
readProviderFailure =
  case workspacePath of
    Left _ -> False
    Right (occurrence, path) ->
      case readAuthority occurrence of
        Left _ -> False
        Right authority ->
          case checkReadUTF8
              occurrence path 8
              (PossessedCapability fsReadCapability)
              authority emptyFileSystemState
              (FileReadFailed FileSystemNotFound) of
            Right checked ->
              checkedReadUTF8Outcome checked ==
                ReadUTF8ProviderFailed FileSystemNotFound
            Left _ -> False

readNativeError :: Bool
readNativeError =
  case workspacePath of
    Left _ -> False
    Right (occurrence, path) ->
      case readAuthority occurrence of
        Left _ -> False
        Right authority ->
          case checkReadUTF8
              occurrence path (-1)
              (PossessedCapability fsReadCapability)
              authority emptyFileSystemState
              (FileReadFailed FileSystemNotFound) of
            Left (UTF8FileSystemError (FileSystemNegativeReadLimit (-1))) -> True
            _ -> False

writeAccepted :: Bool
writeAccepted =
  case workspacePath of
    Left _ -> False
    Right (occurrence, path) ->
      case replaceAuthority occurrence of
        Left _ -> False
        Right authority ->
          case checkWriteUTF8
              occurrence path
              (PossessedCapability fsReplaceCapability)
              authority emptyFileSystemState
              "write λ"
              FileReplaceSucceeded of
            Right checked ->
              checkedWriteUTF8Bytes checked == utf8Encode "write λ"
            Left _ -> False

lineAccepted :: Bool
lineAccepted =
  let stdout = consoleEnvironmentStdout standardConsoleEnvironment
  in case consoleAuthority stdout of
      Left _ -> False
      Right authority ->
        case checkWriteLine
            stdout
            (PossessedCapability stdoutCapability)
            authority
            "hello"
            ConsoleWriteSucceeded of
          Right checked ->
            checkedWriteLineRequestedText checked == "hello\n"
          Left _ -> False

lineNativeError :: Bool
lineNativeError =
  let stdout = consoleEnvironmentStdout standardConsoleEnvironment
  in case checkWriteLine
      stdout
      (PossessedCapability stdoutCapability)
      emptyAuthorityState
      "hello"
      ConsoleWriteSucceeded of
    Left (UTF8ConsoleError
      (ConsoleAuthorityError (UnknownCapabilityOccurrence key))) ->
        key == stdoutCapability
    _ -> False

workspacePath :: Either String (FileSystemOccurrence, ProviderRelativePath)
workspacePath = do
  occurrence <- mapLeft show (fileSystemOccurrence "filesystem.codec.production")
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

consoleAuthority
  :: ConsoleProviderOccurrence
  -> Either String AuthorityState
consoleAuthority occurrence = do
  capability <- mapLeft show $
    defaultConsoleAuthorityCapability stdoutCapability occurrence
  mapLeft show $ insertAuthorityCapability capability emptyAuthorityState

fsReadCapability :: CapabilityOccurrenceKey
fsReadCapability = CapabilityOccurrenceKey "authority.codec.production.read"

fsReplaceCapability :: CapabilityOccurrenceKey
fsReplaceCapability = CapabilityOccurrenceKey "authority.codec.production.replace"

stdoutCapability :: CapabilityOccurrenceKey
stdoutCapability = CapabilityOccurrenceKey "authority.codec.production.stdout"

isReadDecoded :: Kernel.UTF8ReadDecision -> Bool
isReadDecoded value = case value of
  Kernel.UTF8ReadDecoded -> True
  _ -> False

isReadDecodeFailed :: Kernel.UTF8ReadDecision -> Bool
isReadDecodeFailed value = case value of
  Kernel.UTF8ReadDecodeFailed -> True
  _ -> False

isReadProviderFailed :: Kernel.UTF8ReadDecision -> Bool
isReadProviderFailed value = case value of
  Kernel.UTF8ReadProviderFailed -> True
  _ -> False

isReadPredecessorRejected :: Kernel.UTF8ReadDecision -> Bool
isReadPredecessorRejected value = case value of
  Kernel.UTF8ReadPredecessorRejected -> True
  _ -> False

isCompositionAccepted :: Kernel.UTF8CompositionDecision -> Bool
isCompositionAccepted value = case value of
  Kernel.UTF8CompositionAccepted -> True
  _ -> False

report :: (String, Bool) -> IO ()
report (label, ok) =
  putStrLn ((if ok then "PASS: " else "FAIL: ") <> "IO-CODEC production " <> label)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
