{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified ConsoleImplementationKernel as Kernel
import qualified Data.Set as Set
import Phil.Core.Authority
  ( AuthorityCheckError (..)
  , AuthorityExerciseSource (..)
  , CapabilityOccurrenceKey (..)
  , AuthorityState
  , emptyAuthorityState
  , insertAuthorityCapability
  )
import Phil.Core.Syntax (Mode (..))
import Phil.IO.Console
import System.Exit (exitFailure)

main :: IO ()
main = do
  let results =
        [ ("production nonempty input occurrence accepts", nonemptyOccurrenceAccepts)
        , ("production empty occurrence keeps native diagnostic", emptyOccurrenceRejects)
        , ("production illegal operation keeps native diagnostic", illegalOperationRejects)
        , ("production bounded read accepts", boundedReadAccepts)
        , ("production overbound read keeps native diagnostic", overboundReadRejects)
        , ("production read authority rejection keeps native diagnostic", readAuthorityRejects)
        , ("production successful write exposes full request", successfulWriteExact)
        , ("production failed write exposes exact prefix", partialWriteExact)
        , ("production impossible write progress keeps native diagnostic", impossibleWriteRejects)
        , ("production authorized flush accepts", flushAccepts)
        , ("production write-only authority does not grant flush", flushAuthorityRejects)
        , ("checked-in kernel accepts exact read facts",
            isReadAccepted
              (Kernel.decideConsoleReadByFacts
                True True Kernel.ObservedConsoleLine True))
        , ("checked-in kernel rejects overbound read facts",
            isReadLimit
              (Kernel.decideConsoleReadByFacts
                True True Kernel.ObservedConsoleLine False))
        , ("checked-in kernel accepts in-range partial write",
            isWriteAccepted
              (Kernel.decideConsoleWriteByFacts True True False True))
        , ("checked-in kernel rejects out-of-range partial write",
            isWriteProgress
              (Kernel.decideConsoleWriteByFacts True True False False))
        ]
  mapM_ report results
  if all snd results then pure () else exitFailure

nonemptyOccurrenceAccepts :: Bool
nonemptyOccurrenceAccepts =
  case consoleInputOccurrence "custom.stdin" of
    Right occurrence ->
      consoleProviderKind occurrence == ConsoleInputProvider
        && consoleProviderOccurrenceKey occurrence == ConsoleOccurrenceKey "custom.stdin"
    Left _ -> False

emptyOccurrenceRejects :: Bool
emptyOccurrenceRejects =
  case consoleInputOccurrence "" of
    Left EmptyConsoleOccurrenceKey -> True
    _ -> False

illegalOperationRejects :: Bool
illegalOperationRejects =
  let stdin = consoleEnvironmentStdin standardConsoleEnvironment
  in case consoleOperationContract stdin ConsoleWriteOp of
      Left (ConsoleOperationKindMismatch key ConsoleInputProvider ConsoleWriteOp) ->
        key == consoleProviderOccurrenceKey stdin
      _ -> False

boundedReadAccepts :: Bool
boundedReadAccepts =
  let stdin = consoleEnvironmentStdin standardConsoleEnvironment
  in case stateWithDefault stdin stdinCapability of
      Left _ -> False
      Right state ->
        case checkConsoleReadLine
            stdin 5 (PossessedCapability stdinCapability) state (ConsoleLine "hello") of
          Right checked -> checkedConsoleReadOutcome checked == ConsoleLine "hello"
          Left _ -> False

overboundReadRejects :: Bool
overboundReadRejects =
  let stdin = consoleEnvironmentStdin standardConsoleEnvironment
  in case stateWithDefault stdin stdinCapability of
      Left _ -> False
      Right state ->
        case checkConsoleReadLine
            stdin 4 (PossessedCapability stdinCapability) state (ConsoleLine "hello") of
          Left (ConsoleReadLineExceedsLimit 4 5) -> True
          _ -> False

readAuthorityRejects :: Bool
readAuthorityRejects =
  let stdin = consoleEnvironmentStdin standardConsoleEnvironment
  in case checkConsoleReadLine
      stdin 5 (PossessedCapability stdinCapability) emptyAuthorityState (ConsoleLine "hello") of
    Left (ConsoleAuthorityError (UnknownCapability key)) -> key == stdinCapability
    _ -> False

successfulWriteExact :: Bool
successfulWriteExact =
  let stdout = consoleEnvironmentStdout standardConsoleEnvironment
  in case stateWithDefault stdout stdoutCapability of
      Left _ -> False
      Right state ->
        case checkConsoleWrite
            stdout
            (PossessedCapability stdoutCapability)
            state
            "hello"
            ConsoleWriteSucceeded of
          Right checked ->
            checkedConsoleWriteObservablePrefixLength checked == 5
              && checkedConsoleWriteObservablePrefix checked == "hello"
          Left _ -> False

partialWriteExact :: Bool
partialWriteExact =
  let stdout = consoleEnvironmentStdout standardConsoleEnvironment
  in case stateWithDefault stdout stdoutCapability of
      Left _ -> False
      Right state ->
        case checkConsoleWrite
            stdout
            (PossessedCapability stdoutCapability)
            state
            "hello"
            (ConsoleWriteFailed ConsoleUnavailable 2) of
          Right checked ->
            checkedConsoleWriteObservablePrefixLength checked == 2
              && checkedConsoleWriteObservablePrefix checked == "he"
          Left _ -> False

impossibleWriteRejects :: Bool
impossibleWriteRejects =
  let stdout = consoleEnvironmentStdout standardConsoleEnvironment
  in case stateWithDefault stdout stdoutCapability of
      Left _ -> False
      Right state ->
        case checkConsoleWrite
            stdout
            (PossessedCapability stdoutCapability)
            state
            "hello"
            (ConsoleWriteFailed ConsoleUnavailable 6) of
          Left (ConsoleWriteProgressOutOfRange 5 6) -> True
          _ -> False

flushAccepts :: Bool
flushAccepts =
  let stdout = consoleEnvironmentStdout standardConsoleEnvironment
  in case stateWithDefault stdout stdoutCapability of
      Left _ -> False
      Right state ->
        case checkConsoleFlush
            stdout
            (PossessedCapability stdoutCapability)
            state
            ConsoleFlushSucceeded of
          Right checked -> checkedConsoleFlushOutcome checked == ConsoleFlushSucceeded
          Left _ -> False

flushAuthorityRejects :: Bool
flushAuthorityRejects =
  let stdout = consoleEnvironmentStdout standardConsoleEnvironment
      capability = makeConsoleAuthorityCapability
        writeOnlyCapability
        Affine
        stdout
        (Set.singleton ConsoleWriteOp)
  in case capability of
      Left _ -> False
      Right cap ->
        case insertAuthorityCapability cap emptyAuthorityState of
          Left _ -> False
          Right state ->
            case checkConsoleFlush
                stdout
                (PossessedCapability writeOnlyCapability)
                state
                ConsoleFlushSucceeded of
              Left (ConsoleAuthorityError (AuthorityOperationNotPermitted _)) -> True
              _ -> False

stateWithDefault
  :: ConsoleProviderOccurrence
  -> CapabilityOccurrenceKey
  -> Either String AuthorityState
stateWithDefault occurrence capabilityKey = do
  capability <- mapLeft show (defaultConsoleAuthorityCapability capabilityKey occurrence)
  mapLeft show (insertAuthorityCapability capability emptyAuthorityState)

stdinCapability :: CapabilityOccurrenceKey
stdinCapability = CapabilityOccurrenceKey "authority.console.production.stdin"

stdoutCapability :: CapabilityOccurrenceKey
stdoutCapability = CapabilityOccurrenceKey "authority.console.production.stdout"

writeOnlyCapability :: CapabilityOccurrenceKey
writeOnlyCapability = CapabilityOccurrenceKey "authority.console.production.write-only"

isReadAccepted :: Kernel.ConsoleReadDecision -> Bool
isReadAccepted value = case value of
  Kernel.ConsoleReadAccepted -> True
  _ -> False

isReadLimit :: Kernel.ConsoleReadDecision -> Bool
isReadLimit value = case value of
  Kernel.ConsoleReadLineExceedsLimit -> True
  _ -> False

isWriteAccepted :: Kernel.ConsoleWriteDecision -> Bool
isWriteAccepted value = case value of
  Kernel.ConsoleWriteAccepted -> True
  _ -> False

isWriteProgress :: Kernel.ConsoleWriteDecision -> Bool
isWriteProgress value = case value of
  Kernel.ConsoleWriteProgressOutOfRange -> True
  _ -> False

report :: (String, Bool) -> IO ()
report (label, ok) =
  putStrLn ((if ok then "PASS: " else "FAIL: ") <> "IO-CONSOLE production " <> label)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
