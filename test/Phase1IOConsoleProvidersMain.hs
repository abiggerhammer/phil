{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import Phil.Core.Authority
  ( AuthorityCheckError (..)
  , AuthorityExerciseSource (..)
  , AuthorityState
  , CapabilityOccurrenceKey (..)
  , copyAuthorityCapability
  , emptyAuthorityState
  , insertAuthorityCapability
  )
import Phil.Core.Callable (SemanticEffect (..))
import Phil.Core.Syntax (Mode (..))
import Phil.IO.Console
import System.Exit (exitFailure)

main :: IO ()
main = do
  let checks =
        [ ("standard stdin/stdout/stderr are distinct provider occurrences", standardOccurrencesDistinct)
        , ("bounded stdin read accepts a line and explicit EOF", boundedReadAndEOF)
        , ("successful line larger than the caller bound rejects", overLimitSuccessRejects)
        , ("default stdin authority is restricted linear ownership", inputAuthorityIsRestricted)
        , ("stdout authority does not grant stderr authority", stdoutAuthorityDoesNotGrantStderr)
        , ("effect permission alone is not console authority", effectPermissionIsNotAuthority)
        , ("ambient stdio registry entry is not console authority", ambientRegistryIsNotAuthority)
        , ("failed write preserves exact externally observable prefix progress", partialWriteProgressIsExplicit)
        , ("failed write cannot claim progress beyond requested text", invalidWriteProgressRejects)
        , ("write authority does not silently imply flush authority", writeAndFlushAuthorityAreDistinct)
        , ("console effects are indexed by exact occurrence and operation", effectsAreSubjectIndexed)
        ]
  mapM_ report checks
  if all (either (const False) (const True) . snd) checks
    then pure ()
    else exitFailure
  where
    report (label, Right ()) = putStrLn ("PASS: IO-CONSOLE-001 " <> label)
    report (label, Left detail) = putStrLn ("FAIL: IO-CONSOLE-001 " <> label <> " -- " <> detail)

standardOccurrencesDistinct :: Either String ()
standardOccurrencesDistinct = do
  let env = standardConsoleEnvironment
      stdin = consoleEnvironmentStdin env
      stdout = consoleEnvironmentStdout env
      stderr = consoleEnvironmentStderr env
  assert (stdin /= stdout && stdin /= stderr && stdout /= stderr)
    "standard console occurrences collapsed"
  assert (consoleProviderKind stdin == ConsoleInputProvider)
    "stdin did not retain ConsoleInput provider identity"
  assert (consoleProviderKind stdout == ConsoleOutputProvider
       && consoleProviderKind stderr == ConsoleOutputProvider)
    "stdout/stderr did not retain ConsoleOutput provider identity"

boundedReadAndEOF :: Either String ()
boundedReadAndEOF = do
  let stdin = consoleEnvironmentStdin standardConsoleEnvironment
  state <- stateWithDefault stdin stdinCapability
  line <- mapLeft show $ checkConsoleReadLine
    stdin 5 (PossessedCapability stdinCapability) state (ConsoleLine "hello")
  assert (checkedConsoleReadOutcome line == ConsoleLine "hello")
    "bounded line result changed"
  eof <- mapLeft show $ checkConsoleReadLine
    stdin 0 (PossessedCapability stdinCapability) state ConsoleEndOfInput
  assert (checkedConsoleReadOutcome eof == ConsoleEndOfInput)
    "EOF was not preserved as an explicit outcome"
  tooLarge <- mapLeft show $ checkConsoleReadLine
    stdin 1 (PossessedCapability stdinCapability) state (ConsoleReadFailed ConsoleTooLarge)
  assert (checkedConsoleReadOutcome tooLarge == ConsoleReadFailed ConsoleTooLarge)
    "TooLarge was not preserved as an explicit negative outcome"

overLimitSuccessRejects :: Either String ()
overLimitSuccessRejects = do
  let stdin = consoleEnvironmentStdin standardConsoleEnvironment
  state <- stateWithDefault stdin stdinCapability
  case checkConsoleReadLine
      stdin 4 (PossessedCapability stdinCapability) state (ConsoleLine "hello") of
    Left (ConsoleReadLineExceedsLimit 4 5) -> Right ()
    other -> Left ("oversized successful line did not reject: " <> show other)

inputAuthorityIsRestricted :: Either String ()
inputAuthorityIsRestricted = do
  let stdin = consoleEnvironmentStdin standardConsoleEnvironment
  capability <- mapLeft show (defaultConsoleAuthorityCapability stdinCapability stdin)
  state <- mapLeft show (insertAuthorityCapability capability emptyAuthorityState)
  case copyAuthorityCapability stdinCapability duplicateStdinCapability state of
    Left (RestrictedCapabilityCopy key Linear) ->
      assert (key == stdinCapability) "copy rejection named the wrong stdin capability"
    other -> Left ("default stdin authority was copyable: " <> show other)

stdoutAuthorityDoesNotGrantStderr :: Either String ()
stdoutAuthorityDoesNotGrantStderr = do
  let env = standardConsoleEnvironment
      stdout = consoleEnvironmentStdout env
      stderr = consoleEnvironmentStderr env
  state <- stateWithDefault stdout stdoutCapability
  _ <- mapLeft show $ checkConsoleWrite
    stdout
    (PossessedCapability stdoutCapability)
    state
    "visible"
    ConsoleWriteSucceeded
  case checkConsoleWrite
      stderr
      (PossessedCapability stdoutCapability)
      state
      "wrong sink"
      ConsoleWriteSucceeded of
    Left (ConsoleAuthorityError (AuthoritySubjectMismatch _ _)) -> Right ()
    other -> Left ("stdout authority satisfied stderr write: " <> show other)

effectPermissionIsNotAuthority :: Either String ()
effectPermissionIsNotAuthority = do
  let stdout = consoleEnvironmentStdout standardConsoleEnvironment
      SemanticEffect effect = consoleOperationEffect stdout ConsoleWriteOp
  state <- stateWithDefault stdout stdoutCapability
  case checkConsoleWrite
      stdout
      (EffectPermissionOnly effect)
      state
      "no authority"
      ConsoleWriteSucceeded of
    Left (ConsoleAuthorityError (AuthoritySourceIsNotPossession _)) -> Right ()
    other -> Left ("effect permission was accepted as authority: " <> show other)

ambientRegistryIsNotAuthority :: Either String ()
ambientRegistryIsNotAuthority = do
  let stdout = consoleEnvironmentStdout standardConsoleEnvironment
  state <- stateWithDefault stdout stdoutCapability
  case checkConsoleWrite
      stdout
      (AmbientAuthorityRegistryEntry "stdout")
      state
      "no ambient stdio"
      ConsoleWriteSucceeded of
    Left (ConsoleAuthorityError (AuthoritySourceIsNotPossession _)) -> Right ()
    other -> Left ("ambient stdout registry supplied authority: " <> show other)

partialWriteProgressIsExplicit :: Either String ()
partialWriteProgressIsExplicit = do
  let stdout = consoleEnvironmentStdout standardConsoleEnvironment
  state <- stateWithDefault stdout stdoutCapability
  checked <- mapLeft show $ checkConsoleWrite
    stdout
    (PossessedCapability stdoutCapability)
    state
    "hello"
    (ConsoleWriteFailed ConsoleUnavailable 2)
  assert (checkedConsoleWriteObservablePrefixLength checked == 2)
    "partial failure lost exact prefix length"
  assert (checkedConsoleWriteObservablePrefix checked == "he")
    "partial failure lost exact observable prefix"

invalidWriteProgressRejects :: Either String ()
invalidWriteProgressRejects = do
  let stdout = consoleEnvironmentStdout standardConsoleEnvironment
  state <- stateWithDefault stdout stdoutCapability
  case checkConsoleWrite
      stdout
      (PossessedCapability stdoutCapability)
      state
      "hello"
      (ConsoleWriteFailed ConsoleUnavailable 6) of
    Left (ConsoleWriteProgressOutOfRange 5 6) -> Right ()
    other -> Left ("impossible write progress was accepted: " <> show other)

writeAndFlushAuthorityAreDistinct :: Either String ()
writeAndFlushAuthorityAreDistinct = do
  let stdout = consoleEnvironmentStdout standardConsoleEnvironment
  capability <- mapLeft show $ makeConsoleAuthorityCapability
    writeOnlyCapability
    Affine
    stdout
    (Set.singleton ConsoleWriteOp)
  state <- mapLeft show (insertAuthorityCapability capability emptyAuthorityState)
  _ <- mapLeft show $ checkConsoleWrite
    stdout
    (PossessedCapability writeOnlyCapability)
    state
    "write only"
    ConsoleWriteSucceeded
  case checkConsoleFlush
      stdout
      (PossessedCapability writeOnlyCapability)
      state
      ConsoleFlushSucceeded of
    Left (ConsoleAuthorityError (AuthorityOperationNotPermitted _)) -> Right ()
    other -> Left ("write-only authority silently granted flush: " <> show other)

effectsAreSubjectIndexed :: Either String ()
effectsAreSubjectIndexed = do
  let env = standardConsoleEnvironment
      stdout = consoleEnvironmentStdout env
      stderr = consoleEnvironmentStderr env
      stdoutWrite = consoleOperationEffect stdout ConsoleWriteOp
      stderrWrite = consoleOperationEffect stderr ConsoleWriteOp
      stdoutFlush = consoleOperationEffect stdout ConsoleFlushOp
  assert (stdoutWrite /= stderrWrite)
    "stdout and stderr write effects collapsed"
  assert (stdoutWrite /= stdoutFlush)
    "stdout write and flush effects collapsed"

stateWithDefault
  :: ConsoleProviderOccurrence
  -> CapabilityOccurrenceKey
  -> Either String AuthorityState
stateWithDefault occurrence capabilityKey = do
  capability <- mapLeft show (defaultConsoleAuthorityCapability capabilityKey occurrence)
  mapLeft show (insertAuthorityCapability capability emptyAuthorityState)

stdinCapability :: CapabilityOccurrenceKey
stdinCapability = CapabilityOccurrenceKey "authority.console.stdin"

duplicateStdinCapability :: CapabilityOccurrenceKey
duplicateStdinCapability = CapabilityOccurrenceKey "authority.console.stdin.copy"

stdoutCapability :: CapabilityOccurrenceKey
stdoutCapability = CapabilityOccurrenceKey "authority.console.stdout"

writeOnlyCapability :: CapabilityOccurrenceKey
writeOnlyCapability = CapabilityOccurrenceKey "authority.console.stdout.write-only"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
