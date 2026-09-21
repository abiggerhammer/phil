module Main (main) where

import ConsoleImplementationKernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  let controls =
        [ ("nonempty console occurrence accepts",
            isOccurrenceAccepted (decideConsoleOccurrenceByFacts False))
        , ("empty console occurrence rejects",
            isOccurrenceEmpty (decideConsoleOccurrenceByFacts True))
        , ("allowed operation accepts",
            isOperationAccepted (decideConsoleOperationByFacts True))
        , ("kind mismatch rejects operation",
            isOperationMismatch (decideConsoleOperationByFacts False))
        , ("bounded line accepts",
            isReadAccepted
              (decideConsoleReadByFacts True True ObservedConsoleLine True))
        , ("overbound line rejects",
            isReadLimit
              (decideConsoleReadByFacts True True ObservedConsoleLine False))
        , ("read authority rejects before outcome",
            isReadAuthority
              (decideConsoleReadByFacts True False ObservedConsoleLine True))
        , ("read kind mismatch rejects first",
            isReadKind
              (decideConsoleReadByFacts False True ObservedConsoleLine True))
        , ("EOF accepts after preconditions",
            isReadAccepted
              (decideConsoleReadByFacts
                True True ObservedConsoleEndOfInput False))
        , ("provider read failure accepts after preconditions",
            isReadAccepted
              (decideConsoleReadByFacts
                True True ObservedConsoleReadFailure False))
        , ("successful write accepts without progress-range fact",
            isWriteAccepted
              (decideConsoleWriteByFacts True True True False))
        , ("in-range partial write accepts",
            isWriteAccepted
              (decideConsoleWriteByFacts True True False True))
        , ("out-of-range partial write rejects",
            isWriteProgress
              (decideConsoleWriteByFacts True True False False))
        , ("write authority rejects before progress",
            isWriteAuthority
              (decideConsoleWriteByFacts True False False True))
        , ("write kind mismatch rejects first",
            isWriteKind
              (decideConsoleWriteByFacts False True True True))
        , ("successful write selects full requested length",
            consoleWriteUsesFullRequested True)
        , ("failed write selects reported prefix",
            not (consoleWriteUsesFullRequested False))
        , ("authorized output flush accepts",
            isFlushAccepted (decideConsoleFlushByFacts True True))
        , ("flush authority rejection is explicit",
            isFlushAuthority (decideConsoleFlushByFacts True False))
        , ("flush kind mismatch rejects first",
            isFlushKind (decideConsoleFlushByFacts False True))
        ]
  mapM_ report controls
  if all snd controls then pure () else exitFailure

report :: (String, Bool) -> IO ()
report (label, ok) =
  putStrLn ((if ok then "PASS: " else "FAIL: ") <> "IO-CONSOLE kernel " <> label)

isOccurrenceAccepted :: ConsoleOccurrenceDecision -> Bool
isOccurrenceAccepted value = case value of
  ConsoleOccurrenceAccepted -> True
  _ -> False

isOccurrenceEmpty :: ConsoleOccurrenceDecision -> Bool
isOccurrenceEmpty value = case value of
  ConsoleOccurrenceEmpty -> True
  _ -> False

isOperationAccepted :: ConsoleOperationDecision -> Bool
isOperationAccepted value = case value of
  ConsoleOperationAccepted -> True
  _ -> False

isOperationMismatch :: ConsoleOperationDecision -> Bool
isOperationMismatch value = case value of
  ConsoleOperationKindMismatch -> True
  _ -> False

isReadAccepted :: ConsoleReadDecision -> Bool
isReadAccepted value = case value of
  ConsoleReadAccepted -> True
  _ -> False

isReadKind :: ConsoleReadDecision -> Bool
isReadKind value = case value of
  ConsoleReadOperationKindMismatch -> True
  _ -> False

isReadAuthority :: ConsoleReadDecision -> Bool
isReadAuthority value = case value of
  ConsoleReadAuthorityRejected -> True
  _ -> False

isReadLimit :: ConsoleReadDecision -> Bool
isReadLimit value = case value of
  ConsoleReadLineExceedsLimit -> True
  _ -> False

isWriteAccepted :: ConsoleWriteDecision -> Bool
isWriteAccepted value = case value of
  ConsoleWriteAccepted -> True
  _ -> False

isWriteKind :: ConsoleWriteDecision -> Bool
isWriteKind value = case value of
  ConsoleWriteOperationKindMismatch -> True
  _ -> False

isWriteAuthority :: ConsoleWriteDecision -> Bool
isWriteAuthority value = case value of
  ConsoleWriteAuthorityRejected -> True
  _ -> False

isWriteProgress :: ConsoleWriteDecision -> Bool
isWriteProgress value = case value of
  ConsoleWriteProgressOutOfRange -> True
  _ -> False

isFlushAccepted :: ConsoleFlushDecision -> Bool
isFlushAccepted value = case value of
  ConsoleFlushAccepted -> True
  _ -> False

isFlushKind :: ConsoleFlushDecision -> Bool
isFlushKind value = case value of
  ConsoleFlushOperationKindMismatch -> True
  _ -> False

isFlushAuthority :: ConsoleFlushDecision -> Bool
isFlushAuthority value = case value of
  ConsoleFlushAuthorityRejected -> True
  _ -> False
