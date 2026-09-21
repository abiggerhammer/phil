module ConsoleImplementationKernel where

import qualified Prelude

data ConsoleOccurrenceDecision =
   ConsoleOccurrenceAccepted
 | ConsoleOccurrenceEmpty

decideConsoleOccurrenceByFacts :: Prelude.Bool -> ConsoleOccurrenceDecision
decideConsoleOccurrenceByFacts occurrenceEmpty =
  case occurrenceEmpty of {
   Prelude.True -> ConsoleOccurrenceEmpty;
   Prelude.False -> ConsoleOccurrenceAccepted}

data ConsoleOperationDecision =
   ConsoleOperationAccepted
 | ConsoleOperationKindMismatch

decideConsoleOperationByFacts :: Prelude.Bool -> ConsoleOperationDecision
decideConsoleOperationByFacts kindAllowsOperation =
  case kindAllowsOperation of {
   Prelude.True -> ConsoleOperationAccepted;
   Prelude.False -> ConsoleOperationKindMismatch}

data ConsoleObservedReadKind =
   ObservedConsoleLine
 | ObservedConsoleEndOfInput
 | ObservedConsoleReadFailure

data ConsoleReadDecision =
   ConsoleReadAccepted
 | ConsoleReadOperationKindMismatch
 | ConsoleReadAuthorityRejected
 | ConsoleReadLineExceedsLimit

decideConsoleReadByFacts :: Prelude.Bool -> Prelude.Bool ->
                            ConsoleObservedReadKind -> Prelude.Bool ->
                            ConsoleReadDecision
decideConsoleReadByFacts kindAllowsRead authorityAccepted observedKind lineWithinLimit =
  case kindAllowsRead of {
   Prelude.True ->
    case authorityAccepted of {
     Prelude.True ->
      case observedKind of {
       ObservedConsoleLine ->
        case lineWithinLimit of {
         Prelude.True -> ConsoleReadAccepted;
         Prelude.False -> ConsoleReadLineExceedsLimit};
       _ -> ConsoleReadAccepted};
     Prelude.False -> ConsoleReadAuthorityRejected};
   Prelude.False -> ConsoleReadOperationKindMismatch}

data ConsoleWriteDecision =
   ConsoleWriteAccepted
 | ConsoleWriteOperationKindMismatch
 | ConsoleWriteAuthorityRejected
 | ConsoleWriteProgressOutOfRange

decideConsoleWriteByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
                             Prelude.Bool -> ConsoleWriteDecision
decideConsoleWriteByFacts kindAllowsWrite authorityAccepted observedSuccess progressWithinRequest =
  case kindAllowsWrite of {
   Prelude.True ->
    case authorityAccepted of {
     Prelude.True ->
      case observedSuccess of {
       Prelude.True -> ConsoleWriteAccepted;
       Prelude.False ->
        case progressWithinRequest of {
         Prelude.True -> ConsoleWriteAccepted;
         Prelude.False -> ConsoleWriteProgressOutOfRange}};
     Prelude.False -> ConsoleWriteAuthorityRejected};
   Prelude.False -> ConsoleWriteOperationKindMismatch}

consoleWriteUsesFullRequested :: Prelude.Bool -> Prelude.Bool
consoleWriteUsesFullRequested observedSuccess =
  observedSuccess

data ConsoleFlushDecision =
   ConsoleFlushAccepted
 | ConsoleFlushOperationKindMismatch
 | ConsoleFlushAuthorityRejected

decideConsoleFlushByFacts :: Prelude.Bool -> Prelude.Bool ->
                             ConsoleFlushDecision
decideConsoleFlushByFacts kindAllowsFlush authorityAccepted =
  case kindAllowsFlush of {
   Prelude.True ->
    case authorityAccepted of {
     Prelude.True -> ConsoleFlushAccepted;
     Prelude.False -> ConsoleFlushAuthorityRejected};
   Prelude.False -> ConsoleFlushOperationKindMismatch}
