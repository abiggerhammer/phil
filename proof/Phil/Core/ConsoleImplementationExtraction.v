From Stdlib Require Import Extraction.

From Phil.Core Require Import ConsoleImplementation.

Extraction Language Haskell.

Extract Inductive bool =>
  "Prelude.Bool" ["Prelude.True" "Prelude.False"].

Extraction "ConsoleImplementationKernel"
  decideConsoleOccurrenceByFacts
  decideConsoleOperationByFacts
  decideConsoleReadByFacts
  decideConsoleWriteByFacts
  consoleWriteUsesFullRequested
  decideConsoleFlushByFacts.
