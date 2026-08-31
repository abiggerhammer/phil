From Corelib Require Extraction.
From Phil.Core Require Import ProtocolProgressionGuardImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "ProtocolProgressionGuardKernel"
  decideProtocolContinuationByFacts
  decideProtocolCloseByFact
  planProtocolSuccessorContract
  decideProtocolGuardListByFact
  decideProtocolGuardRequirementByFacts.
