From Corelib Require Extraction.
From Phil.Core Require Import DataSubjectImplementation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "DataSubjectKernel"
  decideDataSubjectPrerequisites
  decideDataSubjectTransportMode
  decideDataSubjectTransport.
