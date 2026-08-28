From Corelib Require Extraction.

From Phil.Core Require Import ArchitectureIdentityImplementation.

Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "ArchitectureIdentityKernel"
  declarationIdentityFactsb
  decideDeclarationIdentityEquality
  interfaceValidityScopeFactsb
  decideInterfaceValidityScopeEquality
  architectureInstanceIdentityFactsb
  decideArchitectureInstanceIdentityEquality.
