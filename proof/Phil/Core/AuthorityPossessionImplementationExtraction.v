From Corelib Require Extraction.
From Phil.Core Require Import AuthorityPossessionImplementation.

Extraction Language Haskell.

(* Keep the executable representation aligned with native Haskell facts, as in
   GenericStructuralImplementationExtraction.v. *)
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "AuthorityPossessionKernel"
  AuthorityExerciseDecision
  decideAuthorityExerciseFacts
  AuthorityCopyDecision
  decideAuthorityCopy
  AuthorityDropDecision
  decideAuthorityDrop.
