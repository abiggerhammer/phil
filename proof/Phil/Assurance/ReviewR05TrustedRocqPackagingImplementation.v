From Stdlib Require Import Bool.Bool.

Inductive ReviewR05Decision : Type :=
| ReviewR05Accepted
| ReviewR05Rejected.

Definition reviewR05Factsb
  (trustedPackagingAcknowledged obligationMarkerPresent
   expectedTheoremDeclarationsPresent sourceArtifactDigestBound
   compiledArtifactDigestBound certificateNamesTrustedPackaging
   evidenceNamesExternalCheckPrecondition : bool) : bool :=
  trustedPackagingAcknowledged &&
  obligationMarkerPresent &&
  expectedTheoremDeclarationsPresent &&
  sourceArtifactDigestBound &&
  compiledArtifactDigestBound &&
  certificateNamesTrustedPackaging &&
  evidenceNamesExternalCheckPrecondition.

Definition decideReviewR05
  (trustedPackagingAcknowledged obligationMarkerPresent
   expectedTheoremDeclarationsPresent sourceArtifactDigestBound
   compiledArtifactDigestBound certificateNamesTrustedPackaging
   evidenceNamesExternalCheckPrecondition : bool)
  : ReviewR05Decision :=
  if reviewR05Factsb
      trustedPackagingAcknowledged
      obligationMarkerPresent
      expectedTheoremDeclarationsPresent
      sourceArtifactDigestBound
      compiledArtifactDigestBound
      certificateNamesTrustedPackaging
      evidenceNamesExternalCheckPrecondition
  then ReviewR05Accepted
  else ReviewR05Rejected.

Theorem exact_trusted_packaging_accepts :
  decideReviewR05 true true true true true true true =
    ReviewR05Accepted.
Proof. reflexivity. Qed.

Theorem legacy_unacknowledged_invocation_rejects :
  decideReviewR05 false true true true true true true =
    ReviewR05Rejected.
Proof. reflexivity. Qed.

Theorem malformed_source_profile_rejects :
  decideReviewR05 true false true true true true true =
      ReviewR05Rejected /\
  decideReviewR05 true true false true true true true =
      ReviewR05Rejected.
Proof. split; reflexivity. Qed.

Theorem missing_content_binding_rejects :
  decideReviewR05 true true true false true true true =
      ReviewR05Rejected /\
  decideReviewR05 true true true true false true true =
      ReviewR05Rejected.
Proof. split; reflexivity. Qed.

Theorem hidden_trust_boundary_rejects :
  decideReviewR05 true true true true true false true =
      ReviewR05Rejected /\
  decideReviewR05 true true true true true true false =
      ReviewR05Rejected.
Proof. split; reflexivity. Qed.
