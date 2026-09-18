From Stdlib Require Import Bool.Bool.

From Phil.Verification Require Import ManifestClosure.

Inductive ManifestClosureDecision : Type :=
| ManifestClosureAccepted
| ManifestClosureRejected.

Definition manifestClosureFactsb
  (intrinsicAccepted policyExact architectureExact obligationDomainExact
   revisionBodiesExact acceptedEvidenceRefsExact selectedEvidenceCurrent
   selectedEvidenceAccepted selectedEvidenceValidityExact
   assumptionDependenciesExplicit noUnusedAssumptions
   exportsExplicit exportsPermitted exportsValidityExact
   usesExplicit manifestVerifierAccepted : bool) : bool :=
  intrinsicAccepted &&
  policyExact &&
  architectureExact &&
  obligationDomainExact &&
  revisionBodiesExact &&
  acceptedEvidenceRefsExact &&
  selectedEvidenceCurrent &&
  selectedEvidenceAccepted &&
  selectedEvidenceValidityExact &&
  assumptionDependenciesExplicit &&
  noUnusedAssumptions &&
  exportsExplicit &&
  exportsPermitted &&
  exportsValidityExact &&
  usesExplicit &&
  manifestVerifierAccepted.

Definition decideManifestClosure
  (intrinsicAccepted policyExact architectureExact obligationDomainExact
   revisionBodiesExact acceptedEvidenceRefsExact selectedEvidenceCurrent
   selectedEvidenceAccepted selectedEvidenceValidityExact
   assumptionDependenciesExplicit noUnusedAssumptions
   exportsExplicit exportsPermitted exportsValidityExact
   usesExplicit manifestVerifierAccepted : bool) : ManifestClosureDecision :=
  if manifestClosureFactsb
      intrinsicAccepted policyExact architectureExact obligationDomainExact
      revisionBodiesExact acceptedEvidenceRefsExact selectedEvidenceCurrent
      selectedEvidenceAccepted selectedEvidenceValidityExact
      assumptionDependenciesExplicit noUnusedAssumptions
      exportsExplicit exportsPermitted exportsValidityExact
      usesExplicit manifestVerifierAccepted
  then ManifestClosureAccepted
  else ManifestClosureRejected.

Theorem exact_manifest_closure_accepts :
  decideManifestClosure
    true true true true true true true true
    true true true true true true true true =
  ManifestClosureAccepted.
Proof. reflexivity. Qed.

Theorem intrinsic_rejection_cannot_be_closed :
  decideManifestClosure
    false true true true true true true true
    true true true true true true true true =
  ManifestClosureRejected.
Proof. reflexivity. Qed.

Theorem policy_or_architecture_substitution_rejects :
  decideManifestClosure
    true false true true true true true true
    true true true true true true true true =
      ManifestClosureRejected /\
  decideManifestClosure
    true true false true true true true true
    true true true true true true true true =
      ManifestClosureRejected.
Proof. split; reflexivity. Qed.

Theorem obligation_or_revision_substitution_rejects :
  decideManifestClosure
    true true true false true true true true
    true true true true true true true true =
      ManifestClosureRejected /\
  decideManifestClosure
    true true true true false true true true
    true true true true true true true true =
      ManifestClosureRejected.
Proof. split; reflexivity. Qed.

Theorem stale_or_foreign_evidence_rejects :
  decideManifestClosure
    true true true true true false true true
    true true true true true true true true =
      ManifestClosureRejected /\
  decideManifestClosure
    true true true true true true false true
    true true true true true true true true =
      ManifestClosureRejected /\
  decideManifestClosure
    true true true true true true true false
    true true true true true true true true =
      ManifestClosureRejected.
Proof. repeat split; reflexivity. Qed.

Theorem evidence_validity_mismatch_rejects :
  decideManifestClosure
    true true true true true true true true
    false true true true true true true true =
  ManifestClosureRejected.
Proof. reflexivity. Qed.

Theorem hidden_or_unused_assumption_rejects :
  decideManifestClosure
    true true true true true true true true
    true false true true true true true true =
      ManifestClosureRejected /\
  decideManifestClosure
    true true true true true true true true
    true true false true true true true true =
      ManifestClosureRejected.
Proof. split; reflexivity. Qed.

Theorem invalid_export_rejects :
  decideManifestClosure
    true true true true true true true true
    true true true false true true true true =
      ManifestClosureRejected /\
  decideManifestClosure
    true true true true true true true true
    true true true true false true true true =
      ManifestClosureRejected /\
  decideManifestClosure
    true true true true true true true true
    true true true true true false true true =
      ManifestClosureRejected.
Proof. repeat split; reflexivity. Qed.

Theorem missing_use_or_manifest_verifier_rejection_rejects :
  decideManifestClosure
    true true true true true true true true
    true true true true true true false true =
      ManifestClosureRejected /\
  decideManifestClosure
    true true true true true true true true
    true true true true true true true false =
      ManifestClosureRejected.
Proof. split; reflexivity. Qed.
