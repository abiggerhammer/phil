From Stdlib Require Import Bool.Bool.

Inductive ReviewR04Decision : Type :=
| ReviewR04Accepted
| ReviewR04Rejected.

Definition reviewR04Factsb
  (lineageSeparated exactRevisionEvidence
   justificationAcyclic recursiveRevisitRejected : bool) : bool :=
  lineageSeparated &&
  exactRevisionEvidence &&
  justificationAcyclic &&
  recursiveRevisitRejected.

Definition decideReviewR04
  (lineageSeparated exactRevisionEvidence
   justificationAcyclic recursiveRevisitRejected : bool)
  : ReviewR04Decision :=
  if reviewR04Factsb
      lineageSeparated exactRevisionEvidence
      justificationAcyclic recursiveRevisitRejected
  then ReviewR04Accepted
  else ReviewR04Rejected.

Theorem exact_review_r04_accepts :
  decideReviewR04 true true true true = ReviewR04Accepted.
Proof. reflexivity. Qed.

Theorem lineage_authority_collapse_rejects :
  decideReviewR04 false true true true = ReviewR04Rejected.
Proof. reflexivity. Qed.

Theorem nonexact_revision_evidence_rejects :
  decideReviewR04 true false true true = ReviewR04Rejected.
Proof. reflexivity. Qed.

Theorem cyclic_justification_rejects :
  decideReviewR04 true true false true = ReviewR04Rejected.
Proof. reflexivity. Qed.

Theorem recursive_revisit_acceptance_rejects :
  decideReviewR04 true true true false = ReviewR04Rejected.
Proof. reflexivity. Qed.
