From Stdlib Require Import Bool.Bool.

Inductive ReviewR01Decision : Type :=
| ReviewR01Accepted
| ReviewR01Rejected.

Definition reviewR01Factsb
  (surfaceSystemsIdentityExact llvmProjectionExact
   sourceNamespaceInjective syntheticNamespaceInjective blockNamespaceInjective
   sourceSyntheticDisjoint sourceBlockDisjoint syntheticBlockDisjoint
   renderedDefinitionsUnique : bool) : bool :=
  surfaceSystemsIdentityExact &&
  llvmProjectionExact &&
  sourceNamespaceInjective &&
  syntheticNamespaceInjective &&
  blockNamespaceInjective &&
  sourceSyntheticDisjoint &&
  sourceBlockDisjoint &&
  syntheticBlockDisjoint &&
  renderedDefinitionsUnique.

Definition decideReviewR01
  (surfaceSystemsIdentityExact llvmProjectionExact
   sourceNamespaceInjective syntheticNamespaceInjective blockNamespaceInjective
   sourceSyntheticDisjoint sourceBlockDisjoint syntheticBlockDisjoint
   renderedDefinitionsUnique : bool) : ReviewR01Decision :=
  if reviewR01Factsb
      surfaceSystemsIdentityExact llvmProjectionExact
      sourceNamespaceInjective syntheticNamespaceInjective blockNamespaceInjective
      sourceSyntheticDisjoint sourceBlockDisjoint syntheticBlockDisjoint
      renderedDefinitionsUnique
  then ReviewR01Accepted
  else ReviewR01Rejected.

Theorem exact_review_r01_accepts :
  decideReviewR01
    true true true true true true true true true =
  ReviewR01Accepted.
Proof. reflexivity. Qed.

Theorem projection_identity_drift_rejects :
  decideReviewR01
    false true true true true true true true true =
      ReviewR01Rejected /\
  decideReviewR01
    true false true true true true true true true =
      ReviewR01Rejected.
Proof. split; reflexivity. Qed.

Theorem noninjective_namespace_rejects :
  decideReviewR01
    true true false true true true true true true =
      ReviewR01Rejected /\
  decideReviewR01
    true true true false true true true true true =
      ReviewR01Rejected /\
  decideReviewR01
    true true true true false true true true true =
      ReviewR01Rejected.
Proof. repeat split; reflexivity. Qed.

Theorem cross_namespace_collision_rejects :
  decideReviewR01
    true true true true true false true true true =
      ReviewR01Rejected /\
  decideReviewR01
    true true true true true true false true true =
      ReviewR01Rejected /\
  decideReviewR01
    true true true true true true true false true =
      ReviewR01Rejected.
Proof. repeat split; reflexivity. Qed.

Theorem duplicate_rendered_definition_rejects :
  decideReviewR01
    true true true true true true true true false =
  ReviewR01Rejected.
Proof. reflexivity. Qed.
