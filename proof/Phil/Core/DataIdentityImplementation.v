From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import DataIdentity.

(*
  PHIL-DATA-ID-001 — representation-neutral implementation correspondence.

  Production keeps concrete alias traversal, nominal-key representation, and
  finite operation-set membership native. This layer owns the final semantic
  decisions over the exact reflected facts:

    - whether the two fully resolved nominal identities match; and
    - whether the requested operation is explicitly present in the independent
      operation contract.

  The operation decision deliberately does not consume an identity/shape fact:
  definitional identity cannot manufacture equality/hash/serialization/ABI or
  any other DATA-011 competence.
*)

Inductive DataIdentityDecision : Type :=
| DataIdentityAccepted
| DataIdentityRejected.

Definition decideDataIdentityByFact
  (resolvedIdentityMatches : bool) : DataIdentityDecision :=
  if resolvedIdentityMatches then DataIdentityAccepted else DataIdentityRejected.

Inductive DataOperationDecision : Type :=
| DataOperationAccepted
| DataOperationRejected.

Definition decideDataOperationByFact
  (operationExplicitlyGranted : bool) : DataOperationDecision :=
  if operationExplicitlyGranted then DataOperationAccepted else DataOperationRejected.

Definition decideDataOperationAfterIdentityByFacts
  (_identityMatches operationExplicitlyGranted : bool) : DataOperationDecision :=
  decideDataOperationByFact operationExplicitlyGranted.

Theorem data_identity_reflection_sound_complete :
  forall left right reflected,
    (reflected = true <-> DefinitionallyEqualDataType left right) ->
    (decideDataIdentityByFact reflected = DataIdentityAccepted <->
      DefinitionallyEqualDataType left right).
Proof.
  intros left right reflected Hreflect.
  destruct reflected.
  - split.
    + intro Haccepted. apply Hreflect. reflexivity.
    + intro Hequal. reflexivity.
  - split.
    + intro H. discriminate.
    + intro Hequal.
      exfalso.
      apply (proj2 Hreflect) in Hequal.
      discriminate.
Qed.

Theorem reflected_identity_mismatch_rejects :
  decideDataIdentityByFact false = DataIdentityRejected.
Proof. reflexivity. Qed.

Theorem reflected_identity_match_accepts :
  decideDataIdentityByFact true = DataIdentityAccepted.
Proof. reflexivity. Qed.

Theorem data_operation_reflection_sound_complete :
  forall contract operation reflected,
    (reflected = true <-> permitsOperation contract operation) ->
    (decideDataOperationByFact reflected = DataOperationAccepted <->
      permitsOperation contract operation).
Proof.
  intros contract operation reflected Hreflect.
  destruct reflected.
  - split.
    + intro Haccepted. apply Hreflect. reflexivity.
    + intro Hpermit. reflexivity.
  - split.
    + intro H. discriminate.
    + intro Hpermit.
      exfalso.
      apply (proj2 Hreflect) in Hpermit.
      discriminate.
Qed.

Theorem explicit_operation_absence_rejects :
  decideDataOperationByFact false = DataOperationRejected.
Proof. reflexivity. Qed.

Theorem explicit_operation_presence_accepts :
  decideDataOperationByFact true = DataOperationAccepted.
Proof. reflexivity. Qed.

Theorem identity_cannot_change_operation_decision :
  forall firstIdentityFact secondIdentityFact operationExplicitlyGranted,
    decideDataOperationAfterIdentityByFacts
      firstIdentityFact operationExplicitlyGranted =
    decideDataOperationAfterIdentityByFacts
      secondIdentityFact operationExplicitlyGranted.
Proof. reflexivity. Qed.

Theorem identity_match_cannot_manufacture_ungranted_operation :
  decideDataOperationAfterIdentityByFacts true false = DataOperationRejected.
Proof. reflexivity. Qed.

Theorem identity_mismatch_cannot_hide_explicit_operation_grant :
  decideDataOperationAfterIdentityByFacts false true = DataOperationAccepted.
Proof. reflexivity. Qed.
