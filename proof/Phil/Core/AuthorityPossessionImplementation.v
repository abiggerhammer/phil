From Stdlib Require Import Bool.Bool Arith.PeanoNat.

From Phil.Core Require Import AuthorityPossession.

(*
  PHIL-AUTH-POSSESS-IMPL-001 — executable correspondence for the bounded
  PHIL-AUTH-POSSESS-001 authority-possession semantics.

  Production resolves concrete occurrence identity and Map/Set membership with
  native Haskell representations.  The extracted kernel owns the semantic
  decision once those primitive facts have been reflected: possession source,
  exact contract, exact subject, operation membership, and structural mode for
  copy/drop.
*)

Inductive AuthorityExerciseDecision : Type :=
| AuthorityExerciseSourceRejected
| AuthorityExerciseContractRejected
| AuthorityExerciseSubjectRejected
| AuthorityExerciseOperationRejected
| AuthorityExerciseAccepted.

Definition decideAuthorityExerciseFacts
  (sourcePossessed contractMatches subjectMatches operationPermitted : bool)
  : AuthorityExerciseDecision :=
  if sourcePossessed then
    if contractMatches then
      if subjectMatches then
        if operationPermitted then AuthorityExerciseAccepted
        else AuthorityExerciseOperationRejected
      else AuthorityExerciseSubjectRejected
    else AuthorityExerciseContractRejected
  else AuthorityExerciseSourceRejected.

Definition sourceIsPossessed (source : AuthorityExerciseSource) : bool :=
  match source with
  | PossessedCapability => true
  | _ => false
  end.

Definition authorityExerciseDecision
  (requirement : AuthorityRequirement)
  (source : AuthorityExerciseSource)
  (capability : AuthorityCapability) : AuthorityExerciseDecision :=
  decideAuthorityExerciseFacts
    (sourceIsPossessed source)
    (Nat.eqb (capabilityContract capability) (requiredContract requirement))
    (Nat.eqb (capabilitySubject capability) (requiredSubject requirement))
    (permitsOperation capability (requiredOperation requirement)).

Theorem authority_exercise_decision_accept_iff_certified :
  forall requirement source capability,
    authorityExerciseDecision requirement source capability =
      AuthorityExerciseAccepted <->
    authorityExerciseAllowed requirement source capability = true.
Proof.
  intros requirement source capability.
  destruct source;
    cbn [authorityExerciseDecision sourceIsPossessed
         decideAuthorityExerciseFacts authorityExerciseAllowed
         capabilityMatchesRequirement].
  - destruct (Nat.eqb (capabilityContract capability)
              (requiredContract requirement));
      cbn;
      destruct (Nat.eqb (capabilitySubject capability)
                (requiredSubject requirement));
      cbn;
      destruct (permitsOperation capability (requiredOperation requirement));
      cbn;
      split; intro H; try discriminate; reflexivity.
  - split; intro H; discriminate.
  - split; intro H; discriminate.
  - split; intro H; discriminate.
  - split; intro H; discriminate.
  - split; intro H; discriminate.
Qed.

Theorem authority_exercise_source_rejection_precedes_semantic_facts :
  forall contractMatches subjectMatches operationPermitted,
    decideAuthorityExerciseFacts false contractMatches subjectMatches
      operationPermitted = AuthorityExerciseSourceRejected.
Proof.
  reflexivity.
Qed.

Theorem authority_exercise_contract_rejection_precedes_subject_and_operation :
  forall subjectMatches operationPermitted,
    decideAuthorityExerciseFacts true false subjectMatches operationPermitted =
      AuthorityExerciseContractRejected.
Proof.
  reflexivity.
Qed.

Theorem authority_exercise_subject_rejection_precedes_operation :
  forall operationPermitted,
    decideAuthorityExerciseFacts true true false operationPermitted =
      AuthorityExerciseSubjectRejected.
Proof.
  reflexivity.
Qed.

Theorem authority_exercise_operation_rejection_is_final_semantic_gate :
  decideAuthorityExerciseFacts true true true false =
    AuthorityExerciseOperationRejected.
Proof.
  reflexivity.
Qed.

Theorem authority_exercise_exact_facts_accept :
  decideAuthorityExerciseFacts true true true true = AuthorityExerciseAccepted.
Proof.
  reflexivity.
Qed.

Inductive AuthorityCopyDecision : Type :=
| AuthorityCopyRejected
| AuthorityCopyAccepted.

Definition decideAuthorityCopy (mode : Mode) : AuthorityCopyDecision :=
  if capabilityCopyAllowed mode then AuthorityCopyAccepted
  else AuthorityCopyRejected.

Theorem authority_copy_decision_accept_iff_certified :
  forall mode,
    decideAuthorityCopy mode = AuthorityCopyAccepted <->
    capabilityCopyAllowed mode = true.
Proof.
  destruct mode; reflexivity.
Qed.

Inductive AuthorityDropDecision : Type :=
| AuthorityDropRejected
| AuthorityDropAccepted.

Definition decideAuthorityDrop (mode : Mode) : AuthorityDropDecision :=
  if capabilityDropAllowed mode then AuthorityDropAccepted
  else AuthorityDropRejected.

Theorem authority_drop_decision_accept_iff_certified :
  forall mode,
    decideAuthorityDrop mode = AuthorityDropAccepted <->
    capabilityDropAllowed mode = true.
Proof.
  destruct mode; reflexivity.
Qed.
