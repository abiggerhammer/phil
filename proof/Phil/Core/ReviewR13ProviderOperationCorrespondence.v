From Stdlib Require Import Arith.PeanoNat.

From Phil.Core Require Import SystemsSubjectAuthority.

(*
  PHIL-P1-REVIEW-R13 — every represented provider call must agree with an
  independently supplied semantic expectation for both provider occurrence and
  qualified provider operation.

  PHIL-SYS-SUBJECT-AUTH-001 remains the underlying SYS-005 authority: the
  provider call must already use an exact qualified binding, accepted provider
  admission, exact interface, selected operation, exact implementation entry,
  and exact represented call-site domain.

  R13 adds a separate source/Core expectation so the candidate link cannot
  define which provider occurrence or operation it was supposed to denote.
  Runtime symbol spelling is deliberately absent from this semantic relation.
  Completeness of the independent expectation inventory is REVIEW-R14.
*)

Definition ReviewR13ProviderOccurrence := nat.
Definition ReviewR13ProviderOperation := nat.
Definition ReviewR13RuntimeSymbol := nat.

Record ReviewR13Expectation : Type := mkReviewR13Expectation {
  r13ExpectedOccurrence : ReviewR13ProviderOccurrence;
  r13ExpectedOperation : ReviewR13ProviderOperation
}.

Record ReviewR13ExactLink : Type := mkReviewR13ExactLink {
  r13LinkOccurrence : ReviewR13ProviderOccurrence;
  r13LinkOperation : ReviewR13ProviderOperation;
  r13LinkRuntimeSymbol : ReviewR13RuntimeSymbol
}.

Definition ReviewR13ExpectationMatches
  (expected : ReviewR13Expectation)
  (link : ReviewR13ExactLink) : Prop :=
  r13ExpectedOccurrence expected = r13LinkOccurrence link /\
  r13ExpectedOperation expected = r13LinkOperation link.

Definition ReviewR13Accepted
  (base : ProviderCallStageFacts)
  (expected : ReviewR13Expectation)
  (link : ReviewR13ExactLink) : Prop :=
  provider_call_stage_ok base /\
  ReviewR13ExpectationMatches expected link.

Definition ReviewR13SiteAccepted
  (base : ProviderCallStageFacts)
  (expected : option ReviewR13Expectation)
  (link : ReviewR13ExactLink) : Prop :=
  match expected with
  | Some semanticExpectation =>
      ReviewR13Accepted base semanticExpectation link
  | None => False
  end.

Theorem review_r13_missing_independent_expectation_rejects :
  forall base link,
    ~ ReviewR13SiteAccepted base None link.
Proof.
  intros base link H.
  exact H.
Qed.

Theorem review_r13_cross_provider_donor_rejects :
  forall base expected link,
    r13ExpectedOccurrence expected <> r13LinkOccurrence link ->
    ~ ReviewR13Accepted base expected link.
Proof.
  intros base expected link Hmismatch Haccepted.
  destruct Haccepted as [_ [Hoccurrence _]].
  apply Hmismatch.
  exact Hoccurrence.
Qed.

Theorem review_r13_same_provider_wrong_operation_rejects :
  forall base expected link,
    r13ExpectedOperation expected <> r13LinkOperation link ->
    ~ ReviewR13Accepted base expected link.
Proof.
  intros base expected link Hmismatch Haccepted.
  destruct Haccepted as [_ [_ Hoperation]].
  apply Hmismatch.
  exact Hoperation.
Qed.

Definition reviewR13RenameRuntimeSymbol
  (link : ReviewR13ExactLink)
  (symbol : ReviewR13RuntimeSymbol) : ReviewR13ExactLink :=
  mkReviewR13ExactLink
    (r13LinkOccurrence link)
    (r13LinkOperation link)
    symbol.

Theorem review_r13_runtime_symbol_rename_is_nonauthoritative :
  forall base expected link symbol,
    ReviewR13Accepted base expected link <->
    ReviewR13Accepted
      base expected (reviewR13RenameRuntimeSymbol link symbol).
Proof.
  intros base expected link symbol.
  unfold ReviewR13Accepted, ReviewR13ExpectationMatches,
    reviewR13RenameRuntimeSymbol.
  simpl.
  split.
  - intros [Hbase [Hoccurrence Hoperation]].
    repeat split; assumption.
  - intros [Hbase [Hoccurrence Hoperation]].
    repeat split; assumption.
Qed.

Theorem review_r13_acceptance_preserves_sys005_exact_operation :
  forall base expected link,
    ReviewR13Accepted base expected link ->
    provider_operation_exact base.
Proof.
  intros base expected link Haccepted.
  destruct Haccepted as [Hbase _].
  exact
    (proj1
      (accepted_provider_call_has_exact_operation_and_entry
        base Hbase)).
Qed.

Theorem review_r13_acceptance_requires_exact_provider_binding_basis :
  forall base expected link,
    ReviewR13Accepted base expected link ->
    provider_binding_basis base <> RuntimeSymbolOnlyProviderCall.
Proof.
  intros base expected link Haccepted Heq.
  destruct Haccepted as [Hbase _].
  destruct Hbase as [_ [Hbinding _]].
  rewrite Heq in Hbinding.
  simpl in Hbinding.
  exact Hbinding.
Qed.

Theorem review_r13_acceptance_has_independent_occurrence_and_operation :
  forall base expected link,
    ReviewR13Accepted base expected link ->
    r13ExpectedOccurrence expected = r13LinkOccurrence link /\
    r13ExpectedOperation expected = r13LinkOperation link.
Proof.
  intros base expected link Haccepted.
  exact (proj2 Haccepted).
Qed.
