From Stdlib Require Import Bool.Bool.

(*
  PHIL-P1-REVIEW-R05 — public Rocq proof authority is a trusted-packaging
  boundary, not an in-process Rocq checker.

  The public certification adapter may package ProofAssistantTheorem authority
  only when the caller explicitly selects the trusted checked-input path.  The
  resulting authority must continue to name that external-check precondition
  and bind both source and compiled proof artifacts.

  Critically, this theorem family does not claim that the packaging adapter
  itself authenticates Rocq or proves that arbitrary compiled bytes are valid.
  Successful Rocq checking remains an explicit producer-side trust premise.
*)

Record TrustedRocqPackagingFacts : Type := mkTrustedRocqPackagingFacts {
  trustedPackagingAcknowledged : bool;
  obligationMarkerPresent : bool;
  expectedTheoremDeclarationsPresent : bool;
  sourceArtifactDigestBound : bool;
  compiledArtifactDigestBound : bool;
  certificateNamesTrustedPackaging : bool;
  evidenceNamesExternalCheckPrecondition : bool
}.

Definition TrustedRocqPackagingAccepted
  (facts : TrustedRocqPackagingFacts) : Prop :=
  trustedPackagingAcknowledged facts = true /\
  obligationMarkerPresent facts = true /\
  expectedTheoremDeclarationsPresent facts = true /\
  sourceArtifactDigestBound facts = true /\
  compiledArtifactDigestBound facts = true /\
  certificateNamesTrustedPackaging facts = true /\
  evidenceNamesExternalCheckPrecondition facts = true.

Theorem accepted_public_packaging_requires_explicit_trust_acknowledgement :
  forall facts,
    TrustedRocqPackagingAccepted facts ->
    trustedPackagingAcknowledged facts = true.
Proof.
  intros facts Haccepted.
  exact (proj1 Haccepted).
Qed.

Theorem accepted_public_packaging_names_external_check_boundary :
  forall facts,
    TrustedRocqPackagingAccepted facts ->
    certificateNamesTrustedPackaging facts = true /\
    evidenceNamesExternalCheckPrecondition facts = true.
Proof.
  intros facts Haccepted.
  destruct Haccepted as
    [_ [_ [_ [_ [_ [Hcertificate Hevidence]]]]]].
  split; assumption.
Qed.

Theorem accepted_public_packaging_binds_source_and_compiled_artifacts :
  forall facts,
    TrustedRocqPackagingAccepted facts ->
    sourceArtifactDigestBound facts = true /\
    compiledArtifactDigestBound facts = true.
Proof.
  intros facts Haccepted.
  destruct Haccepted as
    [_ [_ [_ [Hsource [Hcompiled _]]]]].
  split; assumption.
Qed.

Theorem missing_trust_acknowledgement_rejects :
  forall facts,
    trustedPackagingAcknowledged facts = false ->
    ~ TrustedRocqPackagingAccepted facts.
Proof.
  intros facts Hfalse Haccepted.
  pose proof
    (accepted_public_packaging_requires_explicit_trust_acknowledgement
      facts Haccepted) as Htrue.
  rewrite Hfalse in Htrue.
  discriminate.
Qed.

Theorem missing_source_profile_or_theorem_declaration_rejects :
  forall facts,
    obligationMarkerPresent facts = false \/
    expectedTheoremDeclarationsPresent facts = false ->
    ~ TrustedRocqPackagingAccepted facts.
Proof.
  intros facts Hmissing Haccepted.
  destruct Haccepted as [_ [Hmarker [Htheorems _]]].
  destruct Hmissing as [Hmissing | Hmissing].
  - rewrite Hmissing in Hmarker. discriminate.
  - rewrite Hmissing in Htheorems. discriminate.
Qed.

Definition ExternalRocqCheckEstablishedByPackagingAdapter : Prop := False.

Theorem packaging_adapter_does_not_claim_to_establish_external_rocq_check :
  ~ ExternalRocqCheckEstablishedByPackagingAdapter.
Proof.
  unfold ExternalRocqCheckEstablishedByPackagingAdapter.
  tauto.
Qed.

Definition TrustedRocqAuthorityUse
  (externallyChecked : Prop)
  (facts : TrustedRocqPackagingFacts) : Prop :=
  externallyChecked /\ TrustedRocqPackagingAccepted facts.

Theorem public_proof_authority_retains_external_check_as_premise :
  forall externallyChecked facts,
    TrustedRocqAuthorityUse externallyChecked facts ->
    externallyChecked.
Proof.
  intros externallyChecked facts Hauthority.
  exact (proj1 Hauthority).
Qed.
