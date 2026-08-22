From Stdlib Require Import Arith.PeanoNat Bool.Bool.

(*
  PHIL-LLVM-STRENGTH-001 — proof-oriented model of strengthening authority and
  defined-execution discipline in Phil.LLVM.Verify.

  Concrete Map enumeration, LLVM syntax/rendering, and construction of the
  authorization map remain implementation correspondence boundaries.  The
  normalized model proves that accepted strengthenings are declared under the
  same key as their stable identity, have nonempty claims, exist at the
  declared location, are used exactly once at that location with the correct
  use kind, and cite an explicitly permitted authority that actually exists.
  It also proves rejection of unjustified unreachable, poison, undef, and
  freeze, and makes explicit that llvm.assume cannot replace mandatory runtime
  preservation.
*)

Definition StrengtheningId := nat.
Definition ClaimId := nat.
Definition AuthorityId := nat.
Definition FunctionId := nat.
Definition BlockId := nat.
Definition RuntimeSiteId := nat.

Inductive StrengtheningKind : Type :=
| NoUnsignedWrapKind
| NoSignedWrapKind
| InBoundsKind
| AssumeKind
| UnreachableFactKind.

Record Strengthening : Type := mkStrengthening {
  strengtheningStableId : StrengtheningId;
  strengtheningKind : StrengtheningKind;
  strengtheningClaim : ClaimId;
  strengtheningClaimNonempty : bool;
  strengtheningAuthority : AuthorityId;
  strengtheningFunction : FunctionId;
  strengtheningBlock : BlockId
}.

Record StrengtheningEnvironment : Type := mkStrengtheningEnvironment {
  strengtheningLookup : StrengtheningId -> option Strengthening;
  strengtheningUseCount : StrengtheningId -> nat;
  strengtheningUseFunction : StrengtheningId -> option FunctionId;
  strengtheningUseBlock : StrengtheningId -> option BlockId;
  strengtheningUseInTerminator : StrengtheningId -> bool;
  strengtheningLocationExists : FunctionId -> BlockId -> bool;
  strengtheningAuthorityPermitted : ClaimId -> AuthorityId -> bool;
  strengtheningAuthorityExists : AuthorityId -> bool;
  strengtheningPoisonPresent : bool;
  strengtheningUndefPresent : bool;
  strengtheningFreezePresent : bool;
  strengtheningUnjustifiedUnreachablePresent : bool
}.

Definition kindMatchesLocation
  (kind : StrengtheningKind)
  (inTerminator : bool) : bool :=
  match kind with
  | UnreachableFactKind => inTerminator
  | _ => negb inTerminator
  end.

Definition StrengtheningEntryVerificationSuccess
  (environment : StrengtheningEnvironment)
  (key : StrengtheningId)
  (entry : Strengthening) : Prop :=
  key = strengtheningStableId entry /\
  strengtheningClaimNonempty entry = true /\
  strengtheningLocationExists environment
    (strengtheningFunction entry) (strengtheningBlock entry) = true /\
  strengtheningUseCount environment key = 1 /\
  strengtheningUseFunction environment key = Some (strengtheningFunction entry) /\
  strengtheningUseBlock environment key = Some (strengtheningBlock entry) /\
  kindMatchesLocation
    (strengtheningKind entry)
    (strengtheningUseInTerminator environment key) = true /\
  strengtheningAuthorityPermitted environment
    (strengtheningClaim entry) (strengtheningAuthority entry) = true /\
  strengtheningAuthorityExists environment (strengtheningAuthority entry) = true.

Definition StrengtheningVerificationSuccess
  (environment : StrengtheningEnvironment) : Prop :=
  (forall strengtheningId,
    strengtheningUseCount environment strengtheningId <> 0 ->
    exists entry,
      strengtheningLookup environment strengtheningId = Some entry) /\
  (forall key entry,
    strengtheningLookup environment key = Some entry ->
    StrengtheningEntryVerificationSuccess environment key entry) /\
  strengtheningPoisonPresent environment = false /\
  strengtheningUndefPresent environment = false /\
  strengtheningFreezePresent environment = false /\
  strengtheningUnjustifiedUnreachablePresent environment = false.

Theorem verified_strengthening_use_has_declaration :
  forall environment strengtheningId,
    StrengtheningVerificationSuccess environment ->
    strengtheningUseCount environment strengtheningId <> 0 ->
    exists entry,
      strengtheningLookup environment strengtheningId = Some entry.
Proof.
  intros environment strengtheningId Hverified Hused.
  destruct Hverified as [Huses _].
  apply Huses.
  exact Hused.
Qed.

Theorem verified_strengthening_key_matches_stable_id :
  forall environment key entry,
    StrengtheningVerificationSuccess environment ->
    strengtheningLookup environment key = Some entry ->
    key = strengtheningStableId entry.
Proof.
  intros environment key entry Hverified Hlookup.
  destruct Hverified as [_ [Hentries _]].
  pose proof (Hentries key entry Hlookup) as Hentry.
  destruct Hentry as [Hkey _].
  exact Hkey.
Qed.

Theorem verified_strengthening_claim_is_nonempty :
  forall environment key entry,
    StrengtheningVerificationSuccess environment ->
    strengtheningLookup environment key = Some entry ->
    strengtheningClaimNonempty entry = true.
Proof.
  intros environment key entry Hverified Hlookup.
  destruct Hverified as [_ [Hentries _]].
  pose proof (Hentries key entry Hlookup) as Hentry.
  destruct Hentry as [_ [Hclaim _]].
  exact Hclaim.
Qed.

Theorem verified_strengthening_location_exists :
  forall environment key entry,
    StrengtheningVerificationSuccess environment ->
    strengtheningLookup environment key = Some entry ->
    strengtheningLocationExists environment
      (strengtheningFunction entry) (strengtheningBlock entry) = true.
Proof.
  intros environment key entry Hverified Hlookup.
  destruct Hverified as [_ [Hentries _]].
  pose proof (Hentries key entry Hlookup) as Hentry.
  destruct Hentry as [_ [_ [Hlocation _]]].
  exact Hlocation.
Qed.

Theorem verified_strengthening_has_exactly_one_use :
  forall environment key entry,
    StrengtheningVerificationSuccess environment ->
    strengtheningLookup environment key = Some entry ->
    strengtheningUseCount environment key = 1.
Proof.
  intros environment key entry Hverified Hlookup.
  destruct Hverified as [_ [Hentries _]].
  pose proof (Hentries key entry Hlookup) as Hentry.
  destruct Hentry as [_ [_ [_ [Hcount _]]]].
  exact Hcount.
Qed.

Theorem verified_strengthening_use_location_is_exact :
  forall environment key entry,
    StrengtheningVerificationSuccess environment ->
    strengtheningLookup environment key = Some entry ->
    strengtheningUseFunction environment key = Some (strengtheningFunction entry) /\
    strengtheningUseBlock environment key = Some (strengtheningBlock entry).
Proof.
  intros environment key entry Hverified Hlookup.
  destruct Hverified as [_ [Hentries _]].
  pose proof (Hentries key entry Hlookup) as Hentry.
  destruct Hentry as [_ [_ [_ [_ [Hfunction [Hblock _]]]]]].
  split; assumption.
Qed.

Theorem verified_strengthening_use_kind_matches_location :
  forall environment key entry,
    StrengtheningVerificationSuccess environment ->
    strengtheningLookup environment key = Some entry ->
    kindMatchesLocation
      (strengtheningKind entry)
      (strengtheningUseInTerminator environment key) = true.
Proof.
  intros environment key entry Hverified Hlookup.
  destruct Hverified as [_ [Hentries _]].
  pose proof (Hentries key entry Hlookup) as Hentry.
  destruct Hentry as [_ [_ [_ [_ [_ [_ [Hkind _]]]]]]].
  exact Hkind.
Qed.

Theorem verified_strengthening_authority_is_permitted :
  forall environment key entry,
    StrengtheningVerificationSuccess environment ->
    strengtheningLookup environment key = Some entry ->
    strengtheningAuthorityPermitted environment
      (strengtheningClaim entry) (strengtheningAuthority entry) = true.
Proof.
  intros environment key entry Hverified Hlookup.
  destruct Hverified as [_ [Hentries _]].
  pose proof (Hentries key entry Hlookup) as Hentry.
  destruct Hentry as [_ [_ [_ [_ [_ [_ [_ [Hpermitted _]]]]]]]].
  exact Hpermitted.
Qed.

Theorem verified_strengthening_authority_exists :
  forall environment key entry,
    StrengtheningVerificationSuccess environment ->
    strengtheningLookup environment key = Some entry ->
    strengtheningAuthorityExists environment (strengtheningAuthority entry) = true.
Proof.
  intros environment key entry Hverified Hlookup.
  destruct Hverified as [_ [Hentries _]].
  pose proof (Hentries key entry Hlookup) as Hentry.
  destruct Hentry as [_ [_ [_ [_ [_ [_ [_ [_ Hexists]]]]]]]].
  exact Hexists.
Qed.

Theorem poison_is_rejected :
  forall environment,
    strengtheningPoisonPresent environment = true ->
    ~ StrengtheningVerificationSuccess environment.
Proof.
  intros environment Hpoison Hverified.
  destruct Hverified as [_ [_ [Hnone _]]].
  rewrite Hpoison in Hnone.
  discriminate.
Qed.

Theorem undef_is_rejected :
  forall environment,
    strengtheningUndefPresent environment = true ->
    ~ StrengtheningVerificationSuccess environment.
Proof.
  intros environment Hundef Hverified.
  destruct Hverified as [_ [_ [_ [Hnone _]]]].
  rewrite Hundef in Hnone.
  discriminate.
Qed.

Theorem freeze_is_rejected :
  forall environment,
    strengtheningFreezePresent environment = true ->
    ~ StrengtheningVerificationSuccess environment.
Proof.
  intros environment Hfreeze Hverified.
  destruct Hverified as [_ [_ [_ [_ [Hnone _]]]]].
  rewrite Hfreeze in Hnone.
  discriminate.
Qed.

Theorem unjustified_unreachable_is_rejected :
  forall environment,
    strengtheningUnjustifiedUnreachablePresent environment = true ->
    ~ StrengtheningVerificationSuccess environment.
Proof.
  intros environment Hunreachable Hverified.
  destruct Hverified as [_ [_ [_ [_ [_ Hnone]]]]].
  rewrite Hunreachable in Hnone.
  discriminate.
Qed.

Record RuntimeSubstitutionModel : Type := mkRuntimeSubstitutionModel {
  substitutionSourceRuntimeCount : RuntimeSiteId -> nat;
  substitutionTargetRuntimeCount : RuntimeSiteId -> nat;
  substitutionAssumePresent : bool
}.

Definition RuntimePreservationRequired
  (model : RuntimeSubstitutionModel) : Prop :=
  forall site,
    substitutionSourceRuntimeCount model site =
      substitutionTargetRuntimeCount model site.

Theorem assume_cannot_replace_missing_runtime_enforcement :
  forall model site,
    substitutionAssumePresent model = true ->
    substitutionSourceRuntimeCount model site <>
      substitutionTargetRuntimeCount model site ->
    ~ RuntimePreservationRequired model.
Proof.
  intros model site Hassume Hmismatch Hpreserved.
  apply Hmismatch.
  apply Hpreserved.
Qed.
