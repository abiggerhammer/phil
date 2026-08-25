From Stdlib Require Import Bool.Bool Arith.PeanoNat.

From Phil.Core Require Import AuthorityPossession.

(*
  PHIL-AUTH-ATTEN-001 — explicit authority attenuation and non-widening.

  This normalized model is layered on PHIL-AUTH-POSSESS-001. Contract, subject,
  and operation identities remain opaque semantic atoms represented by nat.
  Operation sets are represented extensionally as nat -> bool predicates rather
  than by any concrete Haskell Set ordering.

  Authority attenuation concerns public semantic visibility, not ownership of a
  capability occurrence. Structural mode remains in AuthorityCapability but is
  deliberately absent from AuthoritySurface.
*)

Record AuthoritySurface : Type := mkAuthoritySurface {
  surfaceContract : nat;
  surfaceSubject : nat;
  surfaceOperations : nat -> bool
}.

Record AuthorityAttenuationWitness : Type := mkAuthorityAttenuationWitness {
  witnessSourceContract : nat;
  witnessTargetContract : nat;
  witnessSubject : nat;
  witnessVisibleOperations : nat -> bool
}.

Inductive AuthorityBoundaryKind : Type :=
| GenericBindingBoundary
| CallableSubstitutionBoundary
| ProviderReplacementBoundary
| ArchitectureBoundary
| OtherBoundary.

Definition sameOperationSet
  (left right : nat -> bool) : Prop :=
  forall operation, left operation = right operation.

Definition operationSubset
  (source target : AuthoritySurface) : Prop :=
  forall operation,
    surfaceOperations target operation = true ->
    surfaceOperations source operation = true.

Definition authoritySurfaceFromCapability
  (capability : AuthorityCapability) : AuthoritySurface :=
  mkAuthoritySurface
    (capabilityContract capability)
    (capabilitySubject capability)
    (permitsOperation capability).

Definition exactAuthorityAttenuation
  (source target : AuthoritySurface)
  (witness : AuthorityAttenuationWitness) : Prop :=
  surfaceSubject source = surfaceSubject target /\
  operationSubset source target /\
  witnessSourceContract witness = surfaceContract source /\
  witnessTargetContract witness = surfaceContract target /\
  witnessSubject witness = surfaceSubject target /\
  sameOperationSet
    (witnessVisibleOperations witness)
    (surfaceOperations target).

Definition authorityBoundaryAllowed
  (_kind : AuthorityBoundaryKind)
  (available visible : AuthoritySurface)
  (maybeWitness : option AuthorityAttenuationWitness) : Prop :=
  surfaceSubject available = surfaceSubject visible /\
  operationSubset available visible /\
  ((surfaceContract available = surfaceContract visible /\
    sameOperationSet
      (surfaceOperations available)
      (surfaceOperations visible))
   \/
   (surfaceContract available <> surfaceContract visible /\
    exists witness,
      maybeWitness = Some witness /\
      exactAuthorityAttenuation available visible witness)).

Definition authorityJoinAllowed
  (branches : nat -> AuthoritySurface)
  (continues : nat -> bool)
  (joined : AuthoritySurface) : Prop :=
  (exists branch, continues branch = true) /\
  (forall branch,
    continues branch = true ->
    surfaceSubject (branches branch) = surfaceSubject joined) /\
  (forall branch,
    continues branch = true ->
    surfaceContract (branches branch) = surfaceContract joined) /\
  (forall branch operation,
    continues branch = true ->
    surfaceOperations joined operation = true ->
    surfaceOperations (branches branch) operation = true).

Theorem capability_projection_preserves_semantic_surface :
  forall contract subject mode operations,
    authoritySurfaceFromCapability
      (mkAuthorityCapability contract subject mode operations) =
    mkAuthoritySurface contract subject operations.
Proof.
  reflexivity.
Qed.

Theorem authority_surface_projection_is_mode_independent :
  forall contract subject firstMode secondMode operations,
    authoritySurfaceFromCapability
      (mkAuthorityCapability contract subject firstMode operations) =
    authoritySurfaceFromCapability
      (mkAuthorityCapability contract subject secondMode operations).
Proof.
  reflexivity.
Qed.

Theorem explicit_attenuation_preserves_exact_subject :
  forall source target witness,
    exactAuthorityAttenuation source target witness ->
    surfaceSubject source = surfaceSubject target.
Proof.
  intros source target witness Hchecked.
  unfold exactAuthorityAttenuation in Hchecked.
  destruct Hchecked as [Hsubject _].
  exact Hsubject.
Qed.

Theorem explicit_attenuation_never_widens :
  forall source target witness,
    exactAuthorityAttenuation source target witness ->
    operationSubset source target.
Proof.
  intros source target witness Hchecked.
  unfold exactAuthorityAttenuation in Hchecked.
  destruct Hchecked as [_ [Hsubset _]].
  exact Hsubset.
Qed.

Theorem attenuation_witness_binds_source_contract :
  forall source target witness,
    exactAuthorityAttenuation source target witness ->
    witnessSourceContract witness = surfaceContract source.
Proof.
  intros source target witness Hchecked.
  unfold exactAuthorityAttenuation in Hchecked.
  destruct Hchecked as [_ [_ [Hsource _]]].
  exact Hsource.
Qed.

Theorem attenuation_witness_binds_target_contract :
  forall source target witness,
    exactAuthorityAttenuation source target witness ->
    witnessTargetContract witness = surfaceContract target.
Proof.
  intros source target witness Hchecked.
  unfold exactAuthorityAttenuation in Hchecked.
  destruct Hchecked as [_ [_ [_ [Htarget _]]]].
  exact Htarget.
Qed.

Theorem attenuation_witness_binds_subject :
  forall source target witness,
    exactAuthorityAttenuation source target witness ->
    witnessSubject witness = surfaceSubject target.
Proof.
  intros source target witness Hchecked.
  unfold exactAuthorityAttenuation in Hchecked.
  destruct Hchecked as [_ [_ [_ [_ [Hsubject _]]]]].
  exact Hsubject.
Qed.

Theorem attenuation_witness_binds_visible_operations :
  forall source target witness,
    exactAuthorityAttenuation source target witness ->
    sameOperationSet
      (witnessVisibleOperations witness)
      (surfaceOperations target).
Proof.
  intros source target witness Hchecked.
  unfold exactAuthorityAttenuation in Hchecked.
  destruct Hchecked as [_ [_ [_ [_ [_ Hoperations]]]]].
  exact Hoperations.
Qed.

Theorem exact_narrowing_constructs_checked_attenuation :
  forall source target witness,
    surfaceSubject source = surfaceSubject target ->
    operationSubset source target ->
    witnessSourceContract witness = surfaceContract source ->
    witnessTargetContract witness = surfaceContract target ->
    witnessSubject witness = surfaceSubject target ->
    sameOperationSet
      (witnessVisibleOperations witness)
      (surfaceOperations target) ->
    exactAuthorityAttenuation source target witness.
Proof.
  intros source target witness
    Hsubject Hsubset Hsource Htarget HwitnessSubject Hoperations.
  unfold exactAuthorityAttenuation.
  repeat split; assumption.
Qed.

Theorem authority_boundary_preserves_exact_subject :
  forall kind available visible maybeWitness,
    authorityBoundaryAllowed kind available visible maybeWitness ->
    surfaceSubject available = surfaceSubject visible.
Proof.
  intros kind available visible maybeWitness Hallowed.
  unfold authorityBoundaryAllowed in Hallowed.
  destruct Hallowed as [Hsubject _].
  exact Hsubject.
Qed.

Theorem authority_boundary_never_widens :
  forall kind available visible maybeWitness,
    authorityBoundaryAllowed kind available visible maybeWitness ->
    operationSubset available visible.
Proof.
  intros kind available visible maybeWitness Hallowed.
  unfold authorityBoundaryAllowed in Hallowed.
  destruct Hallowed as [_ [Hsubset _]].
  exact Hsubset.
Qed.

Theorem same_contract_boundary_preserves_operation_surface :
  forall kind available visible maybeWitness,
    authorityBoundaryAllowed kind available visible maybeWitness ->
    surfaceContract available = surfaceContract visible ->
    sameOperationSet
      (surfaceOperations available)
      (surfaceOperations visible).
Proof.
  intros kind available visible maybeWitness Hallowed Hcontract.
  unfold authorityBoundaryAllowed in Hallowed.
  destruct Hallowed as [_ [_ [Hsame | Hchanged]]].
  - destruct Hsame as [_ Hoperations].
    exact Hoperations.
  - destruct Hchanged as [Hdifferent _].
    contradiction.
Qed.

Theorem contract_change_requires_exact_attenuation_witness :
  forall kind available visible maybeWitness,
    authorityBoundaryAllowed kind available visible maybeWitness ->
    surfaceContract available <> surfaceContract visible ->
    exists witness,
      maybeWitness = Some witness /\
      exactAuthorityAttenuation available visible witness.
Proof.
  intros kind available visible maybeWitness Hallowed Hdifferent.
  unfold authorityBoundaryAllowed in Hallowed.
  destruct Hallowed as [_ [_ [Hsame | Hchanged]]].
  - destruct Hsame as [Hcontract _].
    contradiction.
  - destruct Hchanged as [_ [witness [Hwitness Hchecked]]].
    exists witness.
    split; assumption.
Qed.

Theorem boundary_kind_does_not_change_authority_rule :
  forall firstKind secondKind available visible maybeWitness,
    authorityBoundaryAllowed firstKind available visible maybeWitness <->
    authorityBoundaryAllowed secondKind available visible maybeWitness.
Proof.
  intros firstKind secondKind available visible maybeWitness.
  split; intro Hallowed; exact Hallowed.
Qed.

Theorem authority_join_requires_continuing_branch :
  forall branches continues joined,
    authorityJoinAllowed branches continues joined ->
    exists branch, continues branch = true.
Proof.
  intros branches continues joined Hjoin.
  unfold authorityJoinAllowed in Hjoin.
  destruct Hjoin as [Hnonempty _].
  exact Hnonempty.
Qed.

Theorem authority_join_preserves_subject_on_every_branch :
  forall branches continues joined,
    authorityJoinAllowed branches continues joined ->
    forall branch,
      continues branch = true ->
      surfaceSubject (branches branch) = surfaceSubject joined.
Proof.
  intros branches continues joined Hjoin.
  unfold authorityJoinAllowed in Hjoin.
  destruct Hjoin as [_ [Hsubject _]].
  exact Hsubject.
Qed.

Theorem authority_join_preserves_contract_on_every_branch :
  forall branches continues joined,
    authorityJoinAllowed branches continues joined ->
    forall branch,
      continues branch = true ->
      surfaceContract (branches branch) = surfaceContract joined.
Proof.
  intros branches continues joined Hjoin.
  unfold authorityJoinAllowed in Hjoin.
  destruct Hjoin as [_ [_ [Hcontract _]]].
  exact Hcontract.
Qed.

Theorem authority_join_never_unions_branch_local_authority :
  forall branches continues joined,
    authorityJoinAllowed branches continues joined ->
    forall branch operation,
      continues branch = true ->
      surfaceOperations joined operation = true ->
      surfaceOperations (branches branch) operation = true.
Proof.
  intros branches continues joined Hjoin.
  unfold authorityJoinAllowed in Hjoin.
  destruct Hjoin as [_ [_ [_ Hoperations]]].
  exact Hoperations.
Qed.

Theorem branch_local_absence_blocks_join_visibility :
  forall branches continues joined branch operation,
    authorityJoinAllowed branches continues joined ->
    continues branch = true ->
    surfaceOperations (branches branch) operation = false ->
    surfaceOperations joined operation = false.
Proof.
  intros branches continues joined branch operation
    Hjoin Hcontinues Hmissing.
  destruct (surfaceOperations joined operation) eqn:Hvisible.
  - pose proof
      (authority_join_never_unions_branch_local_authority
        branches continues joined Hjoin
        branch operation Hcontinues Hvisible) as Hpresent.
    rewrite Hmissing in Hpresent.
    discriminate.
  - reflexivity.
Qed.

Theorem common_authority_may_join :
  forall branches continues joined,
    (exists branch, continues branch = true) ->
    (forall branch,
      continues branch = true ->
      surfaceSubject (branches branch) = surfaceSubject joined) ->
    (forall branch,
      continues branch = true ->
      surfaceContract (branches branch) = surfaceContract joined) ->
    (forall branch operation,
      continues branch = true ->
      surfaceOperations joined operation = true ->
      surfaceOperations (branches branch) operation = true) ->
    authorityJoinAllowed branches continues joined.
Proof.
  intros branches continues joined
    Hnonempty Hsubject Hcontract Hoperations.
  unfold authorityJoinAllowed.
  repeat split; assumption.
Qed.
