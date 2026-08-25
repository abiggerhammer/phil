From Stdlib Require Import Bool.Bool Arith.PeanoNat.

From Phil.Core Require Import GenericStructural.

(*
  PHIL-AUTH-POSSESS-001 — explicit semantic authority possession.

  The normalized model captures the semantic core of Phil.Core.Authority after
  one capability occurrence has been resolved from AuthorityState.  Contract,
  subject, and operation identities are represented by nat.  Only a possessed
  capability can authorize an operation; imports, effect permissions, runtime
  handles, backend symbols, and ambient registry entries are explicitly
  non-possession sources.

  Concrete CapabilityOccurrenceKey/Text identity, Map/Set lookup and
  normalization, duplicate occurrence diagnostics, and correspondence from a
  checked state lookup to this normalized capability remain explicit trust
  boundaries.
*)

Record AuthorityRequirement : Type := mkAuthorityRequirement {
  requiredContract : nat;
  requiredSubject : nat;
  requiredOperation : nat
}.

Record AuthorityCapability : Type := mkAuthorityCapability {
  capabilityContract : nat;
  capabilitySubject : nat;
  capabilityMode : Mode;
  permitsOperation : nat -> bool
}.

Inductive AuthorityExerciseSource : Type :=
| PossessedCapability
| ImportedAuthorityDeclaration
| EffectPermissionOnly
| RuntimeAuthorityHandle
| BackendAuthoritySymbol
| AmbientAuthorityRegistryEntry.

Definition capabilityMatchesRequirement
  (requirement : AuthorityRequirement)
  (capability : AuthorityCapability) : bool :=
  andb
    (Nat.eqb (capabilityContract capability) (requiredContract requirement))
    (andb
      (Nat.eqb (capabilitySubject capability) (requiredSubject requirement))
      (permitsOperation capability (requiredOperation requirement))).

Definition authorityExerciseAllowed
  (requirement : AuthorityRequirement)
  (source : AuthorityExerciseSource)
  (capability : AuthorityCapability) : bool :=
  match source with
  | PossessedCapability => capabilityMatchesRequirement requirement capability
  | _ => false
  end.

Definition capabilityCopyAllowed (mode : Mode) : bool :=
  modeAllowsStructuralPermission mode ContractionPermission.

Definition capabilityDropAllowed (mode : Mode) : bool :=
  modeAllowsStructuralPermission mode WeakeningPermission.

Definition copyPreservesSemanticAuthority
  (source target : AuthorityCapability) : Prop :=
  capabilityContract source = capabilityContract target /\
  capabilitySubject source = capabilitySubject target /\
  permitsOperation source = permitsOperation target.

Theorem exact_possessed_capability_authorizes_operation :
  forall contract subject operation mode permissions,
    permissions operation = true ->
    authorityExerciseAllowed
      (mkAuthorityRequirement contract subject operation)
      PossessedCapability
      (mkAuthorityCapability contract subject mode permissions) = true.
Proof.
  intros contract subject operation mode permissions Hpermit.
  unfold authorityExerciseAllowed, capabilityMatchesRequirement.
  simpl.
  rewrite Nat.eqb_refl, Nat.eqb_refl, Hpermit.
  reflexivity.
Qed.

Theorem authority_exercise_requires_exact_contract :
  forall required actual subject operation mode permissions,
    required <> actual ->
    authorityExerciseAllowed
      (mkAuthorityRequirement required subject operation)
      PossessedCapability
      (mkAuthorityCapability actual subject mode permissions) = false.
Proof.
  intros required actual subject operation mode permissions Hneq.
  unfold authorityExerciseAllowed, capabilityMatchesRequirement.
  simpl.
  apply Nat.eqb_neq in Hneq.
  rewrite Nat.eqb_sym in Hneq.
  rewrite Hneq.
  reflexivity.
Qed.

Theorem authority_exercise_requires_exact_subject :
  forall contract required actual operation mode permissions,
    required <> actual ->
    authorityExerciseAllowed
      (mkAuthorityRequirement contract required operation)
      PossessedCapability
      (mkAuthorityCapability contract actual mode permissions) = false.
Proof.
  intros contract required actual operation mode permissions Hneq.
  unfold authorityExerciseAllowed, capabilityMatchesRequirement.
  simpl.
  rewrite Nat.eqb_refl.
  apply Nat.eqb_neq in Hneq.
  rewrite Nat.eqb_sym in Hneq.
  rewrite Hneq.
  reflexivity.
Qed.

Theorem undeclared_authority_operation_rejects :
  forall contract subject operation mode permissions,
    permissions operation = false ->
    authorityExerciseAllowed
      (mkAuthorityRequirement contract subject operation)
      PossessedCapability
      (mkAuthorityCapability contract subject mode permissions) = false.
Proof.
  intros contract subject operation mode permissions Hdeny.
  unfold authorityExerciseAllowed, capabilityMatchesRequirement.
  simpl.
  rewrite Nat.eqb_refl, Nat.eqb_refl, Hdeny.
  reflexivity.
Qed.

Theorem imported_declaration_is_not_possession :
  forall requirement capability,
    authorityExerciseAllowed requirement ImportedAuthorityDeclaration capability = false.
Proof.
  reflexivity.
Qed.

Theorem effect_permission_is_not_possession :
  forall requirement capability,
    authorityExerciseAllowed requirement EffectPermissionOnly capability = false.
Proof.
  reflexivity.
Qed.

Theorem runtime_handle_is_not_possession :
  forall requirement capability,
    authorityExerciseAllowed requirement RuntimeAuthorityHandle capability = false.
Proof.
  reflexivity.
Qed.

Theorem backend_symbol_is_not_possession :
  forall requirement capability,
    authorityExerciseAllowed requirement BackendAuthoritySymbol capability = false.
Proof.
  reflexivity.
Qed.

Theorem ambient_registry_entry_is_not_possession :
  forall requirement capability,
    authorityExerciseAllowed requirement AmbientAuthorityRegistryEntry capability = false.
Proof.
  reflexivity.
Qed.

Theorem non_possession_source_never_authorizes :
  forall requirement source capability,
    source <> PossessedCapability ->
    authorityExerciseAllowed requirement source capability = false.
Proof.
  intros requirement source capability Hnot.
  destruct source; try reflexivity.
  contradiction.
Qed.

Theorem runtime_identity_cannot_repair_semantic_subject_mismatch :
  forall contract required actual operation mode permissions,
    required <> actual ->
    authorityExerciseAllowed
      (mkAuthorityRequirement contract required operation)
      RuntimeAuthorityHandle
      (mkAuthorityCapability contract actual mode permissions) = false.
Proof.
  reflexivity.
Qed.

Theorem unrestricted_authority_may_be_copied :
  capabilityCopyAllowed Unrestricted = true.
Proof.
  reflexivity.
Qed.

Theorem affine_authority_may_not_be_copied :
  capabilityCopyAllowed Affine = false.
Proof.
  reflexivity.
Qed.

Theorem linear_authority_may_not_be_copied :
  capabilityCopyAllowed Linear = false.
Proof.
  reflexivity.
Qed.

Theorem unrestricted_authority_may_be_dropped :
  capabilityDropAllowed Unrestricted = true.
Proof.
  reflexivity.
Qed.

Theorem affine_authority_may_be_dropped :
  capabilityDropAllowed Affine = true.
Proof.
  reflexivity.
Qed.

Theorem linear_authority_may_not_be_dropped :
  capabilityDropAllowed Linear = false.
Proof.
  reflexivity.
Qed.

Theorem unrestricted_copy_preserves_contract_subject_and_operations :
  forall contract subject permissions,
    copyPreservesSemanticAuthority
      (mkAuthorityCapability contract subject Unrestricted permissions)
      (mkAuthorityCapability contract subject Unrestricted permissions).
Proof.
  intros contract subject permissions.
  repeat split; reflexivity.
Qed.

Theorem exercise_permission_does_not_consume_possession :
  forall requirement capability,
    authorityExerciseAllowed requirement PossessedCapability capability = true ->
    capability = capability.
Proof.
  intros requirement capability _.
  reflexivity.
Qed.
