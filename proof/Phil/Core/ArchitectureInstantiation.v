From Phil.Core Require Import ArchitectureIdentity.

(* Representation-neutral Phase 1 architecture-instantiation model.
   Concrete graph containers, lookup, and canonical serialization remain
   implementation/correspondence boundaries. *)

Theorem distinct_occurrence_slots_are_generative :
  forall (parent : InstanceKey) (leftSlot rightSlot : nat),
    leftSlot <> rightSlot ->
    scopedInstanceKey parent leftSlot <>
    scopedInstanceKey parent rightSlot.
Proof.
  intros parent leftSlot rightSlot Hneq Heq.
  apply Hneq.
  inversion Heq.
  reflexivity.
Qed.

Theorem same_slot_under_distinct_parents_is_generative :
  forall (leftParent rightParent : InstanceKey) (slot : nat),
    leftParent <> rightParent ->
    scopedInstanceKey leftParent slot <>
    scopedInstanceKey rightParent slot.
Proof.
  intros leftParent rightParent slot Hneq Heq.
  apply Hneq.
  inversion Heq.
  reflexivity.
Qed.

Theorem distinct_occurrence_keys_induce_distinct_instance_identities :
  forall (leftKey rightKey : InstanceKey)
         (parent : option InstanceKey)
         (declaration : DeclarationIdentity)
         (bindings : nat),
    leftKey <> rightKey ->
    deriveArchitectureInstanceIdentity
      {| architectureInstanceKey := leftKey;
         architectureParentInstanceKey := parent;
         architectureDeclarationIdentity := declaration;
         architectureStaticBindings := bindings |} <>
    deriveArchitectureInstanceIdentity
      {| architectureInstanceKey := rightKey;
         architectureParentInstanceKey := parent;
         architectureDeclarationIdentity := declaration;
         architectureStaticBindings := bindings |}.
Proof.
  intros leftKey rightKey parent declaration bindings Hneq Heq.
  apply Hneq.
  exact (f_equal identityInstanceKey Heq).
Qed.

Theorem changed_static_binding_preserves_occurrence_key :
  forall (occurrence : InstanceKey)
         (parent : option InstanceKey)
         (declaration : DeclarationIdentity)
         (oldBindings newBindings : nat),
    identityInstanceKey
      (deriveArchitectureInstanceIdentity
        {| architectureInstanceKey := occurrence;
           architectureParentInstanceKey := parent;
           architectureDeclarationIdentity := declaration;
           architectureStaticBindings := oldBindings |}) =
    identityInstanceKey
      (deriveArchitectureInstanceIdentity
        {| architectureInstanceKey := occurrence;
           architectureParentInstanceKey := parent;
           architectureDeclarationIdentity := declaration;
           architectureStaticBindings := newBindings |}).
Proof.
  reflexivity.
Qed.

Theorem changed_static_binding_revises_instance_identity :
  forall (occurrence : InstanceKey)
         (parent : option InstanceKey)
         (declaration : DeclarationIdentity)
         (oldBindings newBindings : nat),
    oldBindings <> newBindings ->
    deriveArchitectureInstanceIdentity
      {| architectureInstanceKey := occurrence;
         architectureParentInstanceKey := parent;
         architectureDeclarationIdentity := declaration;
         architectureStaticBindings := oldBindings |} <>
    deriveArchitectureInstanceIdentity
      {| architectureInstanceKey := occurrence;
         architectureParentInstanceKey := parent;
         architectureDeclarationIdentity := declaration;
         architectureStaticBindings := newBindings |}.
Proof.
  intros occurrence parent declaration oldBindings newBindings Hneq Heq.
  apply Hneq.
  pose proof (f_equal identityInstanceRevision Heq) as Hrevision.
  exact (f_equal instanceRevisionBindings Hrevision).
Qed.

Record ExplicitArchitectureReference : Type := {
  explicitReferenceTarget : InstanceKey
}.

Definition resolveExplicitReference
  (reference : ExplicitArchitectureReference) : InstanceKey :=
  explicitReferenceTarget reference.

Theorem explicit_reference_shares_existing_occurrence :
  forall (target : InstanceKey),
    resolveExplicitReference
      {| explicitReferenceTarget := target |} = target.
Proof.
  reflexivity.
Qed.

Inductive ChildSlotDecision : Type :=
| ChildSlotAccepted
| ChildSlotDuplicate.

Definition decideChildSlotByFacts
  (slotFresh : bool) : ChildSlotDecision :=
  if slotFresh then ChildSlotAccepted else ChildSlotDuplicate.

Theorem duplicate_stable_slot_rejects :
  decideChildSlotByFacts false = ChildSlotDuplicate.
Proof.
  reflexivity.
Qed.

Inductive ArchitectureRequirementDecision : Type :=
| ArchitectureRequirementAccepted
| ArchitectureRequirementUnresolved
| ArchitectureRequirementMissingBindingTarget
| ArchitectureRequirementInterfaceMismatch.

(* A non-bound explicit disposition (static satisfaction, runtime binding,
   assumption, re-export, or deployment export) is already explicit at the
   architecture level. BoundTo additionally requires an existing target and,
   when an exact interface is required, a matching reflected interface fact. *)
Definition decideArchitectureRequirementByFacts
  (hasExplicitDisposition isBoundTo targetExists interfaceMatches : bool)
  : ArchitectureRequirementDecision :=
  if hasExplicitDisposition then
    if isBoundTo then
      if targetExists then
        if interfaceMatches
        then ArchitectureRequirementAccepted
        else ArchitectureRequirementInterfaceMismatch
      else ArchitectureRequirementMissingBindingTarget
    else ArchitectureRequirementAccepted
  else ArchitectureRequirementUnresolved.

Theorem no_ambient_binding_closes_unresolved_requirement :
  forall (isBoundTo targetExists interfaceMatches : bool),
    decideArchitectureRequirementByFacts
      false isBoundTo targetExists interfaceMatches =
    ArchitectureRequirementUnresolved.
Proof.
  reflexivity.
Qed.

Definition decideRootRequirementByFacts :=
  decideArchitectureRequirementByFacts.

Theorem root_requirement_has_no_magical_initial_binding :
  forall (isBoundTo targetExists interfaceMatches : bool),
    decideRootRequirementByFacts
      false isBoundTo targetExists interfaceMatches =
    ArchitectureRequirementUnresolved.
Proof.
  reflexivity.
Qed.

Theorem explicit_nonbinding_disposition_closes_requirement :
  forall (targetExists interfaceMatches : bool),
    decideArchitectureRequirementByFacts
      true false targetExists interfaceMatches =
    ArchitectureRequirementAccepted.
Proof.
  reflexivity.
Qed.

Theorem explicit_binding_to_missing_target_rejects :
  forall (interfaceMatches : bool),
    decideArchitectureRequirementByFacts
      true true false interfaceMatches =
    ArchitectureRequirementMissingBindingTarget.
Proof.
  reflexivity.
Qed.

Theorem explicit_binding_requires_exact_interface_when_reflected :
  decideArchitectureRequirementByFacts true true true false =
  ArchitectureRequirementInterfaceMismatch.
Proof.
  reflexivity.
Qed.

Theorem explicit_binding_with_matching_interface_accepts :
  decideArchitectureRequirementByFacts true true true true =
  ArchitectureRequirementAccepted.
Proof.
  reflexivity.
Qed.

Inductive ArchitectureReferenceDecision : Type :=
| ArchitectureReferenceAccepted
| ArchitectureReferenceUnknownTarget.

Definition decideArchitectureReferenceByFacts
  (targetExists : bool) : ArchitectureReferenceDecision :=
  if targetExists
  then ArchitectureReferenceAccepted
  else ArchitectureReferenceUnknownTarget.

Theorem explicit_sharing_target_must_exist :
  decideArchitectureReferenceByFacts false =
  ArchitectureReferenceUnknownTarget.
Proof.
  reflexivity.
Qed.

Theorem existing_explicit_sharing_target_accepts :
  decideArchitectureReferenceByFacts true =
  ArchitectureReferenceAccepted.
Proof.
  reflexivity.
Qed.
