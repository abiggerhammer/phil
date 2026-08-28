From Stdlib Require Import Arith.PeanoNat.

(* Representation-neutral Phase 1 architecture identity model.
   Concrete canonical serialization and hashing remain implementation boundaries. *)

Record DeclarationDescriptor : Type := {
  declarationPresentationName : nat;
  declarationPresentationModule : nat;
  declarationKey : nat;
  declarationInterfaceSemantics : nat;
  declarationDefinitionSemantics : nat
}.

Record DefinitionRevision : Type := {
  definitionRevisionInterface : nat;
  definitionRevisionBody : nat
}.

Record DeclarationIdentity : Type := {
  identityDeclarationKey : nat;
  identityInterfaceRevision : nat;
  identityDefinitionRevision : DefinitionRevision
}.

Definition deriveDeclarationIdentity
  (descriptor : DeclarationDescriptor) : DeclarationIdentity :=
  {| identityDeclarationKey := declarationKey descriptor;
     identityInterfaceRevision := declarationInterfaceSemantics descriptor;
     identityDefinitionRevision :=
       {| definitionRevisionInterface := declarationInterfaceSemantics descriptor;
          definitionRevisionBody := declarationDefinitionSemantics descriptor |} |}.

Definition interfaceValidityDimension
  (identity : DeclarationIdentity) : nat :=
  identityDeclarationKey identity.

Definition interfaceValidityValue
  (identity : DeclarationIdentity) : nat :=
  identityInterfaceRevision identity.

Definition interfaceValidityScope
  (identity : DeclarationIdentity) : nat * nat :=
  (interfaceValidityDimension identity, interfaceValidityValue identity).

Theorem presentation_change_preserves_declaration_identity :
  forall oldName oldModule newName newModule key interfaceSem definitionSem,
    deriveDeclarationIdentity
      {| declarationPresentationName := oldName;
         declarationPresentationModule := oldModule;
         declarationKey := key;
         declarationInterfaceSemantics := interfaceSem;
         declarationDefinitionSemantics := definitionSem |} =
    deriveDeclarationIdentity
      {| declarationPresentationName := newName;
         declarationPresentationModule := newModule;
         declarationKey := key;
         declarationInterfaceSemantics := interfaceSem;
         declarationDefinitionSemantics := definitionSem |}.
Proof.
  reflexivity.
Qed.

Theorem public_interface_change_preserves_declaration_key :
  forall name modulePath key oldInterface newInterface oldDefinition newDefinition,
    identityDeclarationKey
      (deriveDeclarationIdentity
        {| declarationPresentationName := name;
           declarationPresentationModule := modulePath;
           declarationKey := key;
           declarationInterfaceSemantics := oldInterface;
           declarationDefinitionSemantics := oldDefinition |}) =
    identityDeclarationKey
      (deriveDeclarationIdentity
        {| declarationPresentationName := name;
           declarationPresentationModule := modulePath;
           declarationKey := key;
           declarationInterfaceSemantics := newInterface;
           declarationDefinitionSemantics := newDefinition |}).
Proof.
  reflexivity.
Qed.

Theorem public_interface_change_revises_interface :
  forall name modulePath key oldInterface newInterface oldDefinition newDefinition,
    oldInterface <> newInterface ->
    identityInterfaceRevision
      (deriveDeclarationIdentity
        {| declarationPresentationName := name;
           declarationPresentationModule := modulePath;
           declarationKey := key;
           declarationInterfaceSemantics := oldInterface;
           declarationDefinitionSemantics := oldDefinition |}) <>
    identityInterfaceRevision
      (deriveDeclarationIdentity
        {| declarationPresentationName := name;
           declarationPresentationModule := modulePath;
           declarationKey := key;
           declarationInterfaceSemantics := newInterface;
           declarationDefinitionSemantics := newDefinition |}).
Proof.
  intros name modulePath key oldInterface newInterface oldDefinition newDefinition Hneq.
  cbn.
  exact Hneq.
Qed.

Theorem public_interface_change_revises_definition :
  forall name modulePath key oldInterface newInterface oldDefinition newDefinition,
    oldInterface <> newInterface ->
    identityDefinitionRevision
      (deriveDeclarationIdentity
        {| declarationPresentationName := name;
           declarationPresentationModule := modulePath;
           declarationKey := key;
           declarationInterfaceSemantics := oldInterface;
           declarationDefinitionSemantics := oldDefinition |}) <>
    identityDefinitionRevision
      (deriveDeclarationIdentity
        {| declarationPresentationName := name;
           declarationPresentationModule := modulePath;
           declarationKey := key;
           declarationInterfaceSemantics := newInterface;
           declarationDefinitionSemantics := newDefinition |}).
Proof.
  intros name modulePath key oldInterface newInterface oldDefinition newDefinition Hneq Heq.
  apply Hneq.
  exact (f_equal definitionRevisionInterface Heq).
Qed.

Theorem definition_replacement_preserves_interface :
  forall name modulePath key interfaceSem oldDefinition newDefinition,
    identityInterfaceRevision
      (deriveDeclarationIdentity
        {| declarationPresentationName := name;
           declarationPresentationModule := modulePath;
           declarationKey := key;
           declarationInterfaceSemantics := interfaceSem;
           declarationDefinitionSemantics := oldDefinition |}) =
    identityInterfaceRevision
      (deriveDeclarationIdentity
        {| declarationPresentationName := name;
           declarationPresentationModule := modulePath;
           declarationKey := key;
           declarationInterfaceSemantics := interfaceSem;
           declarationDefinitionSemantics := newDefinition |}).
Proof.
  reflexivity.
Qed.

Theorem definition_replacement_revises_definition :
  forall name modulePath key interfaceSem oldDefinition newDefinition,
    oldDefinition <> newDefinition ->
    identityDefinitionRevision
      (deriveDeclarationIdentity
        {| declarationPresentationName := name;
           declarationPresentationModule := modulePath;
           declarationKey := key;
           declarationInterfaceSemantics := interfaceSem;
           declarationDefinitionSemantics := oldDefinition |}) <>
    identityDefinitionRevision
      (deriveDeclarationIdentity
        {| declarationPresentationName := name;
           declarationPresentationModule := modulePath;
           declarationKey := key;
           declarationInterfaceSemantics := interfaceSem;
           declarationDefinitionSemantics := newDefinition |}).
Proof.
  intros name modulePath key interfaceSem oldDefinition newDefinition Hneq Heq.
  apply Hneq.
  exact (f_equal definitionRevisionBody Heq).
Qed.

Theorem presentation_change_preserves_interface_validity_scope :
  forall oldName oldModule newName newModule key interfaceSem definitionSem,
    interfaceValidityScope
      (deriveDeclarationIdentity
        {| declarationPresentationName := oldName;
           declarationPresentationModule := oldModule;
           declarationKey := key;
           declarationInterfaceSemantics := interfaceSem;
           declarationDefinitionSemantics := definitionSem |}) =
    interfaceValidityScope
      (deriveDeclarationIdentity
        {| declarationPresentationName := newName;
           declarationPresentationModule := newModule;
           declarationKey := key;
           declarationInterfaceSemantics := interfaceSem;
           declarationDefinitionSemantics := definitionSem |}).
Proof.
  reflexivity.
Qed.

Theorem definition_replacement_preserves_interface_validity_scope :
  forall name modulePath key interfaceSem oldDefinition newDefinition,
    interfaceValidityScope
      (deriveDeclarationIdentity
        {| declarationPresentationName := name;
           declarationPresentationModule := modulePath;
           declarationKey := key;
           declarationInterfaceSemantics := interfaceSem;
           declarationDefinitionSemantics := oldDefinition |}) =
    interfaceValidityScope
      (deriveDeclarationIdentity
        {| declarationPresentationName := name;
           declarationPresentationModule := modulePath;
           declarationKey := key;
           declarationInterfaceSemantics := interfaceSem;
           declarationDefinitionSemantics := newDefinition |}).
Proof.
  reflexivity.
Qed.

Theorem public_interface_change_revises_interface_validity_scope :
  forall name modulePath key oldInterface newInterface oldDefinition newDefinition,
    oldInterface <> newInterface ->
    interfaceValidityScope
      (deriveDeclarationIdentity
        {| declarationPresentationName := name;
           declarationPresentationModule := modulePath;
           declarationKey := key;
           declarationInterfaceSemantics := oldInterface;
           declarationDefinitionSemantics := oldDefinition |}) <>
    interfaceValidityScope
      (deriveDeclarationIdentity
        {| declarationPresentationName := name;
           declarationPresentationModule := modulePath;
           declarationKey := key;
           declarationInterfaceSemantics := newInterface;
           declarationDefinitionSemantics := newDefinition |}).
Proof.
  intros name modulePath key oldInterface newInterface oldDefinition newDefinition Hneq Heq.
  apply Hneq.
  exact (f_equal snd Heq).
Qed.

Inductive InstanceKey : Type :=
| RootInstanceKey : nat -> InstanceKey
| ScopedInstanceKey : InstanceKey -> nat -> InstanceKey.

Definition scopedInstanceKey
  (parent : InstanceKey)
  (slot : nat) : InstanceKey :=
  ScopedInstanceKey parent slot.

Record InstanceRevision : Type := {
  instanceRevisionKey : InstanceKey;
  instanceRevisionParent : option InstanceKey;
  instanceRevisionDeclarationKey : nat;
  instanceRevisionInterface : nat;
  instanceRevisionDefinition : DefinitionRevision;
  instanceRevisionBindings : nat
}.

Record ArchitectureInstanceDescriptor : Type := {
  architectureInstanceKey : InstanceKey;
  architectureParentInstanceKey : option InstanceKey;
  architectureDeclarationIdentity : DeclarationIdentity;
  architectureStaticBindings : nat
}.

Record ArchitectureInstanceIdentity : Type := {
  identityInstanceKey : InstanceKey;
  identityInstanceRevision : InstanceRevision
}.

Definition deriveArchitectureInstanceIdentity
  (descriptor : ArchitectureInstanceDescriptor) : ArchitectureInstanceIdentity :=
  let declarationIdentity := architectureDeclarationIdentity descriptor in
  {| identityInstanceKey := architectureInstanceKey descriptor;
     identityInstanceRevision :=
       {| instanceRevisionKey := architectureInstanceKey descriptor;
          instanceRevisionParent := architectureParentInstanceKey descriptor;
          instanceRevisionDeclarationKey := identityDeclarationKey declarationIdentity;
          instanceRevisionInterface := identityInterfaceRevision declarationIdentity;
          instanceRevisionDefinition := identityDefinitionRevision declarationIdentity;
          instanceRevisionBindings := architectureStaticBindings descriptor |} |}.

Theorem presentation_change_preserves_instance_identity :
  forall oldName oldModule newName newModule declarationKeyValue interfaceSem definitionSem
         occurrenceKey parentKey bindings,
    deriveArchitectureInstanceIdentity
      {| architectureInstanceKey := occurrenceKey;
         architectureParentInstanceKey := parentKey;
         architectureDeclarationIdentity :=
           deriveDeclarationIdentity
             {| declarationPresentationName := oldName;
                declarationPresentationModule := oldModule;
                declarationKey := declarationKeyValue;
                declarationInterfaceSemantics := interfaceSem;
                declarationDefinitionSemantics := definitionSem |};
         architectureStaticBindings := bindings |} =
    deriveArchitectureInstanceIdentity
      {| architectureInstanceKey := occurrenceKey;
         architectureParentInstanceKey := parentKey;
         architectureDeclarationIdentity :=
           deriveDeclarationIdentity
             {| declarationPresentationName := newName;
                declarationPresentationModule := newModule;
                declarationKey := declarationKeyValue;
                declarationInterfaceSemantics := interfaceSem;
                declarationDefinitionSemantics := definitionSem |};
         architectureStaticBindings := bindings |}.
Proof.
  reflexivity.
Qed.

Theorem unaffected_sibling_occurrence_ignores_parent_definition_revision :
  forall parentOccurrence slot childIdentity childBindings
         parentDefinitionBefore parentDefinitionAfter,
    deriveArchitectureInstanceIdentity
      {| architectureInstanceKey := scopedInstanceKey parentOccurrence slot;
         architectureParentInstanceKey := Some parentOccurrence;
         architectureDeclarationIdentity := childIdentity;
         architectureStaticBindings := childBindings |} =
    deriveArchitectureInstanceIdentity
      {| architectureInstanceKey := scopedInstanceKey parentOccurrence slot;
         architectureParentInstanceKey := Some parentOccurrence;
         architectureDeclarationIdentity := childIdentity;
         architectureStaticBindings := childBindings |}.
Proof.
  intros.
  reflexivity.
Qed.

Theorem sibling_edit_preserves_unaffected_child_key :
  forall parentOccurrence slot,
    scopedInstanceKey parentOccurrence slot = scopedInstanceKey parentOccurrence slot.
Proof.
  reflexivity.
Qed.

Theorem sibling_edit_preserves_unaffected_interface_validity_scope :
  forall childIdentity parentDefinitionBefore parentDefinitionAfter,
    interfaceValidityScope childIdentity = interfaceValidityScope childIdentity.
Proof.
  reflexivity.
Qed.
