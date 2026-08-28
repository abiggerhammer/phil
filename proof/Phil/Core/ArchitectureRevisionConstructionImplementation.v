From Phil.Core Require Import ArchitectureIdentity.

(*
  PHIL-ARCH-ID-IMPL-001 — representation-neutral revision-construction plans.

  The Certified architecture identity model fixes which semantic coordinates
  determine DeclarationIdentity, scoped occurrence identity, and
  ArchitectureInstanceIdentity. Production currently realizes those coordinates
  as canonical SemanticForm/Text encodings.

  This layer deliberately does not serialize Text, SemanticForm, Map, Set, or
  concrete keys/revisions through Rocq. Instead it extracts typed construction
  plans whose fields are polymorphic. Production can instantiate those fields
  with its native values while the extracted kernel owns exactly which inputs
  participate in each revision construction and which revision namespace is
  selected. Concrete canonical encoding remains an explicit representation
  bridge for the later production-binding tranche.
*)

Inductive ArchitectureRevisionNamespace : Type :=
| InterfaceRevisionNamespace
| DefinitionRevisionNamespace
| ScopedInstanceKeyNamespace
| InstanceRevisionNamespace.

Record InterfaceRevisionPlan (Semantic : Type) : Type :=
  mkInterfaceRevisionPlan {
    interfaceRevisionPlanNamespace : ArchitectureRevisionNamespace;
    interfaceRevisionPlanSemantics : Semantic
  }.

Definition planInterfaceRevision {Semantic : Type}
  (interfaceSemantics : Semantic) : InterfaceRevisionPlan Semantic :=
  {| interfaceRevisionPlanNamespace := InterfaceRevisionNamespace;
     interfaceRevisionPlanSemantics := interfaceSemantics |}.

Record DefinitionRevisionPlan (Interface Body : Type) : Type :=
  mkDefinitionRevisionPlan {
    definitionRevisionPlanNamespace : ArchitectureRevisionNamespace;
    definitionRevisionPlanInterface : Interface;
    definitionRevisionPlanBody : Body
  }.

Definition planDefinitionRevision {Interface Body : Type}
  (interfaceRevision : Interface)
  (definitionSemantics : Body)
  : DefinitionRevisionPlan Interface Body :=
  {| definitionRevisionPlanNamespace := DefinitionRevisionNamespace;
     definitionRevisionPlanInterface := interfaceRevision;
     definitionRevisionPlanBody := definitionSemantics |}.

Record ScopedInstanceKeyPlan (Parent Slot : Type) : Type :=
  mkScopedInstanceKeyPlan {
    scopedInstanceKeyPlanNamespace : ArchitectureRevisionNamespace;
    scopedInstanceKeyPlanParent : Parent;
    scopedInstanceKeyPlanSlot : Slot
  }.

Definition planScopedInstanceKey {Parent Slot : Type}
  (parent : Parent)
  (slot : Slot)
  : ScopedInstanceKeyPlan Parent Slot :=
  {| scopedInstanceKeyPlanNamespace := ScopedInstanceKeyNamespace;
     scopedInstanceKeyPlanParent := parent;
     scopedInstanceKeyPlanSlot := slot |}.

Record InstanceRevisionPlan
  (Key Parent DeclarationKeyValue Interface DefinitionValue Bindings : Type)
  : Type :=
  mkInstanceRevisionPlan {
    instanceRevisionPlanNamespace : ArchitectureRevisionNamespace;
    instanceRevisionPlanKey : Key;
    instanceRevisionPlanParent : Parent;
    instanceRevisionPlanDeclarationKey : DeclarationKeyValue;
    instanceRevisionPlanInterface : Interface;
    instanceRevisionPlanDefinition : DefinitionValue;
    instanceRevisionPlanBindings : Bindings
  }.

Definition planInstanceRevision
  {Key Parent DeclarationKeyValue Interface DefinitionValue Bindings : Type}
  (instanceKey : Key)
  (parent : Parent)
  (declarationKeyValue : DeclarationKeyValue)
  (interfaceRevision : Interface)
  (definitionRevision : DefinitionValue)
  (bindings : Bindings)
  : InstanceRevisionPlan
      Key Parent DeclarationKeyValue Interface DefinitionValue Bindings :=
  {| instanceRevisionPlanNamespace := InstanceRevisionNamespace;
     instanceRevisionPlanKey := instanceKey;
     instanceRevisionPlanParent := parent;
     instanceRevisionPlanDeclarationKey := declarationKeyValue;
     instanceRevisionPlanInterface := interfaceRevision;
     instanceRevisionPlanDefinition := definitionRevision;
     instanceRevisionPlanBindings := bindings |}.

Theorem interface_revision_plan_corresponds_certified_identity :
  forall descriptor,
    let certifiedIdentity := deriveDeclarationIdentity descriptor in
    let plan := planInterfaceRevision
      (declarationInterfaceSemantics descriptor) in
    interfaceRevisionPlanNamespace plan = InterfaceRevisionNamespace /\
    interfaceRevisionPlanSemantics plan =
      identityInterfaceRevision certifiedIdentity.
Proof.
  intros [presentationName presentationModule key interfaceSemantics definitionSemantics].
  cbn.
  split; reflexivity.
Qed.

Theorem definition_revision_plan_corresponds_certified_identity :
  forall descriptor,
    let certifiedIdentity := deriveDeclarationIdentity descriptor in
    let certifiedDefinition := identityDefinitionRevision certifiedIdentity in
    let plan := planDefinitionRevision
      (identityInterfaceRevision certifiedIdentity)
      (declarationDefinitionSemantics descriptor) in
    definitionRevisionPlanNamespace plan = DefinitionRevisionNamespace /\
    definitionRevisionPlanInterface plan =
      definitionRevisionInterface certifiedDefinition /\
    definitionRevisionPlanBody plan =
      definitionRevisionBody certifiedDefinition.
Proof.
  intros [presentationName presentationModule key interfaceSemantics definitionSemantics].
  cbn.
  repeat split; reflexivity.
Qed.

Theorem scoped_instance_key_plan_corresponds_certified_identity :
  forall parent slot,
    let plan := planScopedInstanceKey parent slot in
    scopedInstanceKeyPlanNamespace plan = ScopedInstanceKeyNamespace /\
    scopedInstanceKeyPlanParent plan = parent /\
    scopedInstanceKeyPlanSlot plan = slot /\
    scopedInstanceKey parent slot = ScopedInstanceKey parent slot.
Proof.
  intros parent slot.
  cbn.
  repeat split; reflexivity.
Qed.

Theorem instance_revision_plan_corresponds_certified_identity :
  forall descriptor,
    let declarationIdentity := architectureDeclarationIdentity descriptor in
    let certifiedIdentity := deriveArchitectureInstanceIdentity descriptor in
    let certifiedRevision := identityInstanceRevision certifiedIdentity in
    let plan := planInstanceRevision
      (architectureInstanceKey descriptor)
      (architectureParentInstanceKey descriptor)
      (identityDeclarationKey declarationIdentity)
      (identityInterfaceRevision declarationIdentity)
      (identityDefinitionRevision declarationIdentity)
      (architectureStaticBindings descriptor) in
    instanceRevisionPlanNamespace plan = InstanceRevisionNamespace /\
    instanceRevisionPlanKey plan = instanceRevisionKey certifiedRevision /\
    instanceRevisionPlanParent plan = instanceRevisionParent certifiedRevision /\
    instanceRevisionPlanDeclarationKey plan =
      instanceRevisionDeclarationKey certifiedRevision /\
    instanceRevisionPlanInterface plan = instanceRevisionInterface certifiedRevision /\
    instanceRevisionPlanDefinition plan = instanceRevisionDefinition certifiedRevision /\
    instanceRevisionPlanBindings plan = instanceRevisionBindings certifiedRevision.
Proof.
  intros [instanceKey parent declarationIdentity bindings].
  destruct declarationIdentity as [declarationKeyValue interfaceRevision definitionRevision].
  cbn.
  repeat split; reflexivity.
Qed.

Theorem definition_body_difference_revises_construction_plan :
  forall (Interface Body : Type)
         (interfaceRevision : Interface)
         (oldBody newBody : Body),
    oldBody <> newBody ->
    planDefinitionRevision interfaceRevision oldBody <>
    planDefinitionRevision interfaceRevision newBody.
Proof.
  intros Interface Body interfaceRevision oldBody newBody Hneq Heq.
  apply Hneq.
  exact (f_equal definitionRevisionPlanBody Heq).
Qed.

Theorem scoped_parent_difference_revises_construction_plan :
  forall (Parent Slot : Type)
         (oldParent newParent : Parent)
         (slot : Slot),
    oldParent <> newParent ->
    planScopedInstanceKey oldParent slot <>
    planScopedInstanceKey newParent slot.
Proof.
  intros Parent Slot oldParent newParent slot Hneq Heq.
  apply Hneq.
  exact (f_equal scopedInstanceKeyPlanParent Heq).
Qed.

Theorem scoped_slot_difference_revises_construction_plan :
  forall (Parent Slot : Type)
         (parent : Parent)
         (oldSlot newSlot : Slot),
    oldSlot <> newSlot ->
    planScopedInstanceKey parent oldSlot <>
    planScopedInstanceKey parent newSlot.
Proof.
  intros Parent Slot parent oldSlot newSlot Hneq Heq.
  apply Hneq.
  exact (f_equal scopedInstanceKeyPlanSlot Heq).
Qed.

Theorem instance_binding_difference_revises_construction_plan :
  forall (Key Parent DeclarationKeyValue Interface DefinitionValue Bindings : Type)
         (instanceKey : Key)
         (parent : Parent)
         (declarationKeyValue : DeclarationKeyValue)
         (interfaceRevision : Interface)
         (definitionRevision : DefinitionValue)
         (oldBindings newBindings : Bindings),
    oldBindings <> newBindings ->
    planInstanceRevision
      instanceKey parent declarationKeyValue interfaceRevision definitionRevision oldBindings <>
    planInstanceRevision
      instanceKey parent declarationKeyValue interfaceRevision definitionRevision newBindings.
Proof.
  intros Key Parent DeclarationKeyValue Interface DefinitionValue Bindings
    instanceKey parent declarationKeyValue interfaceRevision definitionRevision
    oldBindings newBindings Hneq Heq.
  apply Hneq.
  exact (f_equal instanceRevisionPlanBindings Heq).
Qed.

Theorem instance_interface_difference_revises_construction_plan :
  forall (Key Parent DeclarationKeyValue Interface DefinitionValue Bindings : Type)
         (instanceKey : Key)
         (parent : Parent)
         (declarationKeyValue : DeclarationKeyValue)
         (oldInterface newInterface : Interface)
         (definitionRevision : DefinitionValue)
         (bindings : Bindings),
    oldInterface <> newInterface ->
    planInstanceRevision
      instanceKey parent declarationKeyValue oldInterface definitionRevision bindings <>
    planInstanceRevision
      instanceKey parent declarationKeyValue newInterface definitionRevision bindings.
Proof.
  intros Key Parent DeclarationKeyValue Interface DefinitionValue Bindings
    instanceKey parent declarationKeyValue oldInterface newInterface
    definitionRevision bindings Hneq Heq.
  apply Hneq.
  exact (f_equal instanceRevisionPlanInterface Heq).
Qed.
