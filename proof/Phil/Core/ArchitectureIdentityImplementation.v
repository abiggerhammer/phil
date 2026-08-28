From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import ArchitectureIdentity.

(*
  PHIL-ARCH-ID-IMPL-001 — executable equality seams for the Certified
  architecture identity model.

  Rich production keys, revisions, SemanticForm values, and canonical Text
  encodings remain outside this normalized proof model.  The executable kernel
  consumes only primitive equality facts supplied by the production
  representation layer.
*)

Record DeclarationIdentityEqualityFacts : Type :=
  mkDeclarationIdentityEqualityFacts {
    declarationIdentityKeyMatches : bool;
    declarationIdentityInterfaceMatches : bool;
    declarationIdentityDefinitionMatches : bool
  }.

Definition declarationIdentityFactsb
  (facts : DeclarationIdentityEqualityFacts) : bool :=
  andb
    (declarationIdentityKeyMatches facts)
    (andb
      (declarationIdentityInterfaceMatches facts)
      (declarationIdentityDefinitionMatches facts)).

Inductive DeclarationIdentityEqualityDecision : Type :=
| DeclarationIdentityEqual
| DeclarationIdentityDifferent.

Definition decideDeclarationIdentityEquality
  (facts : DeclarationIdentityEqualityFacts)
  : DeclarationIdentityEqualityDecision :=
  if declarationIdentityFactsb facts
  then DeclarationIdentityEqual
  else DeclarationIdentityDifferent.

Record InterfaceValidityScopeEqualityFacts : Type :=
  mkInterfaceValidityScopeEqualityFacts {
    interfaceValidityKeyMatches : bool;
    interfaceValidityRevisionMatches : bool
  }.

Definition interfaceValidityScopeFactsb
  (facts : InterfaceValidityScopeEqualityFacts) : bool :=
  andb
    (interfaceValidityKeyMatches facts)
    (interfaceValidityRevisionMatches facts).

Inductive InterfaceValidityScopeEqualityDecision : Type :=
| InterfaceValidityScopeEqual
| InterfaceValidityScopeDifferent.

Definition decideInterfaceValidityScopeEquality
  (facts : InterfaceValidityScopeEqualityFacts)
  : InterfaceValidityScopeEqualityDecision :=
  if interfaceValidityScopeFactsb facts
  then InterfaceValidityScopeEqual
  else InterfaceValidityScopeDifferent.

Record ArchitectureInstanceIdentityEqualityFacts : Type :=
  mkArchitectureInstanceIdentityEqualityFacts {
    architectureInstanceKeyMatches : bool;
    architectureInstanceRevisionMatches : bool
  }.

Definition architectureInstanceIdentityFactsb
  (facts : ArchitectureInstanceIdentityEqualityFacts) : bool :=
  andb
    (architectureInstanceKeyMatches facts)
    (architectureInstanceRevisionMatches facts).

Inductive ArchitectureInstanceIdentityEqualityDecision : Type :=
| ArchitectureInstanceIdentityEqual
| ArchitectureInstanceIdentityDifferent.

Definition decideArchitectureInstanceIdentityEquality
  (facts : ArchitectureInstanceIdentityEqualityFacts)
  : ArchitectureInstanceIdentityEqualityDecision :=
  if architectureInstanceIdentityFactsb facts
  then ArchitectureInstanceIdentityEqual
  else ArchitectureInstanceIdentityDifferent.

Definition sameDeclarationIdentity
  (left right : DeclarationIdentity) : Prop :=
  identityDeclarationKey left = identityDeclarationKey right /\
  identityInterfaceRevision left = identityInterfaceRevision right /\
  identityDefinitionRevision left = identityDefinitionRevision right.

Definition sameArchitectureInstanceIdentity
  (left right : ArchitectureInstanceIdentity) : Prop :=
  identityInstanceKey left = identityInstanceKey right /\
  identityInstanceRevision left = identityInstanceRevision right.

Theorem declaration_identity_factsb_true_iff :
  forall
    (left right : DeclarationIdentity)
    (keyMatches interfaceMatches definitionMatches : bool),
    (keyMatches = true <->
      identityDeclarationKey left = identityDeclarationKey right) ->
    (interfaceMatches = true <->
      identityInterfaceRevision left = identityInterfaceRevision right) ->
    (definitionMatches = true <->
      identityDefinitionRevision left = identityDefinitionRevision right) ->
    declarationIdentityFactsb
      (mkDeclarationIdentityEqualityFacts
        keyMatches interfaceMatches definitionMatches) = true <->
    sameDeclarationIdentity left right.
Proof.
  intros left right keyMatches interfaceMatches definitionMatches
    Hkey Hinterface Hdefinition.
  split.
  - intro Hfacts.
    unfold declarationIdentityFactsb in Hfacts.
    apply andb_true_iff in Hfacts.
    destruct Hfacts as [HkeyTrue Hrest].
    apply andb_true_iff in Hrest.
    destruct Hrest as [HinterfaceTrue HdefinitionTrue].
    unfold sameDeclarationIdentity.
    split.
    + apply (proj1 Hkey).
      exact HkeyTrue.
    + split.
      * apply (proj1 Hinterface).
        exact HinterfaceTrue.
      * apply (proj1 Hdefinition).
        exact HdefinitionTrue.
  - intro Hsame.
    unfold sameDeclarationIdentity in Hsame.
    destruct Hsame as [HkeyEqual [HinterfaceEqual HdefinitionEqual]].
    unfold declarationIdentityFactsb.
    apply andb_true_iff.
    split.
    + apply (proj2 Hkey).
      exact HkeyEqual.
    + apply andb_true_iff.
      split.
      * apply (proj2 Hinterface).
        exact HinterfaceEqual.
      * apply (proj2 Hdefinition).
        exact HdefinitionEqual.
Qed.

Theorem same_declaration_identity_iff_equal :
  forall left right,
    sameDeclarationIdentity left right <-> left = right.
Proof.
  intros [leftKey leftInterface leftDefinition]
    [rightKey rightInterface rightDefinition].
  unfold sameDeclarationIdentity.
  cbn.
  split.
  - intros [Hkey [Hinterface Hdefinition]].
    subst.
    reflexivity.
  - intro Heq.
    inversion Heq.
    repeat split; reflexivity.
Qed.

Theorem interface_validity_scope_factsb_true_iff :
  forall
    (left right : DeclarationIdentity)
    (keyMatches interfaceMatches : bool),
    (keyMatches = true <->
      identityDeclarationKey left = identityDeclarationKey right) ->
    (interfaceMatches = true <->
      identityInterfaceRevision left = identityInterfaceRevision right) ->
    interfaceValidityScopeFactsb
      (mkInterfaceValidityScopeEqualityFacts
        keyMatches interfaceMatches) = true <->
    interfaceValidityScope left = interfaceValidityScope right.
Proof.
  intros left right keyMatches interfaceMatches Hkey Hinterface.
  split.
  - intro Hfacts.
    unfold interfaceValidityScopeFactsb in Hfacts.
    apply andb_true_iff in Hfacts.
    destruct Hfacts as [HkeyTrue HinterfaceTrue].
    pose proof (proj1 Hkey HkeyTrue) as HkeyEqual.
    pose proof (proj1 Hinterface HinterfaceTrue) as HinterfaceEqual.
    unfold interfaceValidityScope, interfaceValidityDimension, interfaceValidityValue.
    rewrite HkeyEqual, HinterfaceEqual.
    reflexivity.
  - intro Hscope.
    unfold interfaceValidityScope, interfaceValidityDimension, interfaceValidityValue in Hscope.
    unfold interfaceValidityScopeFactsb.
    apply andb_true_iff.
    split.
    + apply (proj2 Hkey).
      exact (f_equal fst Hscope).
    + apply (proj2 Hinterface).
      exact (f_equal snd Hscope).
Qed.

Theorem architecture_instance_identity_factsb_true_iff :
  forall
    (left right : ArchitectureInstanceIdentity)
    (keyMatches revisionMatches : bool),
    (keyMatches = true <->
      identityInstanceKey left = identityInstanceKey right) ->
    (revisionMatches = true <->
      identityInstanceRevision left = identityInstanceRevision right) ->
    architectureInstanceIdentityFactsb
      (mkArchitectureInstanceIdentityEqualityFacts
        keyMatches revisionMatches) = true <->
    sameArchitectureInstanceIdentity left right.
Proof.
  intros left right keyMatches revisionMatches Hkey Hrevision.
  split.
  - intro Hfacts.
    unfold architectureInstanceIdentityFactsb in Hfacts.
    apply andb_true_iff in Hfacts.
    destruct Hfacts as [HkeyTrue HrevisionTrue].
    unfold sameArchitectureInstanceIdentity.
    split.
    + apply (proj1 Hkey).
      exact HkeyTrue.
    + apply (proj1 Hrevision).
      exact HrevisionTrue.
  - intro Hsame.
    unfold sameArchitectureInstanceIdentity in Hsame.
    destruct Hsame as [HkeyEqual HrevisionEqual].
    unfold architectureInstanceIdentityFactsb.
    apply andb_true_iff.
    split.
    + apply (proj2 Hkey).
      exact HkeyEqual.
    + apply (proj2 Hrevision).
      exact HrevisionEqual.
Qed.

Theorem same_architecture_instance_identity_iff_equal :
  forall left right,
    sameArchitectureInstanceIdentity left right <-> left = right.
Proof.
  intros [leftKey leftRevision] [rightKey rightRevision].
  unfold sameArchitectureInstanceIdentity.
  cbn.
  split.
  - intros [Hkey Hrevision].
    subst.
    reflexivity.
  - intro Heq.
    inversion Heq.
    split; reflexivity.
Qed.

Theorem definition_difference_rejects_declaration_identity_equality :
  forall keyMatches interfaceMatches,
    declarationIdentityFactsb
      (mkDeclarationIdentityEqualityFacts
        keyMatches interfaceMatches false) = false.
Proof.
  intros keyMatches interfaceMatches.
  destruct keyMatches; destruct interfaceMatches; reflexivity.
Qed.

Theorem definition_difference_preserves_interface_validity_scope_decision :
  interfaceValidityScopeFactsb
    (mkInterfaceValidityScopeEqualityFacts true true) = true.
Proof.
  reflexivity.
Qed.

Theorem interface_difference_rejects_interface_validity_scope_equality :
  forall keyMatches,
    interfaceValidityScopeFactsb
      (mkInterfaceValidityScopeEqualityFacts keyMatches false) = false.
Proof.
  intros keyMatches.
  destruct keyMatches; reflexivity.
Qed.

Theorem instance_revision_difference_rejects_instance_identity_equality :
  forall keyMatches,
    architectureInstanceIdentityFactsb
      (mkArchitectureInstanceIdentityEqualityFacts keyMatches false) = false.
Proof.
  intros keyMatches.
  destruct keyMatches; reflexivity.
Qed.
