From Stdlib Require Import Lists.List Arith.PeanoNat.

Import ListNotations.

From Phil.Core Require Import GenericInstantiation.

(*
  PHIL-GEN-ID-001 — generic semantic application identity and discharge lineage.

  This normalized model follows the implementation split in Phil.Core.Generic:
  an ordinary generic application is identified by declaration lineage, exact
  public interface revision, and the extensional key->semantic-argument mapping.
  Definition revision and accepted requirement-discharge evidence live in a
  separate discharge lineage.

  Concrete Haskell Map ordering/canonicalization, SemanticForm serialization,
  digest/collision assumptions, and the correspondence from architecture
  occurrence scoping to InstanceKey remain explicit trust boundaries.
*)

Definition SemanticArgument : Type := (nat * nat)%type.

Fixpoint lookupArgument
  (key : nat)
  (arguments : list SemanticArgument) : option nat :=
  match arguments with
  | [] => None
  | (argumentKey, value) :: rest =>
      if Nat.eqb key argumentKey
      then Some value
      else lookupArgument key rest
  end.

Definition argumentsEquivalent
  (left right : list SemanticArgument) : Prop :=
  forall key, lookupArgument key left = lookupArgument key right.

Definition argumentDomainValid (arguments : list SemanticArgument) : Prop :=
  NoDup (map fst arguments).

Record GenericApplicationIdentity : Type := mkApplication {
  applicationDeclarationKey : nat;
  applicationInterfaceRevision : nat;
  applicationSemanticArguments : list SemanticArgument
}.

Definition sameApplication
  (left right : GenericApplicationIdentity) : Prop :=
  applicationDeclarationKey left = applicationDeclarationKey right /\
  applicationInterfaceRevision left = applicationInterfaceRevision right /\
  argumentsEquivalent
    (applicationSemanticArguments left)
    (applicationSemanticArguments right).

Record GenericDischargeLineage : Type := mkDischargeLineage {
  lineageApplication : GenericApplicationIdentity;
  lineageDefinitionRevision : nat;
  lineageEvidenceIdentity : nat
}.

Record ArchitectureEmbedding : Type := mkArchitectureEmbedding {
  embeddingParent : nat;
  embeddingSlot : nat;
  embeddingApplication : GenericApplicationIdentity
}.

Theorem ordinary_generic_application_is_applicative :
  forall declaration interface arguments,
    sameApplication
      (mkApplication declaration interface arguments)
      (mkApplication declaration interface arguments).
Proof.
  intros declaration interface arguments.
  repeat split; reflexivity.
Qed.

Theorem two_distinct_argument_orders_are_equivalent :
  forall firstKey firstValue secondKey secondValue,
    firstKey <> secondKey ->
    argumentsEquivalent
      [(firstKey, firstValue); (secondKey, secondValue)]
      [(secondKey, secondValue); (firstKey, firstValue)].
Proof.
  intros firstKey firstValue secondKey secondValue Hdistinct key.
  simpl.
  destruct (Nat.eqb key firstKey) eqn:Hfirst;
  destruct (Nat.eqb key secondKey) eqn:Hsecond;
  try reflexivity.
  apply Nat.eqb_eq in Hfirst.
  apply Nat.eqb_eq in Hsecond.
  subst.
  contradiction.
Qed.

Theorem semantic_argument_order_is_nonsemantic :
  forall declaration interface firstKey firstValue secondKey secondValue,
    firstKey <> secondKey ->
    sameApplication
      (mkApplication declaration interface
        [(firstKey, firstValue); (secondKey, secondValue)])
      (mkApplication declaration interface
        [(secondKey, secondValue); (firstKey, firstValue)]).
Proof.
  intros declaration interface firstKey firstValue secondKey secondValue Hdistinct.
  repeat split; try reflexivity.
  apply two_distinct_argument_orders_are_equivalent.
  exact Hdistinct.
Qed.

Theorem duplicate_semantic_argument_keys_reject :
  forall key firstValue secondValue,
    ~ argumentDomainValid [(key, firstValue); (key, secondValue)].
Proof.
  intros key firstValue secondValue Hvalid.
  unfold argumentDomainValid in Hvalid.
  simpl in Hvalid.
  inversion Hvalid as [|head tail Hnotin Htail].
  apply Hnotin.
  simpl.
  auto.
Qed.

Theorem declaration_key_is_part_of_application_identity :
  forall leftDeclaration rightDeclaration interface arguments,
    leftDeclaration <> rightDeclaration ->
    ~ sameApplication
        (mkApplication leftDeclaration interface arguments)
        (mkApplication rightDeclaration interface arguments).
Proof.
  intros leftDeclaration rightDeclaration interface arguments Hneq Hsame.
  destruct Hsame as [Hdeclaration _].
  apply Hneq.
  exact Hdeclaration.
Qed.

Theorem interface_revision_is_part_of_application_identity :
  forall declaration leftInterface rightInterface arguments,
    leftInterface <> rightInterface ->
    ~ sameApplication
        (mkApplication declaration leftInterface arguments)
        (mkApplication declaration rightInterface arguments).
Proof.
  intros declaration leftInterface rightInterface arguments Hneq Hsame.
  destruct Hsame as [_ [Hinterface _]].
  apply Hneq.
  exact Hinterface.
Qed.

Theorem identity_bearing_semantic_argument_changes_application :
  forall declaration interface key leftValue rightValue,
    leftValue <> rightValue ->
    ~ sameApplication
        (mkApplication declaration interface [(key, leftValue)])
        (mkApplication declaration interface [(key, rightValue)]).
Proof.
  intros declaration interface key leftValue rightValue Hneq Hsame.
  destruct Hsame as [_ [_ Harguments]].
  specialize (Harguments key).
  simpl in Harguments.
  rewrite Nat.eqb_refl in Harguments.
  inversion Harguments.
  contradiction.
Qed.

Theorem discharge_evidence_replacement_preserves_semantic_application :
  forall application definition evidenceLeft evidenceRight,
    lineageApplication
      (mkDischargeLineage application definition evidenceLeft) =
    lineageApplication
      (mkDischargeLineage application definition evidenceRight).
Proof.
  reflexivity.
Qed.

Theorem discharge_evidence_replacement_changes_lineage :
  forall application definition evidenceLeft evidenceRight,
    evidenceLeft <> evidenceRight ->
    mkDischargeLineage application definition evidenceLeft <>
    mkDischargeLineage application definition evidenceRight.
Proof.
  intros application definition evidenceLeft evidenceRight Hneq Hequal.
  inversion Hequal.
  contradiction.
Qed.

Theorem definition_revision_is_not_semantic_application_identity :
  forall application definitionLeft definitionRight evidence,
    lineageApplication
      (mkDischargeLineage application definitionLeft evidence) =
    lineageApplication
      (mkDischargeLineage application definitionRight evidence).
Proof.
  reflexivity.
Qed.

Theorem definition_revision_change_changes_discharge_lineage :
  forall application definitionLeft definitionRight evidence,
    definitionLeft <> definitionRight ->
    mkDischargeLineage application definitionLeft evidence <>
    mkDischargeLineage application definitionRight evidence.
Proof.
  intros application definitionLeft definitionRight evidence Hneq Hequal.
  inversion Hequal.
  contradiction.
Qed.

Theorem discharge_metadata_is_downstream_of_application_identity :
  forall application definitionLeft definitionRight evidenceLeft evidenceRight,
    lineageApplication
      (mkDischargeLineage application definitionLeft evidenceLeft) = application /\
    lineageApplication
      (mkDischargeLineage application definitionRight evidenceRight) = application.
Proof.
  intros.
  split; reflexivity.
Qed.

Theorem equal_application_at_distinct_occurrence_slots_remains_generative :
  forall parent firstSlot secondSlot application,
    firstSlot <> secondSlot ->
    mkArchitectureEmbedding parent firstSlot application <>
    mkArchitectureEmbedding parent secondSlot application.
Proof.
  intros parent firstSlot secondSlot application Hneq Hequal.
  inversion Hequal.
  contradiction.
Qed.
