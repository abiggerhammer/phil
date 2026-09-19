From Stdlib Require Import Arith.PeanoNat.

From Phil.Surface Require Import SystemsProjection.
From Phil.LLVM Require Import Preservation.

(*
  PHIL-P1-REVIEW-R01 — target identity namespace separation.

  The repair requires three semantically distinct target identity classes:
  source-derived values, compiler-synthetic values, and block labels.  Their
  normalized target identities are tagged by namespace before rendering, so
  distinct namespaces cannot collide even when their local payloads have the
  same spelling/index.

  This aggregate proof composes that namespace invariant with the existing
  PHIL-SURF-SYS-PROJ-001 exact source-value identity preservation boundary and
  PHIL-LLVM-PRESERVE-001 conservative LLVM projection verification.

  Concrete Text prefixes/escaping, Systems ValueId/BlockId representation,
  LLVM textual rendering, and GHC/runtime correctness remain implementation
  correspondence boundaries exercised by the permanent R01 regression.
*)

Inductive TargetIdentityNamespace : Type :=
| SourceValueNamespace
| SyntheticValueNamespace
| BlockLabelNamespace.

Record TargetIdentity : Type := mkTargetIdentity {
  targetIdentityNamespace : TargetIdentityNamespace;
  targetIdentityLocal : nat
}.

Definition sourceTargetIdentity (local : nat) : TargetIdentity :=
  mkTargetIdentity SourceValueNamespace local.

Definition syntheticTargetIdentity (local : nat) : TargetIdentity :=
  mkTargetIdentity SyntheticValueNamespace local.

Definition blockTargetIdentity (local : nat) : TargetIdentity :=
  mkTargetIdentity BlockLabelNamespace local.

Theorem source_target_identity_is_injective :
  forall left right,
    sourceTargetIdentity left = sourceTargetIdentity right ->
    left = right.
Proof.
  intros left right Heq.
  inversion Heq.
  reflexivity.
Qed.

Theorem synthetic_target_identity_is_injective :
  forall left right,
    syntheticTargetIdentity left = syntheticTargetIdentity right ->
    left = right.
Proof.
  intros left right Heq.
  inversion Heq.
  reflexivity.
Qed.

Theorem block_target_identity_is_injective :
  forall left right,
    blockTargetIdentity left = blockTargetIdentity right ->
    left = right.
Proof.
  intros left right Heq.
  inversion Heq.
  reflexivity.
Qed.

Theorem source_and_synthetic_target_identities_are_disjoint :
  forall sourceLocal syntheticLocal,
    sourceTargetIdentity sourceLocal <>
      syntheticTargetIdentity syntheticLocal.
Proof.
  intros sourceLocal syntheticLocal Heq.
  discriminate Heq.
Qed.

Theorem source_value_and_block_target_identities_are_disjoint :
  forall sourceLocal blockLocal,
    sourceTargetIdentity sourceLocal <>
      blockTargetIdentity blockLocal.
Proof.
  intros sourceLocal blockLocal Heq.
  discriminate Heq.
Qed.

Theorem synthetic_value_and_block_target_identities_are_disjoint :
  forall syntheticLocal blockLocal,
    syntheticTargetIdentity syntheticLocal <>
      blockTargetIdentity blockLocal.
Proof.
  intros syntheticLocal blockLocal Heq.
  discriminate Heq.
Qed.

Definition R01TranslationContextValid
  (source : SystemsProjection.SurfaceScalarProjectionModel)
  (systems : SystemsProjection.SystemsScalarProjectionModel)
  (llvm : Preservation.LLVMPreservationModel) : Prop :=
  SystemsProjection.SurfaceSystemsProjectionSuccess source systems /\
  Preservation.LLVMPreservationVerificationSuccess llvm.

Theorem review_r01_surface_alias_preserves_exact_systems_value_identity :
  forall source systems llvm alias sourceBinding,
    R01TranslationContextValid source systems llvm ->
    SystemsProjection.projectionAliasOf source alias = Some sourceBinding ->
    exists value,
      SystemsProjection.projectionBindingValue source sourceBinding = Some value /\
      SystemsProjection.projectionBindingValue source alias = Some value.
Proof.
  intros source systems llvm alias sourceBinding Hvalid Halias.
  destruct Hvalid as [Hprojection _].
  eapply SystemsProjection.verified_surface_alias_reuses_value_identity.
  - exact Hprojection.
  - exact Halias.
Qed.

Theorem review_r01_llvm_projection_is_independently_verified :
  forall source systems llvm block,
    R01TranslationContextValid source systems llvm ->
    Preservation.preservationExpectedOrdinaryOps llvm block =
      Preservation.preservationActualOrdinaryOps llvm block /\
    Preservation.preservationExpectedOrdinaryTerminator llvm block =
      Preservation.preservationActualOrdinaryTerminator llvm block.
Proof.
  intros source systems llvm block Hvalid.
  destruct Hvalid as [_ Hllvm].
  eapply Preservation.verified_llvm_matches_conservative_ordinary_projection.
  exact Hllvm.
Qed.

Theorem review_r01_source_identity_cannot_collide_with_compiler_namespaces :
  forall sourceLocal syntheticLocal blockLocal,
    sourceTargetIdentity sourceLocal <>
      syntheticTargetIdentity syntheticLocal /\
    sourceTargetIdentity sourceLocal <>
      blockTargetIdentity blockLocal.
Proof.
  intros sourceLocal syntheticLocal blockLocal.
  split.
  - apply source_and_synthetic_target_identities_are_disjoint.
  - apply source_value_and_block_target_identities_are_disjoint.
Qed.

Theorem review_r01_all_target_identity_classes_are_pairwise_disjoint :
  forall sourceLocal syntheticLocal blockLocal,
    sourceTargetIdentity sourceLocal <>
      syntheticTargetIdentity syntheticLocal /\
    sourceTargetIdentity sourceLocal <>
      blockTargetIdentity blockLocal /\
    syntheticTargetIdentity syntheticLocal <>
      blockTargetIdentity blockLocal.
Proof.
  intros sourceLocal syntheticLocal blockLocal.
  split.
  - apply source_and_synthetic_target_identities_are_disjoint.
  - split.
    + apply source_value_and_block_target_identities_are_disjoint.
    + apply synthetic_value_and_block_target_identities_are_disjoint.
Qed.
