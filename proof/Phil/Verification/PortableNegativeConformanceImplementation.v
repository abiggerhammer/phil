From Stdlib Require Import Bool.Bool.

From Phil.Verification Require Import PortableNegativeConformance.

Inductive PortableNegativeDecision : Type :=
| PortableNegativeAccepted
| PortableNegativeRejected.

Definition portableNegativeFactsb
  (stableIdentity authorityResolved environmentMaterialized executionRejected
   classExact layerExact : bool) : bool :=
  stableIdentity &&
  authorityResolved &&
  environmentMaterialized &&
  executionRejected &&
  classExact &&
  layerExact.

Definition decidePortableNegative
  (stableIdentity authorityResolved environmentMaterialized executionRejected
   classExact layerExact : bool) : PortableNegativeDecision :=
  if portableNegativeFactsb
      stableIdentity authorityResolved environmentMaterialized executionRejected
      classExact layerExact
  then PortableNegativeAccepted
  else PortableNegativeRejected.

Theorem exact_portable_negative_accepts :
  decidePortableNegative true true true true true true =
    PortableNegativeAccepted.
Proof.
  reflexivity.
Qed.

Theorem missing_identity_or_authority_rejects :
  decidePortableNegative false true true true true true =
      PortableNegativeRejected /\
  decidePortableNegative true false true true true true =
      PortableNegativeRejected.
Proof.
  split; reflexivity.
Qed.

Theorem unmaterialized_environment_or_success_rejects :
  decidePortableNegative true true false true true true =
      PortableNegativeRejected /\
  decidePortableNegative true true true false true true =
      PortableNegativeRejected.
Proof.
  split; reflexivity.
Qed.

Theorem wrong_class_or_layer_rejects :
  decidePortableNegative true true true true false true =
      PortableNegativeRejected /\
  decidePortableNegative true true true true true false =
      PortableNegativeRejected.
Proof.
  split; reflexivity.
Qed.
