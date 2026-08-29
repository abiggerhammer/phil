From Stdlib Require Import Arith.PeanoNat.

(*
  PHIL-DATA-ID-001 — nominal data identity, transparent aliases, and
  non-inference of semantic/representation operations.

  PHIL-ARCH-ID-001 supplies the stable declaration-key principle. This file
  treats that key abstractly as a nat and proves the data-specific layer:
  equal shape does not collapse distinct nominal keys, transparent aliases
  erase only to their exact target, and operation authority is a separate
  explicit contract rather than a consequence of shape or identity.
*)

Inductive DataTypeRef : Type :=
| NominalType : nat -> nat -> DataTypeRef
| TransparentAlias : nat -> DataTypeRef -> DataTypeRef.

(* The second NominalType argument is checked data shape. Identity is nominal. *)
Fixpoint resolveDataType (ref : DataTypeRef) : nat :=
  match ref with
  | NominalType nominalKey _ => nominalKey
  | TransparentAlias _ target => resolveDataType target
  end.

Definition DefinitionallyEqualDataType
  (left right : DataTypeRef) : Prop :=
  resolveDataType left = resolveDataType right.

Theorem nominal_type_equals_itself :
  forall nominalKey shape,
    DefinitionallyEqualDataType
      (NominalType nominalKey shape)
      (NominalType nominalKey shape).
Proof.
  intros nominalKey shape.
  reflexivity.
Qed.

(* Equal structure cannot collapse distinct nominal declarations. *)
Theorem equal_shape_distinct_nominal_keys_remain_distinct :
  forall leftKey rightKey shape,
    leftKey <> rightKey ->
    ~ DefinitionallyEqualDataType
        (NominalType leftKey shape)
        (NominalType rightKey shape).
Proof.
  intros leftKey rightKey shape Hdistinct.
  unfold DefinitionallyEqualDataType.
  simpl.
  exact Hdistinct.
Qed.

(* Transparent aliases erase to exactly the identity of their target. *)
Theorem transparent_alias_equals_exact_target :
  forall aliasName target,
    DefinitionallyEqualDataType
      (TransparentAlias aliasName target)
      target.
Proof.
  intros aliasName target.
  reflexivity.
Qed.

Theorem transparent_alias_chain_resolves_transitively :
  forall outerName innerName target,
    DefinitionallyEqualDataType
      (TransparentAlias outerName (TransparentAlias innerName target))
      target.
Proof.
  intros outerName innerName target.
  reflexivity.
Qed.

(* Alias presentation names themselves create no new nominal identity. *)
Theorem transparent_alias_name_is_nonsemantic :
  forall firstName secondName target,
    DefinitionallyEqualDataType
      (TransparentAlias firstName target)
      (TransparentAlias secondName target).
Proof.
  intros firstName secondName target.
  reflexivity.
Qed.

Inductive DataOperation : Type :=
| OpEquality
| OpOrdering
| OpHashing
| OpClone
| OpDefault
| OpSerialization
| OpDeserialization
| OpMemcpySafety
| OpABICompatibility.

Definition OperationContract : Type := DataOperation -> Prop.

Definition emptyOperationContract : OperationContract :=
  fun _ => False.

Definition grantOperation
  (granted : DataOperation)
  (contract : OperationContract) : OperationContract :=
  fun candidate => candidate = granted \/ contract candidate.

Definition permitsOperation
  (contract : OperationContract)
  (operation : DataOperation) : Prop :=
  contract operation.

(* Shape/identity alone confers none of the DATA-011 operations. *)
Theorem empty_operation_contract_permits_nothing :
  forall operation,
    ~ permitsOperation emptyOperationContract operation.
Proof.
  intros operation Hpermit.
  unfold permitsOperation, emptyOperationContract in Hpermit.
  exact Hpermit.
Qed.

Theorem data_shape_grants_no_automatic_operation :
  forall nominalKey shape operation,
    ~ permitsOperation emptyOperationContract operation.
Proof.
  intros nominalKey shape operation.
  apply empty_operation_contract_permits_nothing.
Qed.

(* Even definitional type equality is not itself an operation contract. *)
Theorem definitional_identity_does_not_grant_operation :
  forall left right operation,
    DefinitionallyEqualDataType left right ->
    ~ permitsOperation emptyOperationContract operation.
Proof.
  intros left right operation Hequal.
  apply empty_operation_contract_permits_nothing.
Qed.

Theorem grant_operation_exact :
  forall granted contract candidate,
    permitsOperation (grantOperation granted contract) candidate <->
    candidate = granted \/ permitsOperation contract candidate.
Proof.
  reflexivity.
Qed.

(* An explicit grant does not imply any distinct semantic/representation grant. *)
Theorem explicit_grant_does_not_imply_distinct_operation :
  forall granted other contract,
    granted <> other ->
    ~ permitsOperation contract other ->
    ~ permitsOperation (grantOperation granted contract) other.
Proof.
  intros granted other contract Hdistinct Hnot Hpermit.
  unfold permitsOperation, grantOperation in Hpermit.
  destruct Hpermit as [Heq | Hold].
  - apply Hdistinct.
    symmetry.
    exact Heq.
  - apply Hnot.
    exact Hold.
Qed.

Corollary explicit_equality_does_not_imply_hashing :
  ~ permitsOperation
      (grantOperation OpEquality emptyOperationContract)
      OpHashing.
Proof.
  eapply explicit_grant_does_not_imply_distinct_operation.
  - discriminate.
  - apply empty_operation_contract_permits_nothing.
Qed.

Corollary explicit_serialization_does_not_imply_abi_compatibility :
  ~ permitsOperation
      (grantOperation OpSerialization emptyOperationContract)
      OpABICompatibility.
Proof.
  eapply explicit_grant_does_not_imply_distinct_operation.
  - discriminate.
  - apply empty_operation_contract_permits_nothing.
Qed.
