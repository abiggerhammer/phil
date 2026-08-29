From Stdlib Require Import Lists.List Arith.PeanoNat.
Import ListNotations.

From Phil.Core Require Import Syntax Context ContextJoin DataMode DataElimination.

(*
  PHIL-DATA-SUM-001 — resource-bearing sums and branch-dependent state.

  This proof composes the already Certified aggregate-mode, elimination, and
  resource-join semantics.  The sum-specific layer is constructor-local
  payload precision plus the fact that reconvergence cannot synthesize hidden
  branch-dependent linear ownership.
*)

(* The whole sum is at least as restrictive as every owned payload mode of
   every constructor. *)
Theorem whole_sum_mode_bounds_every_constructor_payload :
  forall constructors payloadModes fieldMode,
    In payloadModes constructors ->
    In fieldMode payloadModes ->
    modeLe fieldMode (deriveSumMode constructors).
Proof.
  intros constructors payloadModes fieldMode Hconstructor Hfield.
  eapply sum_mode_bounds_every_payload.
  - exact Hconstructor.
  - exact Hfield.
Qed.

(* Pattern matching recovers exactly the selected constructor payload rather
   than the conservative union of all possible payloads. *)
Record SumConstructor : Type := mkSumConstructor {
  sumConstructorTag : nat;
  sumConstructorPayload : list DataField
}.

Fixpoint lookupConstructor
  (tag : nat) (constructors : list SumConstructor) : option SumConstructor :=
  match constructors with
  | [] => None
  | constructor :: rest =>
      if Nat.eqb tag (sumConstructorTag constructor)
      then Some constructor
      else lookupConstructor tag rest
  end.

Definition selectConstructorPayload
  (tag : nat) (constructors : list SumConstructor) : option (list DataField) :=
  match lookupConstructor tag constructors with
  | Some constructor => Some (sumConstructorPayload constructor)
  | None => None
  end.

Theorem selected_constructor_payload_is_exact :
  forall constructors tag constructor,
    lookupConstructor tag constructors = Some constructor ->
    selectConstructorPayload tag constructors =
      Some (sumConstructorPayload constructor).
Proof.
  intros constructors tag constructor Hlookup.
  unfold selectConstructorPayload.
  rewrite Hlookup.
  reflexivity.
Qed.

Theorem unknown_constructor_has_no_payload :
  forall constructors tag,
    lookupConstructor tag constructors = None ->
    selectConstructorPayload tag constructors = None.
Proof.
  intros constructors tag Hlookup.
  unfold selectConstructorPayload.
  rewrite Hlookup.
  reflexivity.
Qed.

(* A continuing arm uses the ordinary Certified elimination discipline for the
   selected constructor-local payload. *)
Definition ContinuingArmAccepted
  (payload : list DataField)
  (dispositions : nat -> option FieldDisposition) : Prop :=
  EliminationPlanAccepted payload dispositions.

Theorem continuing_arm_accounts_every_linear_payload :
  forall payload dispositions field,
    ContinuingArmAccepted payload dispositions ->
    In field payload ->
    dataFieldMode field = Linear ->
    dispositions (dataFieldKey field) = Some FieldBound.
Proof.
  intros payload dispositions field Haccepted Hin Hlinear.
  unfold ContinuingArmAccepted in Haccepted.
  eapply accepted_plan_binds_every_linear_field.
  - exact Haccepted.
  - exact Hin.
  - exact Hlinear.
Qed.

Theorem continuing_arm_with_unaccounted_linear_payload_rejects :
  forall payload dispositions field,
    In field payload ->
    dataFieldMode field = Linear ->
    dispositions (dataFieldKey field) <> Some FieldBound ->
    ~ ContinuingArmAccepted payload dispositions.
Proof.
  intros payload dispositions field Hin Hlinear Hmissing Haccepted.
  apply Hmissing.
  eapply continuing_arm_accounts_every_linear_payload.
  - exact Haccepted.
  - exact Hin.
  - exact Hlinear.
Qed.

(* Successful join preserves linear state extensionally across every
   predecessor.  Hence no hidden branch-dependent owner can be synthesized. *)
Theorem successful_join_linear_owner_was_present_on_every_branch :
  forall contexts joined name ty context,
    ContextJoinSuccess contexts joined ->
    linearBindings joined name = Some ty ->
    In context contexts ->
    linearBindings context name = Some ty.
Proof.
  intros contexts joined name ty context Hjoin Hjoined Hin.
  pose proof
    (context_join_linear_converges contexts joined context Hjoin Hin)
    as Hsame.
  unfold SameBindingMap in Hsame.
  specialize (Hsame name).
  rewrite Hjoined in Hsame.
  symmetry.
  exact Hsame.
Qed.

Theorem successful_join_does_not_synthesize_linear_owner :
  forall first rest joined name,
    ContextJoinSuccess (first :: rest) joined ->
    linearBindings first name = None ->
    linearBindings joined name = None.
Proof.
  intros first rest joined name Hjoin Hmissing.
  assert (Hin : In first (first :: rest)).
  { simpl. left. reflexivity. }
  pose proof
    (context_join_linear_converges (first :: rest) joined first Hjoin Hin)
    as Hsame.
  unfold SameBindingMap in Hsame.
  specialize (Hsame name).
  rewrite Hmissing in Hsame.
  exact Hsame.
Qed.

(* Raw branch-dependent linear shapes cannot satisfy the successful join
   relation when one predecessor owns a name that another predecessor lacks. *)
Theorem mismatched_linear_branch_shapes_cannot_join :
  forall left right name ty,
    linearBindings left name = Some ty ->
    linearBindings right name = None ->
    ~ exists joined, ContextJoinSuccess [left; right] joined.
Proof.
  intros left right name ty Hleft Hright [joined Hjoin].
  assert (HinLeft : In left [left; right]).
  { simpl. left. reflexivity. }
  assert (HinRight : In right [left; right]).
  { simpl. right. left. reflexivity. }
  pose proof
    (context_join_linear_converges [left; right] joined left Hjoin HinLeft)
    as HleftSame.
  pose proof
    (context_join_linear_converges [left; right] joined right Hjoin HinRight)
    as HrightSame.
  unfold SameBindingMap in HleftSame, HrightSame.
  specialize (HleftSame name).
  specialize (HrightSame name).
  rewrite Hleft in HleftSame.
  rewrite Hright in HrightSame.
  rewrite HleftSame in HrightSame.
  discriminate.
Qed.

(* Packaging each branch-local owner into the same explicit linear sum/state
   name makes the ownership shape common; successful ordinary join then
   preserves that explicit sum owner without reclassification. *)
Definition BranchPackagedAs
  (context : ResourceContext) (name : Name) (ty : Ty) : Prop :=
  linearBindings context name = Some ty.

Theorem explicit_common_sum_owner_is_preserved_by_join :
  forall left right joined name ty,
    ContextJoinSuccess [left; right] joined ->
    BranchPackagedAs left name ty ->
    BranchPackagedAs right name ty ->
    BranchPackagedAs joined name ty.
Proof.
  intros left right joined name ty Hjoin Hleft Hright.
  unfold BranchPackagedAs in *.
  assert (HinLeft : In left [left; right]).
  { simpl. left. reflexivity. }
  pose proof
    (context_join_linear_converges [left; right] joined left Hjoin HinLeft)
    as Hsame.
  unfold SameBindingMap in Hsame.
  specialize (Hsame name).
  rewrite Hleft in Hsame.
  exact Hsame.
Qed.
