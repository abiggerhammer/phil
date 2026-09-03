From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import DataSum.

(*
  PHIL-DATA-SUM-001 — executable implementation-refinement staging.

  Constructor/tag lookup, concrete payload metadata, actual Context operations,
  and branch packaging remain native Haskell responsibilities. This layer
  exposes fail-closed executable decisions over the exact facts those native
  operations establish.
*)

Inductive ConstructorSelectionDecision : Type :=
| ConstructorSelectionAcceptedDecision
| ConstructorSelectionUnknownDecision.

Definition decideConstructorSelectionByFact
  (constructorDeclared : bool) : ConstructorSelectionDecision :=
  if constructorDeclared then
    ConstructorSelectionAcceptedDecision
  else
    ConstructorSelectionUnknownDecision.

Theorem constructor_selection_decision_reflects_certified :
  forall constructors tag payload constructorDeclared,
    (constructorDeclared = true <->
      selectConstructorPayload tag constructors = Some payload) ->
    (decideConstructorSelectionByFact constructorDeclared =
       ConstructorSelectionAcceptedDecision <->
     selectConstructorPayload tag constructors = Some payload).
Proof.
  intros constructors tag payload constructorDeclared Hdeclared.
  destruct constructorDeclared; cbn.
  - split; intro H.
    + apply (proj1 Hdeclared). reflexivity.
    + reflexivity.
  - split; intro H.
    + discriminate.
    + pose proof ((proj2 Hdeclared) H) as Htrue.
      discriminate.
Qed.

Inductive SelectedPayloadRestorationDecision : Type :=
| SelectedPayloadRestorationAcceptedDecision
| SelectedPayloadAggregateDecision
| SelectedPayloadExactnessDecision.

Definition decideSelectedPayloadRestorationByFacts
  (aggregateConsumed payloadRestoredExact : bool)
  : SelectedPayloadRestorationDecision :=
  if aggregateConsumed then
    if payloadRestoredExact then
      SelectedPayloadRestorationAcceptedDecision
    else
      SelectedPayloadExactnessDecision
  else
    SelectedPayloadAggregateDecision.

Theorem selected_payload_restoration_accepts_iff_facts :
  forall aggregateConsumed payloadRestoredExact,
    decideSelectedPayloadRestorationByFacts
      aggregateConsumed payloadRestoredExact =
      SelectedPayloadRestorationAcceptedDecision <->
    aggregateConsumed = true /\ payloadRestoredExact = true.
Proof.
  intros aggregateConsumed payloadRestoredExact.
  destruct aggregateConsumed, payloadRestoredExact; cbn; intuition discriminate.
Qed.

Inductive ContinuingArmDecision : Type :=
| ContinuingArmAcceptedDecision
| ContinuingArmPayloadDispositionDecision.

Definition decideContinuingArmByFact
  (selectedPayloadAccounted : bool) : ContinuingArmDecision :=
  if selectedPayloadAccounted then
    ContinuingArmAcceptedDecision
  else
    ContinuingArmPayloadDispositionDecision.

Theorem continuing_arm_decision_reflects_certified :
  forall payload dispositions selectedPayloadAccounted,
    (selectedPayloadAccounted = true <->
      ContinuingArmAccepted payload dispositions) ->
    (decideContinuingArmByFact selectedPayloadAccounted =
       ContinuingArmAcceptedDecision <->
     ContinuingArmAccepted payload dispositions).
Proof.
  intros payload dispositions selectedPayloadAccounted Haccounted.
  destruct selectedPayloadAccounted; cbn.
  - split; intro H.
    + apply (proj1 Haccounted). reflexivity.
    + reflexivity.
  - split; intro H.
    + discriminate.
    + pose proof ((proj2 Haccounted) H) as Htrue.
      discriminate.
Qed.

Inductive BranchConvergenceDecision : Type :=
| BranchConvergenceAcceptedDecision
| BranchConvergenceHiddenStateDecision
| BranchConvergenceJoinDecision.

Definition decideBranchConvergenceByFacts
  (rawLinearShapesCompatible explicitCommonPackage ordinaryJoinAccepted : bool)
  : BranchConvergenceDecision :=
  if ordinaryJoinAccepted then
    if rawLinearShapesCompatible || explicitCommonPackage then
      BranchConvergenceAcceptedDecision
    else
      BranchConvergenceHiddenStateDecision
  else
    BranchConvergenceJoinDecision.

Theorem branch_convergence_accepts_iff_boolean_facts :
  forall rawLinearShapesCompatible explicitCommonPackage ordinaryJoinAccepted,
    decideBranchConvergenceByFacts
      rawLinearShapesCompatible explicitCommonPackage ordinaryJoinAccepted =
      BranchConvergenceAcceptedDecision <->
    ordinaryJoinAccepted = true /\
      (rawLinearShapesCompatible = true \/ explicitCommonPackage = true).
Proof.
  intros rawLinearShapesCompatible explicitCommonPackage ordinaryJoinAccepted.
  destruct rawLinearShapesCompatible,
           explicitCommonPackage,
           ordinaryJoinAccepted;
    cbn; intuition discriminate.
Qed.

Theorem hidden_branch_state_without_explicit_package_rejects :
  forall ordinaryJoinAccepted,
    decideBranchConvergenceByFacts false false ordinaryJoinAccepted <>
      BranchConvergenceAcceptedDecision.
Proof.
  intros ordinaryJoinAccepted Haccepted.
  destruct ordinaryJoinAccepted; discriminate.
Qed.

Theorem explicit_common_package_with_join_accepts :
  forall rawLinearShapesCompatible,
    decideBranchConvergenceByFacts rawLinearShapesCompatible true true =
      BranchConvergenceAcceptedDecision.
Proof.
  intros rawLinearShapesCompatible.
  destruct rawLinearShapesCompatible; reflexivity.
Qed.

Theorem compatible_raw_shape_with_join_accepts :
  forall explicitCommonPackage,
    decideBranchConvergenceByFacts true explicitCommonPackage true =
      BranchConvergenceAcceptedDecision.
Proof.
  intros explicitCommonPackage.
  reflexivity.
Qed.
