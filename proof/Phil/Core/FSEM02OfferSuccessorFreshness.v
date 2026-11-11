From Stdlib Require Import Strings.String.
From Phil.Core Require Import
  Syntax Context SessionStep FSEM02ProtocolHeadProgression
  FSEM02BranchOutcomeSeparation.

(* NON-NORMATIVE FSEM-02. The native checked source/ProtocolContext tests
   separately establish admitted role projection, endpoint name identities,
   selected choice, and exact Haskell error constructors. This model is an
   extensional Context abstraction, not Haskell refinement or new authority. *)

Open Scope string_scope.

(* Existing bindings in ANY of the three structural maps obstruct a distinct
   successor after consumption of the unrelated predecessor. The active-loan
   set remains an independent premise, never silently discharged. *)
Theorem fsem02OccupiedUnrelatedSuccessorCannotContinue :
  forall endpoint successor continuation context,
    String.eqb successor endpoint = false ->
    bindingExists successor context = true ->
    continueEndpointResource endpoint successor continuation context = StepFailed.
Proof.
  intros endpoint successor continuation context Hdistinct Hoccupied.
  unfold continueEndpointResource.
  destruct (consumeLinear endpoint context) as [error | owned consumed]
    eqn:Hconsume.
  - reflexivity.
  - rewrite (String.eqb_sym endpoint successor), Hdistinct.
    pose proof
      (consumeLinear_success_exact endpoint context consumed owned Hconsume)
      as Hresources.
    destruct Hresources as [_ [_ [Hother [HU [HA _]]]]].
    unfold insertBinding, bindingExists, bindingPresent in *.
    rewrite HU, HA, (Hother successor Hdistinct).
    rewrite Hoccupied.
    reflexivity.
Qed.

Theorem fsem02BothSourceOfferLabelsRefuseOccupiedSuccessor :
  forall done canceled endpoint successor context,
    String.eqb successor endpoint = false ->
    bindingExists successor context = true ->
    fsem02Progression (FSEM02Offer "Go")
      (fsem02SeparatedOffer done canceled)
      endpoint successor context = StepFailed /\
    fsem02Progression (FSEM02Offer "Cancel")
      (fsem02SeparatedOffer done canceled)
      endpoint successor context = StepFailed.
Proof.
  intros done canceled endpoint successor context Hdistinct Hoccupied.
  split; unfold fsem02Progression;
    change (selectedContinuation
      (FSEM02Offer "Go") (fsem02SeparatedOffer done canceled))
      with (Some (Some (End done))) in *
      || change (selectedContinuation
      (FSEM02Offer "Cancel") (fsem02SeparatedOffer done canceled))
      with (Some (Some (End canceled))) in *.
  - apply fsem02OccupiedUnrelatedSuccessorCannotContinue; assumption.
  - apply fsem02OccupiedUnrelatedSuccessorCannotContinue; assumption.
Qed.

Theorem fsem02BothSourceOfferLabelsRefuseOldNameAsSuccessor :
  forall done canceled endpoint context,
    fsem02Progression (FSEM02Offer "Go")
      (fsem02SeparatedOffer done canceled)
      endpoint endpoint context = StepFailed /\
    fsem02Progression (FSEM02Offer "Cancel")
      (fsem02SeparatedOffer done canceled)
      endpoint endpoint context = StepFailed.
Proof.
  intros done canceled endpoint context.
  split; eapply same_name_successor_rejects; reflexivity.
Qed.

(* Conditional frame/loan theorem: both chosen paths are independent
   alternatives from the exact SAME context, never coexisting successors. *)
Theorem fsem02BothSourceOfferAlternativesFrameIndependentOwner :
  forall done canceled endpoint successor spectator context goNext cancelNext,
    String.eqb spectator endpoint = false ->
    String.eqb spectator successor = false ->
    fsem02Progression (FSEM02Offer "Go")
      (fsem02SeparatedOffer done canceled)
      endpoint successor context = StepSucceeded goNext ->
    fsem02Progression (FSEM02Offer "Cancel")
      (fsem02SeparatedOffer done canceled)
      endpoint successor context = StepSucceeded cancelNext ->
    linearBindings goNext spectator = linearBindings context spectator /\
    linearBindings cancelNext spectator = linearBindings context spectator /\
    sharedLoans goNext = sharedLoans context /\
    sharedLoans cancelNext = sharedLoans context.
Proof.
  intros done canceled endpoint successor spectator context goNext cancelNext
    HotherOld HotherNew Hgo Hcancel.
  pose proof (continuing_head_exact_predecessor_and_successor
    (FSEM02Offer "Go") (fsem02SeparatedOffer done canceled)
    endpoint successor context goNext (End done) eq_refl Hgo) as HgoFacts.
  pose proof (continuing_head_exact_predecessor_and_successor
    (FSEM02Offer "Cancel") (fsem02SeparatedOffer done canceled)
    endpoint successor context cancelNext (End canceled) eq_refl Hcancel)
    as HcancelFacts.
  destruct HgoFacts as [_ [_ [_ [_ [HgoFrame HgoLoans]]]]].
  destruct HcancelFacts as [_ [_ [_ [_ [HcancelFrame HcancelLoans]]]]].
  repeat split.
  - apply HgoFrame; assumption.
  - apply HcancelFrame; assumption.
  - exact HgoLoans.
  - exact HcancelLoans.
Qed.
