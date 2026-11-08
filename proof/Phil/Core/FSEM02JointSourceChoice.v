From Stdlib Require Import Strings.String Lists.List.
Import ListNotations.

From Phil.Core Require Import
  Syntax Context SessionStep FSEM02ProtocolHeadProgression.

(*
  FSEM-02 non-normative two-ended local-choice relation.
  External peer choice and finite source offer catalog are inputs, never
  derived from a scheduler, owner map, architecture, or source evaluator.
  The Haskell ProcessRendezvous checker separately enforces live dual heads,
  exact protocol identity/role, both process activation and atomic progression.
  This model proves only the conditional *local resource* consequences.
*)

Definition fsem02JointSourceChoice
  (sourceLabels : list string) (branches : Branches)
  (chosen peer : string)
  (clientOld clientNext offerOld offerNext : Name)
  (clientContext offerContext : ResourceContext)
  : option (ResourceContext * ResourceContext) :=
  if String.eqb chosen peer then
    if fsem02SourceContainsLabel chosen sourceLabels then
      match fsem02Progression (FSEM02Select chosen) (Select branches)
              clientOld clientNext clientContext,
            fsem02SourceOfferReplay sourceLabels branches chosen
              offerOld offerNext offerContext with
      | StepSucceeded clientAfter, StepSucceeded offerAfter =>
          Some (clientAfter, offerAfter)
      | _, _ => None
      end
    else None
  else None.

Theorem fsem02JointSourceChoiceRejectsPeerMismatch :
  forall sourceLabels branches chosen peer clientOld clientNext
         offerOld offerNext clientContext offerContext,
    String.eqb chosen peer = false ->
    fsem02JointSourceChoice sourceLabels branches chosen peer
      clientOld clientNext offerOld offerNext clientContext offerContext = None.
Proof.
  intros sourceLabels branches chosen peer clientOld clientNext
    offerOld offerNext clientContext offerContext Hmismatch.
  unfold fsem02JointSourceChoice. now rewrite Hmismatch.
Qed.

Theorem fsem02JointSourceChoiceRejectsUnlistedLabel :
  forall sourceLabels branches chosen peer clientOld clientNext
         offerOld offerNext clientContext offerContext,
    ~ In chosen sourceLabels ->
    fsem02JointSourceChoice sourceLabels branches chosen peer
      clientOld clientNext offerOld offerNext clientContext offerContext = None.
Proof.
  intros sourceLabels branches chosen peer clientOld clientNext
    offerOld offerNext clientContext offerContext Habsent.
  unfold fsem02JointSourceChoice.
  destruct (String.eqb chosen peer).
  - now rewrite (fsem02SourceContainsLabelWhenAbsent
      sourceLabels chosen Habsent).
  - reflexivity.
Qed.

Theorem fsem02JointSourceChoiceSuccessConsumesBothExactPredecessors :
  forall sourceLabels branches chosen peer clientOld clientNext
         offerOld offerNext clientContext offerContext
         clientAfter offerAfter continuation,
    offeredContinuation chosen branches = Some continuation ->
    fsem02JointSourceChoice sourceLabels branches chosen peer
      clientOld clientNext offerOld offerNext clientContext offerContext =
      Some (clientAfter, offerAfter) ->
    String.eqb chosen peer = true /\
    linearBindings clientAfter clientOld = None /\
    linearBindings clientAfter clientNext = Some (endpointType continuation) /\
    linearBindings offerAfter offerOld = None /\
    linearBindings offerAfter offerNext = Some (endpointType continuation).
Proof.
  intros sourceLabels branches chosen peer clientOld clientNext
    offerOld offerNext clientContext offerContext
    clientAfter offerAfter continuation Hcontinuation Hjoint.
  unfold fsem02JointSourceChoice in Hjoint.
  destruct (String.eqb chosen peer) eqn:Hpeer; try discriminate.
  destruct (fsem02SourceContainsLabel chosen sourceLabels) eqn:Hcovered;
    try discriminate.
  destruct (fsem02Progression (FSEM02Select chosen) (Select branches)
    clientOld clientNext clientContext) as [| c] eqn:Hclient;
    try discriminate.
  destruct (fsem02SourceOfferReplay sourceLabels branches chosen
    offerOld offerNext offerContext) as [| o] eqn:Hoffer;
    try discriminate.
  inversion Hjoint; subst; clear Hjoint.
  pose proof (selected_branch_consumes_and_types_exact_successor
    chosen branches clientOld clientNext clientContext c continuation
    Hcontinuation Hclient) as [HclientGone HclientNext].
  unfold fsem02SourceOfferReplay in Hoffer.
  rewrite Hcovered in Hoffer.
  assert (Hselected :
    selectedContinuation (FSEM02Offer chosen) (Offer branches) =
      Some (Some continuation)).
  { simpl. now rewrite Hcontinuation. }
  pose proof (continuing_head_exact_predecessor_and_successor
    (FSEM02Offer chosen) (Offer branches)
    offerOld offerNext offerContext o continuation
    Hselected Hoffer) as Hresources.
  destruct Hresources as [_ [_ [HofferGone [HofferNext _]]]].
  repeat split; assumption.
Qed.
