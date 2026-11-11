From Stdlib Require Import Strings.String.
From Phil.Core Require Import Syntax Context SessionStep FSEM02ProtocolHeadProgression.

(* FSEM-02 NON-NORMATIVE. Two branches from one initial owner are alternative
   executions, never concurrent successors. External label, admitted protocol
   instance, original activation and End-close authority remain premises.
   SessionStep.endpointType is abstract; no Haskell/Rocq refinement is claimed. *)

Open Scope string_scope.

Definition fsem02SeparatedOffer (done canceled : Outcome) : Session :=
  Offer (BCons "Go" None (End done)
    (BCons "Cancel" None (End canceled) BNil)).

Theorem fsem02BothSourceLabelsHaveTheirOwnExactEndHeads :
  forall done canceled,
    selectedContinuation (FSEM02Offer "Go")
      (fsem02SeparatedOffer done canceled) = Some (Some (End done)) /\
    selectedContinuation (FSEM02Offer "Cancel")
      (fsem02SeparatedOffer done canceled) = Some (Some (End canceled)).
Proof. intros. split; reflexivity. Qed.

Theorem fsem02DifferentOutcomesGiveDifferentChosenHeads :
  forall done canceled,
    done <> canceled ->
    selectedContinuation (FSEM02Offer "Go")
      (fsem02SeparatedOffer done canceled) <>
    selectedContinuation (FSEM02Offer "Cancel")
      (fsem02SeparatedOffer done canceled).
Proof.
  intros done canceled Hdistinct Hsame.
  apply Hdistinct.
  simpl in Hsame.
  congruence.
Qed.

Theorem fsem02BothAlternativesConsumeOldAndTypeOwnSuccessor :
  forall done canceled endpoint successor context goNext cancelNext,
    fsem02Progression (FSEM02Offer "Go")
      (fsem02SeparatedOffer done canceled)
      endpoint successor context = StepSucceeded goNext ->
    fsem02Progression (FSEM02Offer "Cancel")
      (fsem02SeparatedOffer done canceled)
      endpoint successor context = StepSucceeded cancelNext ->
    linearBindings goNext endpoint = None /\
    linearBindings cancelNext endpoint = None /\
    linearBindings goNext successor = Some (endpointType (End done)) /\
    linearBindings cancelNext successor = Some (endpointType (End canceled)).
Proof.
  intros done canceled endpoint successor context goNext cancelNext Hgo Hcancel.
  assert (HgoHead : selectedContinuation (FSEM02Offer "Go")
    (fsem02SeparatedOffer done canceled) = Some (Some (End done)))
    by reflexivity.
  assert (HcancelHead : selectedContinuation (FSEM02Offer "Cancel")
    (fsem02SeparatedOffer done canceled) = Some (Some (End canceled)))
    by reflexivity.
  pose proof (continuing_head_exact_predecessor_and_successor
    (FSEM02Offer "Go") (fsem02SeparatedOffer done canceled)
    endpoint successor context goNext (End done) HgoHead Hgo) as HgoExact.
  pose proof (continuing_head_exact_predecessor_and_successor
    (FSEM02Offer "Cancel") (fsem02SeparatedOffer done canceled)
    endpoint successor context cancelNext (End canceled) HcancelHead Hcancel)
    as HcancelExact.
  destruct HgoExact as [_ [_ [HgoGone [HgoNext _]]]].
  destruct HcancelExact as [_ [_ [HcancelGone [HcancelNext _]]]].
  repeat split; assumption.
Qed.

Theorem fsem02WrongCrossBranchTerminalOutcomeFails :
  forall done canceled endpoint successor context,
    done <> canceled ->
    fsem02Progression (FSEM02Close canceled) (End done)
      endpoint successor context = StepFailed /\
    fsem02Progression (FSEM02Close done) (End canceled)
      endpoint successor context = StepFailed.
Proof.
  intros done canceled endpoint successor context Hdistinct.
  split; apply wrong_terminal_outcome_rejects;
    apply String.eqb_neq; congruence.
Qed.

Theorem fsem02ConsumedGoCannotReplayCancelAtOldOwner :
  forall done canceled endpoint successor nextSuccessor context goNext next,
    fsem02Progression (FSEM02Offer "Go")
      (fsem02SeparatedOffer done canceled)
      endpoint successor context = StepSucceeded goNext ->
    fsem02Progression (FSEM02Offer "Cancel")
      (fsem02SeparatedOffer done canceled)
      endpoint nextSuccessor goNext <> StepSucceeded next.
Proof.
  intros done canceled endpoint successor nextSuccessor context goNext next Hgo.
  assert (Hhead : selectedContinuation (FSEM02Offer "Go")
    (fsem02SeparatedOffer done canceled) = Some (Some (End done)))
    by reflexivity.
  pose proof (continuing_head_exact_predecessor_and_successor
    (FSEM02Offer "Go") (fsem02SeparatedOffer done canceled)
    endpoint successor context goNext (End done) Hhead Hgo) as Hresources.
  destruct Hresources as [_ [_ [Hgone _]]].
  eapply stale_linear_predecessor_cannot_succeed.
  exact Hgone.
Qed.
