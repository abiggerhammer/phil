From Stdlib Require Import Strings.String.
From Phil.Core Require Import Syntax Context SessionStep FSEM02ProtocolHeadProgression.

(*
  FSEM-02 NON-NORMATIVE: two distinct, payload-parametric protocol branch
  labels may be reordered without changing the selected local continuation
  or the modeled offer replay. Distinctness is essential: a duplicated
  label with different continuations is order-sensitive in this finite model.
  Source coverage and local Core comparison are checked separately in Haskell.
  No model-to-Haskell refinement, activation, root, or disposal authority.
*)

Theorem fsem02TwoDistinctBranchContinuationPermutation :
  forall (chosen first second : string)
         (firstPayload secondPayload : option (Name * Ty))
         (firstNext secondNext : Session),
    first <> second ->
    offeredContinuation chosen
      (BCons first firstPayload firstNext
        (BCons second secondPayload secondNext BNil)) =
    offeredContinuation chosen
      (BCons second secondPayload secondNext
        (BCons first firstPayload firstNext BNil)).
Proof.
  intros chosen first second firstPayload secondPayload firstNext secondNext
    Hdistinct.
  simpl.
  destruct (String.eqb chosen first) eqn:Hfirst;
  destruct (String.eqb chosen second) eqn:Hsecond;
    try reflexivity.
  apply String.eqb_eq in Hfirst.
  apply String.eqb_eq in Hsecond.
  exfalso. apply Hdistinct. congruence.
Qed.

Theorem fsem02DistinctBranchPermutationPreservesOfferReplay :
  forall (labels : list string) (chosen first second : string)
         (firstPayload secondPayload : option (Name * Ty))
         (firstNext secondNext : Session)
         (endpoint successor : Name) (context : ResourceContext),
    first <> second ->
    fsem02SourceOfferReplay labels
      (BCons first firstPayload firstNext
        (BCons second secondPayload secondNext BNil))
      chosen endpoint successor context =
    fsem02SourceOfferReplay labels
      (BCons second secondPayload secondNext
        (BCons first firstPayload firstNext BNil))
      chosen endpoint successor context.
Proof.
  intros labels chosen first second firstPayload secondPayload
    firstNext secondNext endpoint successor context Hdistinct.
  unfold fsem02SourceOfferReplay.
  destruct (fsem02SourceContainsLabel chosen labels); [|reflexivity].
  unfold fsem02Progression.
  cbn [selectedContinuation].
  rewrite (fsem02TwoDistinctBranchContinuationPermutation
    chosen first second firstPayload secondPayload
    firstNext secondNext Hdistinct).
  reflexivity.
Qed.

Theorem fsem02DuplicateBranchHeadIsOrderSensitive :
  forall (label : string)
         (firstPayload secondPayload : option (Name * Ty))
         (firstNext secondNext : Session),
    firstNext <> secondNext ->
    offeredContinuation label
      (BCons label firstPayload firstNext
        (BCons label secondPayload secondNext BNil)) <>
    offeredContinuation label
      (BCons label secondPayload secondNext
        (BCons label firstPayload firstNext BNil)).
Proof.
  intros label firstPayload secondPayload firstNext secondNext Hdifferent.
  simpl. rewrite String.eqb_refl.
  intro Heq. inversion Heq. contradiction.
Qed.

Theorem fsem02PermutedOfferNeverRevivesStalePredecessor :
  forall (labels : list string) (chosen first second : string)
         (firstPayload secondPayload : option (Name * Ty))
         (firstNext secondNext : Session)
         (endpoint successor : Name) (context next : ResourceContext),
    first <> second ->
    linearBindings context endpoint = None ->
    fsem02SourceOfferReplay labels
      (BCons second secondPayload secondNext
        (BCons first firstPayload firstNext BNil))
      chosen endpoint successor context <> StepSucceeded next.
Proof.
  intros labels chosen first second firstPayload secondPayload
    firstNext secondNext endpoint successor context next
    _ Hstale Hsuccess.
  unfold fsem02SourceOfferReplay in Hsuccess.
  destruct (fsem02SourceContainsLabel chosen labels);
    [|discriminate].
  eapply stale_linear_predecessor_cannot_succeed;
    eassumption.
Qed.
