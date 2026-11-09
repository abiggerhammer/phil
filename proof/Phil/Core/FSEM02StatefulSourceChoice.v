From Stdlib Require Import Strings.String Bool.Bool Lists.List.
From Phil.Core Require Import Syntax Context FSEM02JointSourceChoice.

(*
  Non-normative FSEM-02 owner-ledger model. An owner ledger is a partial
  occurrence-key map, distinct from a local resource context. Process/occurrence
  identities, peer choice and the initially valid ledger are external premises.
  This models exact owner-key renaming, NOT universal Haskell Map refinement.
*)
Definition FSEM02OwnerLedger := string -> option (string * Name).

Definition fsem02OwnerMatches (owners : FSEM02OwnerLedger)
  (occurrence process : string) (localName : Name) : bool :=
  match owners occurrence with
  | Some (actualProcess, actualName) =>
      andb (String.eqb actualProcess process) (String.eqb actualName localName)
  | None => false
  end.

Definition fsem02AdvanceChoiceOwners (owners : FSEM02OwnerLedger)
  (clientOccurrence offerOccurrence clientProcess offerProcess : string)
  (clientOld clientNext offerOld offerNext : Name)
  : option FSEM02OwnerLedger :=
  if String.eqb clientOccurrence offerOccurrence then None
  else if andb
      (fsem02OwnerMatches owners clientOccurrence clientProcess clientOld)
      (fsem02OwnerMatches owners offerOccurrence offerProcess offerOld)
    then Some (fun occurrence =>
      if String.eqb occurrence clientOccurrence
        then Some (clientProcess, clientNext)
      else if String.eqb occurrence offerOccurrence
        then Some (offerProcess, offerNext)
      else owners occurrence)
    else None.

Theorem fsem02AdvanceChoiceOwnersRejectsAliasedOccurrence :
  forall owners occurrence clientProcess offerProcess
         clientOld clientNext offerOld offerNext,
    fsem02AdvanceChoiceOwners owners occurrence occurrence
      clientProcess offerProcess clientOld clientNext offerOld offerNext = None.
Proof.
  intros. unfold fsem02AdvanceChoiceOwners.
  now rewrite String.eqb_refl.
Qed.

Theorem fsem02AdvanceChoiceOwnersRejectsMissingClient :
  forall owners clientOccurrence offerOccurrence clientProcess offerProcess
         clientOld clientNext offerOld offerNext,
    owners clientOccurrence = None ->
    fsem02AdvanceChoiceOwners owners clientOccurrence offerOccurrence
      clientProcess offerProcess clientOld clientNext offerOld offerNext = None.
Proof.
  intros owners clientOccurrence offerOccurrence clientProcess offerProcess
    clientOld clientNext offerOld offerNext Hmissing.
  unfold fsem02AdvanceChoiceOwners.
  destruct (String.eqb clientOccurrence offerOccurrence); [reflexivity|].
  unfold fsem02OwnerMatches at 1.
  now rewrite Hmissing.
Qed.

Theorem fsem02AdvanceChoiceOwnersSuccessExactAndFrame :
  forall owners clientOccurrence offerOccurrence clientProcess offerProcess
         clientOld clientNext offerOld offerNext after,
    fsem02AdvanceChoiceOwners owners clientOccurrence offerOccurrence
      clientProcess offerProcess clientOld clientNext offerOld offerNext =
      Some after ->
    after clientOccurrence = Some (clientProcess, clientNext) /\
    after offerOccurrence = Some (offerProcess, offerNext) /\
    (forall spectator,
      spectator <> clientOccurrence ->
      spectator <> offerOccurrence ->
      after spectator = owners spectator).
Proof.
  intros owners clientOccurrence offerOccurrence clientProcess offerProcess
    clientOld clientNext offerOld offerNext after Hsuccess.
  unfold fsem02AdvanceChoiceOwners in Hsuccess.
  destruct (String.eqb clientOccurrence offerOccurrence) eqn:Hdistinct;
    try discriminate.
  destruct (andb
    (fsem02OwnerMatches owners clientOccurrence clientProcess clientOld)
    (fsem02OwnerMatches owners offerOccurrence offerProcess offerOld))
    eqn:Hmatches; try discriminate.
  inversion Hsuccess; subst; clear Hsuccess.
  apply String.eqb_neq in Hdistinct.
  assert (Hother : String.eqb offerOccurrence clientOccurrence = false).
  { apply String.eqb_neq. intro Hsame. apply Hdistinct. symmetry. exact Hsame. }
  repeat split.
  - simpl. now rewrite String.eqb_refl.
  - simpl. now rewrite Hother, String.eqb_refl.
  - intros spectator HfreshClient HfreshOffer. simpl.
    assert (Hc : String.eqb spectator clientOccurrence = false).
    { now apply String.eqb_neq. }
    assert (Ho : String.eqb spectator offerOccurrence = false).
    { now apply String.eqb_neq. }
    now rewrite Hc, Ho.
Qed.

(* This is a *composition* of the pre-existing conditional source-choice
   resource model and the new separately checked endpoint owner index step.
   It does not assert that a Haskell activation ledger refines this function. *)
Definition fsem02StatefulSourceChoice
  (sourceLabels : list string) (branches : Branches)
  (chosen peer : string)
  (clientOld clientNext offerOld offerNext : Name)
  (clientContext offerContext : ResourceContext)
  (owners : FSEM02OwnerLedger)
  (clientOccurrence offerOccurrence clientProcess offerProcess : string)
  : option ((ResourceContext * ResourceContext) * FSEM02OwnerLedger) :=
  match fsem02JointSourceChoice sourceLabels branches chosen peer
          clientOld clientNext offerOld offerNext clientContext offerContext,
        fsem02AdvanceChoiceOwners owners
          clientOccurrence offerOccurrence clientProcess offerProcess
          clientOld clientNext offerOld offerNext with
  | Some (clientAfter, offerAfter), Some ownersAfter =>
      Some ((clientAfter, offerAfter), ownersAfter)
  | _, _ => None
  end.

Theorem fsem02StatefulSourceChoiceSuccessIsJointAndExactOwners :
  forall sourceLabels branches chosen peer clientOld clientNext
         offerOld offerNext clientContext offerContext
         owners clientOccurrence offerOccurrence clientProcess offerProcess
         clientAfter offerAfter ownersAfter,
    fsem02StatefulSourceChoice sourceLabels branches chosen peer
      clientOld clientNext offerOld offerNext clientContext offerContext
      owners clientOccurrence offerOccurrence clientProcess offerProcess =
      Some ((clientAfter, offerAfter), ownersAfter) ->
    fsem02JointSourceChoice sourceLabels branches chosen peer
      clientOld clientNext offerOld offerNext clientContext offerContext =
      Some (clientAfter, offerAfter) /\
    ownersAfter clientOccurrence = Some (clientProcess, clientNext) /\
    ownersAfter offerOccurrence = Some (offerProcess, offerNext) /\
    (forall spectator,
      spectator <> clientOccurrence ->
      spectator <> offerOccurrence ->
      ownersAfter spectator = owners spectator).
Proof.
  intros sourceLabels branches chosen peer clientOld clientNext
    offerOld offerNext clientContext offerContext owners
    clientOccurrence offerOccurrence clientProcess offerProcess
    clientAfter offerAfter ownersAfter Hstep.
  unfold fsem02StatefulSourceChoice in Hstep.
  destruct (fsem02JointSourceChoice sourceLabels branches chosen peer
      clientOld clientNext offerOld offerNext clientContext offerContext)
      as [[clientResult offerResult]|] eqn:Hjoint; try discriminate.
  destruct (fsem02AdvanceChoiceOwners owners
      clientOccurrence offerOccurrence clientProcess offerProcess
      clientOld clientNext offerOld offerNext)
      as [ownerResult|] eqn:Howner; try discriminate.
  inversion Hstep; subst; clear Hstep.
  pose proof (fsem02AdvanceChoiceOwnersSuccessExactAndFrame
    owners clientOccurrence offerOccurrence clientProcess offerProcess
    clientOld clientNext offerOld offerNext ownersAfter Howner) as Howners.
  destruct Howners as [Hclient [Hoffer Hframe]].
  repeat split; assumption.
Qed.
