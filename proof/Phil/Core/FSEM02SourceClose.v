From Stdlib Require Import Strings.String Bool.Bool.
From Phil.Core Require Import Syntax Context SessionStep
  FSEM02StatefulSourceChoice FSEM02RestrictedSourceTransfer.

(*
  Non-normative FSEM-02 paired source terminal-close owner model. Source shape,
  the preceding checked restricted rendezvous, the independently authorized
  End outcomes, nominal process/role identities, and exact live Haskell
  activation owner indexing are EXTERNAL premises. No model-to-Haskell
  refinement, process completion, assurance discharge or root termination is
  proved. The imported SessionStep.closeEndpointResource_success_exact
  separately proves the resource-side consumption for successful Core close.
*)

Definition fsem02SourceCloseOwners
  (sourceValid headsValid : bool)
  (owners : FSEM02OwnerLedger)
  (clientOccurrence serverOccurrence clientProcess serverProcess : string)
  (clientEndpoint serverEndpoint : Name) : option FSEM02OwnerLedger :=
  if andb sourceValid headsValid then
    if String.eqb clientOccurrence serverOccurrence then None
    else if andb
      (fsem02OwnerMatches owners clientOccurrence clientProcess clientEndpoint)
      (fsem02OwnerMatches owners serverOccurrence serverProcess serverEndpoint)
    then Some (fun occurrence =>
      if orb (String.eqb occurrence clientOccurrence)
             (String.eqb occurrence serverOccurrence)
      then None else owners occurrence)
    else None
  else None.

Theorem fsem02SourceCloseRejectsUnsupported :
  forall headsValid owners clientOccurrence serverOccurrence
         clientProcess serverProcess clientEndpoint serverEndpoint,
    fsem02SourceCloseOwners false headsValid owners
      clientOccurrence serverOccurrence clientProcess serverProcess
      clientEndpoint serverEndpoint = None.
Proof.
  intros. reflexivity.
Qed.

Theorem fsem02SourceCloseRejectsMissingSenderOwner :
  forall sourceValid headsValid owners clientOccurrence serverOccurrence
         clientProcess serverProcess clientEndpoint serverEndpoint,
    owners clientOccurrence = None ->
    fsem02SourceCloseOwners sourceValid headsValid owners
      clientOccurrence serverOccurrence clientProcess serverProcess
      clientEndpoint serverEndpoint = None.
Proof.
  intros sourceValid headsValid owners clientOccurrence serverOccurrence
    clientProcess serverProcess clientEndpoint serverEndpoint Hmissing.
  unfold fsem02SourceCloseOwners.
  destruct (andb sourceValid headsValid); [|reflexivity].
  destruct (String.eqb clientOccurrence serverOccurrence); [reflexivity|].
  unfold fsem02OwnerMatches at 1.
  rewrite Hmissing. reflexivity.
Qed.

Theorem fsem02SourceCloseRejectsMissingReceiverOwner :
  forall sourceValid headsValid owners clientOccurrence serverOccurrence
         clientProcess serverProcess clientEndpoint serverEndpoint,
    owners serverOccurrence = None ->
    fsem02SourceCloseOwners sourceValid headsValid owners
      clientOccurrence serverOccurrence clientProcess serverProcess
      clientEndpoint serverEndpoint = None.
Proof.
  intros sourceValid headsValid owners clientOccurrence serverOccurrence
    clientProcess serverProcess clientEndpoint serverEndpoint Hmissing.
  unfold fsem02SourceCloseOwners.
  destruct (andb sourceValid headsValid); [|reflexivity].
  destruct (String.eqb clientOccurrence serverOccurrence); [reflexivity|].
  destruct (fsem02OwnerMatches owners clientOccurrence clientProcess clientEndpoint);
    [|reflexivity].
  unfold fsem02OwnerMatches. rewrite Hmissing. reflexivity.
Qed.

Theorem fsem02SourceCloseSuccessExactAndFrame :
  forall sourceValid headsValid owners
         clientOccurrence serverOccurrence clientProcess serverProcess
         clientEndpoint serverEndpoint after,
    fsem02SourceCloseOwners sourceValid headsValid owners
      clientOccurrence serverOccurrence clientProcess serverProcess
      clientEndpoint serverEndpoint = Some after ->
    sourceValid = true /\ headsValid = true /\
    clientOccurrence <> serverOccurrence /\
    owners clientOccurrence = Some (clientProcess, clientEndpoint) /\
    owners serverOccurrence = Some (serverProcess, serverEndpoint) /\
    after clientOccurrence = None /\
    after serverOccurrence = None /\
    (forall spectator,
      spectator <> clientOccurrence ->
      spectator <> serverOccurrence ->
      after spectator = owners spectator).
Proof.
  intros sourceValid headsValid owners clientOccurrence serverOccurrence
    clientProcess serverProcess clientEndpoint serverEndpoint after Hstep.
  unfold fsem02SourceCloseOwners in Hstep.
  destruct (andb sourceValid headsValid) eqn:Hvalid; try discriminate.
  destruct (String.eqb clientOccurrence serverOccurrence)
    eqn:Hdistinct; try discriminate.
  destruct (andb
      (fsem02OwnerMatches owners clientOccurrence clientProcess clientEndpoint)
      (fsem02OwnerMatches owners serverOccurrence serverProcess serverEndpoint))
    eqn:Howners; try discriminate.
  inversion Hstep; subst after; clear Hstep.
  apply andb_true_iff in Hvalid as [Hsource Hheads].
  apply andb_true_iff in Howners as [Hclient Hserver].
  apply String.eqb_neq in Hdistinct.
  repeat split.
  - exact Hsource.
  - exact Hheads.
  - exact Hdistinct.
  - apply fsem02SourceOwnerMatchesTrue. exact Hclient.
  - apply fsem02SourceOwnerMatchesTrue. exact Hserver.
  - simpl. now rewrite String.eqb_refl.
  - simpl. rewrite String.eqb_refl. destruct (String.eqb serverOccurrence clientOccurrence);
      reflexivity.
  - intros spectator HnotClient HnotServer.
    simpl.
    assert (Hc : String.eqb spectator clientOccurrence = false).
    { now apply String.eqb_neq. }
    assert (Hs : String.eqb spectator serverOccurrence = false).
    { now apply String.eqb_neq. }
    now rewrite Hc, Hs.
Qed.

Theorem fsem02SourceCloseResourceAndOwners :
  forall sourceValid headsValid owners
         clientOccurrence serverOccurrence clientProcess serverProcess
         clientEndpoint serverEndpoint ownerAfter
         clientBefore clientAfter serverBefore serverAfter,
    fsem02SourceCloseOwners sourceValid headsValid owners
      clientOccurrence serverOccurrence clientProcess serverProcess
      clientEndpoint serverEndpoint = Some ownerAfter ->
    closeEndpointResource clientEndpoint clientBefore = StepSucceeded clientAfter ->
    closeEndpointResource serverEndpoint serverBefore = StepSucceeded serverAfter ->
    linearBindings clientAfter clientEndpoint = None /\
    linearBindings serverAfter serverEndpoint = None /\
    ownerAfter clientOccurrence = None /\
    ownerAfter serverOccurrence = None.
Proof.
  intros sourceValid headsValid owners clientOccurrence serverOccurrence
    clientProcess serverProcess clientEndpoint serverEndpoint ownerAfter
    clientBefore clientAfter serverBefore serverAfter
    Howners Hclient Hserver.
  pose proof
    (closeEndpointResource_success_exact clientEndpoint clientBefore clientAfter Hclient)
    as [_ [HclientGone _]].
  pose proof
    (closeEndpointResource_success_exact serverEndpoint serverBefore serverAfter Hserver)
    as [_ [HserverGone _]].
  pose proof
    (fsem02SourceCloseSuccessExactAndFrame
      sourceValid headsValid owners clientOccurrence serverOccurrence
      clientProcess serverProcess clientEndpoint serverEndpoint ownerAfter Howners)
    as [_ [_ [_ [_ [_ [HclientRetired [HserverRetired _]]]]]]].
  repeat split; assumption.
Qed.
