From Stdlib Require Import Strings.String.
From Phil.Core Require Import Syntax FSEM02StatefulSourceChoice FSEM02SourceClose.

(*
  Non-normative FSEM-02 owner-index observation relation for exact
  terminal-close replay. This conditional model compares a purported owner
  observation with the *computed* paired close owner transition at every key.
  Haskell checks equality of the full native ProcessCommunicationState after
  independently re-executing both closeProcessEndpointState transitions.
  This Rocq relation models only the owner projection; source admission,
  protocol authority, Core resource maps, and Haskell/Rocq representation
  correspondence remain external premises. No universal refinement is claimed.
*)

Definition fsem02OwnerReplayAgreement
  (sourceValid headsValid : bool)
  (before observed : FSEM02OwnerLedger)
  (senderOccurrence receiverOccurrence senderProcess receiverProcess : string)
  (senderEndpoint receiverEndpoint : Name) : Prop :=
  exists computed,
    fsem02SourceCloseOwners sourceValid headsValid before
      senderOccurrence receiverOccurrence senderProcess receiverProcess
      senderEndpoint receiverEndpoint = Some computed /\
    (forall key, observed key = computed key).

Theorem fsem02OwnerReplayExactRetirementAndFrame :
  forall sourceValid headsValid before observed
         senderOccurrence receiverOccurrence senderProcess receiverProcess
         senderEndpoint receiverEndpoint,
    fsem02OwnerReplayAgreement sourceValid headsValid before observed
      senderOccurrence receiverOccurrence senderProcess receiverProcess
      senderEndpoint receiverEndpoint ->
    observed senderOccurrence = None /\
    observed receiverOccurrence = None /\
    (forall spectator,
      spectator <> senderOccurrence ->
      spectator <> receiverOccurrence ->
      observed spectator = before spectator).
Proof.
  intros sourceValid headsValid before observed
    senderOccurrence receiverOccurrence senderProcess receiverProcess
    senderEndpoint receiverEndpoint
    [computed [Hstep Hsame]].
  pose proof
    (fsem02SourceCloseSuccessExactAndFrame
      sourceValid headsValid before senderOccurrence receiverOccurrence
      senderProcess receiverProcess senderEndpoint receiverEndpoint
      computed Hstep)
    as [_ [_ [_ [_ [_ [Hsender [Hreceiver Hframe]]]]]]].
  repeat split.
  - rewrite (Hsame senderOccurrence). exact Hsender.
  - rewrite (Hsame receiverOccurrence). exact Hreceiver.
  - intros spectator HnotSender HnotReceiver.
    rewrite (Hsame spectator).
    apply Hframe; assumption.
Qed.

Theorem fsem02OwnerReplayRejectsLiveSender :
  forall sourceValid headsValid before observed
         senderOccurrence receiverOccurrence senderProcess receiverProcess
         senderEndpoint receiverEndpoint,
    observed senderOccurrence <> None ->
    ~ fsem02OwnerReplayAgreement sourceValid headsValid before observed
      senderOccurrence receiverOccurrence senderProcess receiverProcess
      senderEndpoint receiverEndpoint.
Proof.
  intros sourceValid headsValid before observed
    senderOccurrence receiverOccurrence senderProcess receiverProcess
    senderEndpoint receiverEndpoint Hlive Hagreement.
  apply Hlive.
  pose proof (fsem02OwnerReplayExactRetirementAndFrame
    sourceValid headsValid before observed senderOccurrence receiverOccurrence
    senderProcess receiverProcess senderEndpoint receiverEndpoint Hagreement)
    as [Hgone _].
  exact Hgone.
Qed.

Theorem fsem02OwnerReplayRejectsChangedSpectator :
  forall sourceValid headsValid before observed
         senderOccurrence receiverOccurrence senderProcess receiverProcess
         senderEndpoint receiverEndpoint spectator,
    spectator <> senderOccurrence ->
    spectator <> receiverOccurrence ->
    observed spectator <> before spectator ->
    ~ fsem02OwnerReplayAgreement sourceValid headsValid before observed
      senderOccurrence receiverOccurrence senderProcess receiverProcess
      senderEndpoint receiverEndpoint.
Proof.
  intros sourceValid headsValid before observed
    senderOccurrence receiverOccurrence senderProcess receiverProcess
    senderEndpoint receiverEndpoint spectator HnotSender HnotReceiver
    Hchanged Hagreement.
  apply Hchanged.
  pose proof (fsem02OwnerReplayExactRetirementAndFrame
    sourceValid headsValid before observed senderOccurrence receiverOccurrence
    senderProcess receiverProcess senderEndpoint receiverEndpoint Hagreement)
    as [_ [_ Hframe]].
  apply Hframe; assumption.
Qed.
