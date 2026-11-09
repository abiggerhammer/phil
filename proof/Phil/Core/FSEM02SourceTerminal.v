From Stdlib Require Import Strings.String Bool.Bool.
From Phil.Core Require Import Syntax FSEM02StatefulSourceChoice FSEM02RestrictedSourceTransfer FSEM02SourceClose.

(*
  Non-normative FSEM-02 terminal-obligation gate for the bounded, already
  source-checked send/receive/close prefix. The booleans represent EXTERNAL
  decisions: correct source close identity, successful native lifecycle
  terminal checks and independently established root closure residues.
  Exact owner identities/occurrences and completeness of the finite owner
  index are premises. No source program or Haskell implementation is proven
  to satisfy these premises, and no unconditional terminality is asserted.
*)

Definition fsem02TerminalDisposeOwners
  (sourceCloseValid lifecycleValid rootValid : bool)
  (owners : FSEM02OwnerLedger)
  (payloadOccurrence spectatorOccurrence receiverProcess senderProcess : string)
  (payloadName spectatorName : Name) : option FSEM02OwnerLedger :=
  if andb sourceCloseValid (andb lifecycleValid rootValid) then
    fsem02SourceCloseOwners true true owners
      payloadOccurrence spectatorOccurrence receiverProcess senderProcess
      payloadName spectatorName
  else None.

Theorem fsem02TerminalRejectsUnvalidatedSource :
  forall lifecycleValid rootValid owners payload spectator receiver sender
         payloadName spectatorName,
    fsem02TerminalDisposeOwners false lifecycleValid rootValid owners
      payload spectator receiver sender payloadName spectatorName = None.
Proof. intros; reflexivity. Qed.

Theorem fsem02TerminalRejectsOpenLifecycle :
  forall sourceValid rootValid owners payload spectator receiver sender
         payloadName spectatorName,
    fsem02TerminalDisposeOwners sourceValid false rootValid owners
      payload spectator receiver sender payloadName spectatorName = None.
Proof.
  intros. unfold fsem02TerminalDisposeOwners.
  destruct sourceValid; reflexivity.
Qed.

Theorem fsem02TerminalRejectsOpenRoot :
  forall sourceValid lifecycleValid owners payload spectator receiver sender
         payloadName spectatorName,
    fsem02TerminalDisposeOwners sourceValid lifecycleValid false owners
      payload spectator receiver sender payloadName spectatorName = None.
Proof.
  intros. unfold fsem02TerminalDisposeOwners.
  destruct sourceValid, lifecycleValid; reflexivity.
Qed.

Theorem fsem02TerminalSuccessExact :
  forall sourceValid lifecycleValid rootValid owners
         payload spectator receiver sender payloadName spectatorName after,
    fsem02TerminalDisposeOwners sourceValid lifecycleValid rootValid owners
      payload spectator receiver sender payloadName spectatorName = Some after ->
    sourceValid = true /\ lifecycleValid = true /\ rootValid = true /\
    payload <> spectator /\
    owners payload = Some (receiver, payloadName) /\
    owners spectator = Some (sender, spectatorName) /\
    after payload = None /\ after spectator = None /\
    (forall unrelated,
      unrelated <> payload -> unrelated <> spectator ->
      after unrelated = owners unrelated).
Proof.
  intros sourceValid lifecycleValid rootValid owners
    payload spectator receiver sender payloadName spectatorName after Hstep.
  unfold fsem02TerminalDisposeOwners in Hstep.
  destruct (andb sourceValid (andb lifecycleValid rootValid)) eqn:Hgate;
    try discriminate.
  apply andb_true_iff in Hgate as [Hsource Hrest].
  apply andb_true_iff in Hrest as [Hlifecycle Hroot].
  pose proof (fsem02SourceCloseSuccessExactAndFrame
      true true owners payload spectator receiver sender
      payloadName spectatorName after Hstep)
      as [_ [_ [Hdistinct [Hpayload [Hspectator
        [HpayloadGone [HspectatorGone Hframe]]]]]]].
  repeat split; assumption.
Qed.

Theorem fsem02TerminalIndexEmptyIfAllOtherOwnersAbsent :
  forall sourceValid lifecycleValid rootValid owners
         payload spectator receiver sender payloadName spectatorName after,
    fsem02TerminalDisposeOwners sourceValid lifecycleValid rootValid owners
      payload spectator receiver sender payloadName spectatorName = Some after ->
    (forall k, k <> payload -> k <> spectator -> owners k = None) ->
    forall k, after k = None.
Proof.
  intros sourceValid lifecycleValid rootValid owners
    payload spectator receiver sender payloadName spectatorName after
    Hstep Hcomplete k.
  pose proof (fsem02TerminalSuccessExact
    sourceValid lifecycleValid rootValid owners payload spectator
    receiver sender payloadName spectatorName after Hstep)
    as [_ [_ [_ [_ [_ [_ [Hpayload [Hspectator Hframe]]]]]]]].
  destruct (string_dec k payload) as [HkPayload|HkPayload].
  - subst k. exact Hpayload.
  - destruct (string_dec k spectator) as [HkSpectator|HkSpectator].
    + subst k. exact Hspectator.
    + rewrite (Hframe k HkPayload HkSpectator).
      exact (Hcomplete k HkPayload HkSpectator).
Qed.
