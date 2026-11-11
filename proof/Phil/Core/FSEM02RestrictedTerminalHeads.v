From Stdlib Require Import Strings.String Bool.Bool.
From Phil.Core Require Import Syntax FSEM02RestrictedSourceTransfer.

(*
  FSEM-02 NON-NORMATIVE bounded terminal-continuation head gate.
  The four head/End-match flags are independently checked native evidence,
  NOT a parser, protocol-instance authority, disposal grant or root proof.
  This model refines the existing restricted-owner transfer by requiring
  both Send/Receive head forms and both exact terminal outcomes before
  exposing a successor. Concrete Haskell Text/Map correspondence remains
  executable-test evidence, not a global refinement theorem.
*)

Definition fsem02RestrictedTerminalHeadAdvance
  (sourceAccepted messageAdmitted : bool)
  (senderSend receiverReceive senderEndMatch receiverEndMatch : bool)
  (owners : FSEM02OwnerLedger)
  (senderOccurrence receiverOccurrence payloadOccurrence : string)
  (senderProcess receiverProcess : string)
  (senderOld senderNext receiverOld receiverNext payloadOld payloadNext : Name)
  : option FSEM02OwnerLedger :=
  if andb senderSend
       (andb receiverReceive (andb senderEndMatch receiverEndMatch))
  then fsem02RestrictedSourceTransfer
    sourceAccepted messageAdmitted true owners
    senderOccurrence receiverOccurrence payloadOccurrence
    senderProcess receiverProcess
    senderOld senderNext receiverOld receiverNext payloadOld payloadNext
  else None.

Theorem fsem02RestrictedTerminalHeadNoSenderHead :
  forall sourceAccepted messageAdmitted receiverReceive senderEndMatch receiverEndMatch
    owners sc rc pc sp rp so sn ro rn po pn,
    fsem02RestrictedTerminalHeadAdvance
      sourceAccepted messageAdmitted false receiverReceive
      senderEndMatch receiverEndMatch owners sc rc pc sp rp so sn ro rn po pn = None.
Proof. intros. reflexivity. Qed.

Theorem fsem02RestrictedTerminalHeadNoReceiverHead :
  forall sourceAccepted messageAdmitted senderSend senderEndMatch receiverEndMatch
    owners sc rc pc sp rp so sn ro rn po pn,
    fsem02RestrictedTerminalHeadAdvance
      sourceAccepted messageAdmitted senderSend false
      senderEndMatch receiverEndMatch owners sc rc pc sp rp so sn ro rn po pn = None.
Proof. intros. destruct senderSend; reflexivity. Qed.

Theorem fsem02RestrictedTerminalHeadWrongEndIsNoSuccessor :
  forall sourceAccepted messageAdmitted senderSend receiverReceive
    senderEndMatch receiverEndMatch owners sc rc pc sp rp so sn ro rn po pn,
    senderEndMatch = false \/ receiverEndMatch = false ->
    fsem02RestrictedTerminalHeadAdvance
      sourceAccepted messageAdmitted senderSend receiverReceive
      senderEndMatch receiverEndMatch owners sc rc pc sp rp so sn ro rn po pn = None.
Proof.
  intros sourceAccepted messageAdmitted senderSend receiverReceive
    senderEndMatch receiverEndMatch owners sc rc pc sp rp so sn ro rn po pn Hbad.
  destruct senderSend, receiverReceive, senderEndMatch, receiverEndMatch;
    simpl in *; try reflexivity; destruct Hbad as [Hbad | Hbad]; discriminate.
Qed.

Theorem fsem02RestrictedTerminalHeadSuccessExact :
  forall sourceAccepted messageAdmitted senderSend receiverReceive
    senderEndMatch receiverEndMatch owners sc rc pc sp rp
    so sn ro rn po pn after,
    fsem02RestrictedTerminalHeadAdvance
      sourceAccepted messageAdmitted senderSend receiverReceive
      senderEndMatch receiverEndMatch owners sc rc pc sp rp
      so sn ro rn po pn = Some after ->
    senderSend = true /\ receiverReceive = true /\
    senderEndMatch = true /\ receiverEndMatch = true /\
    sourceAccepted = true /\ messageAdmitted = true /\
    after sc = Some (sp, sn) /\
    after rc = Some (rp, rn) /\
    after pc = Some (rp, pn) /\
    (forall spectator, spectator <> sc -> spectator <> rc -> spectator <> pc ->
       after spectator = owners spectator).
Proof.
  intros sourceAccepted messageAdmitted senderSend receiverReceive
    senderEndMatch receiverEndMatch owners sc rc pc sp rp
    so sn ro rn po pn after Hstep.
  unfold fsem02RestrictedTerminalHeadAdvance in Hstep.
  destruct senderSend, receiverReceive, senderEndMatch, receiverEndMatch;
    simpl in Hstep; try discriminate.
  pose proof (fsem02RestrictedSourceSuccessExactAndFrame
    sourceAccepted messageAdmitted true owners sc rc pc sp rp
    so sn ro rn po pn after Hstep)
    as [Hsource [Hmessage [_ [_ [Hpayload [Hsender [Hreceiver Hframe]]]]]]].
  repeat (apply conj); try reflexivity; try assumption.
  intros spectator Hsc Hrc Hpc.
  apply Hframe; assumption.
Qed.
