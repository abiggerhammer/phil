From Stdlib Require Import Strings.String.
From Phil.Core Require Import Syntax FSEM02StatefulSourceChoice
  FSEM02SelectedClientClose FSEM02ExplicitPeerClose
  FSEM02TerminalCloseDiamond.

(* NON-NORMATIVE FSEM-02. The bool is an EXTERNALLY supplied, already
   checked terminal End outcome admission; a false gate cannot create a
   successful local owner transition. A failed trial does not mutate the
   committed input ledger. No source authority or Haskell refinement. *)
Definition fsem02ChoiceTrialPeerAfterClient
  (outcomeAdmitted : bool) (owners : FSEM02OwnerLedger)
  (occurrence process : string) (endpoint : Name)
  : option FSEM02OwnerLedger :=
  if outcomeAdmitted
  then fsem02RetireExplicitPeerEnd owners occurrence process endpoint
  else None.

Definition fsem02ChoiceTrialClientAfterPeer
  (outcomeAdmitted : bool) (owners : FSEM02OwnerLedger)
  (occurrence process : string) (endpoint : Name)
  : option FSEM02OwnerLedger :=
  if outcomeAdmitted
  then fsem02RetireSelectedClientOwner owners occurrence process endpoint
  else None.

Theorem fsem02ChoiceClientFirstRefusedPeerThenValidRetry :
  forall owners clientOccurrence clientProcess clientEndpoint
    peerOccurrence peerProcess peerEndpoint
    afterClient afterForward afterPeer afterReverse,
    clientOccurrence <> peerOccurrence ->
    fsem02RetireSelectedClientOwner owners
      clientOccurrence clientProcess clientEndpoint = Some afterClient ->
    fsem02RetireExplicitPeerEnd afterClient
      peerOccurrence peerProcess peerEndpoint = Some afterForward ->
    fsem02RetireExplicitPeerEnd owners
      peerOccurrence peerProcess peerEndpoint = Some afterPeer ->
    fsem02RetireSelectedClientOwner afterPeer
      clientOccurrence clientProcess clientEndpoint = Some afterReverse ->
    fsem02ChoiceTrialPeerAfterClient false afterClient
      peerOccurrence peerProcess peerEndpoint = None /\
    fsem02ChoiceTrialPeerAfterClient true afterClient
      peerOccurrence peerProcess peerEndpoint = Some afterForward /\
    afterClient clientOccurrence = None /\
    afterClient peerOccurrence = Some (peerProcess, peerEndpoint) /\
    (forall spectator, spectator <> clientOccurrence ->
      afterClient spectator = owners spectator) /\
    (forall observed, afterForward observed = afterReverse observed).
Proof.
  intros owners co cp ce po pp pe ac af ap ar
    Hdistinct Hclient Hpeer HpeerFirst HclientSecond.
  pose proof (fsem02SelectedClientCloseExactRetirementAndFrame
    owners co cp ce ac Hclient) as [Hgone Hframe].
  pose proof (fsem02SelectedClientCloseRequiresExactOwner
    ac po pp pe af Hpeer) as HpeerLive.
  pose proof (fsem02ConditionalTerminalCloseDiamond
    owners co cp ce po pp pe ac af ap ar
    Hdistinct Hclient Hpeer HpeerFirst HclientSecond) as Hdiamond.
  repeat split.
  - reflexivity.
  - simpl. exact Hpeer.
  - exact Hgone.
  - exact HpeerLive.
  - intros spectator Hother. apply Hframe. exact Hother.
  - exact Hdiamond.
Qed.

Theorem fsem02ChoicePeerFirstRefusedClientThenValidRetry :
  forall owners clientOccurrence clientProcess clientEndpoint
    peerOccurrence peerProcess peerEndpoint
    afterClient afterForward afterPeer afterReverse,
    clientOccurrence <> peerOccurrence ->
    fsem02RetireSelectedClientOwner owners
      clientOccurrence clientProcess clientEndpoint = Some afterClient ->
    fsem02RetireExplicitPeerEnd afterClient
      peerOccurrence peerProcess peerEndpoint = Some afterForward ->
    fsem02RetireExplicitPeerEnd owners
      peerOccurrence peerProcess peerEndpoint = Some afterPeer ->
    fsem02RetireSelectedClientOwner afterPeer
      clientOccurrence clientProcess clientEndpoint = Some afterReverse ->
    fsem02ChoiceTrialClientAfterPeer false afterPeer
      clientOccurrence clientProcess clientEndpoint = None /\
    fsem02ChoiceTrialClientAfterPeer true afterPeer
      clientOccurrence clientProcess clientEndpoint = Some afterReverse /\
    afterPeer peerOccurrence = None /\
    afterPeer clientOccurrence = Some (clientProcess, clientEndpoint) /\
    (forall spectator, spectator <> peerOccurrence ->
      afterPeer spectator = owners spectator) /\
    (forall observed, afterForward observed = afterReverse observed).
Proof.
  intros owners co cp ce po pp pe ac af ap ar
    Hdistinct Hclient Hpeer HpeerFirst HclientSecond.
  pose proof (fsem02SelectedClientCloseExactRetirementAndFrame
    owners po pp pe ap HpeerFirst) as [Hgone Hframe].
  pose proof (fsem02SelectedClientCloseRequiresExactOwner
    ap co cp ce ar HclientSecond) as HclientLive.
  pose proof (fsem02ConditionalTerminalCloseDiamond
    owners co cp ce po pp pe ac af ap ar
    Hdistinct Hclient Hpeer HpeerFirst HclientSecond) as Hdiamond.
  repeat split.
  - reflexivity.
  - simpl. exact HclientSecond.
  - exact Hgone.
  - exact HclientLive.
  - intros spectator Hother. apply Hframe. exact Hother.
  - exact Hdiamond.
Qed.
