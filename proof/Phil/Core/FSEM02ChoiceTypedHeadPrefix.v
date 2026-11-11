From Stdlib Require Import Strings.String.
From Phil.Core Require Import
  Syntax Context SessionStep FSEM02ProtocolHeadProgression
  FSEM02JointSourceChoice FSEM02StatefulSourceChoice
  FSEM02SelectedClientClose FSEM02ExplicitPeerClose
  FSEM02ChoiceClosePrefixLedgers.

(*
  NON-NORMATIVE FSEM-02: exact modeled Select/Offer continuation heads and
  both one-sided End owner prefixes. All admitted source/protocol/activation,
  distinct occurrence, End authorization and valid predecessor conditions
  are explicit premises. The Haskell adapter separately executes the actual
  local Core protocol checker from the ORIGINAL activation context and compares
  all native process contexts; this proof does not establish Haskell refinement.
*)

Theorem fsem02ChoiceTypedEndHeadsAndBothPrefixes :
  forall sourceLabels branches chosen peer clientOld clientNext
         offerOld offerNext clientContext offerContext owners
         clientOccurrence offerOccurrence clientProcess offerProcess
         clientReady offerReady afterChoice afterClient afterForward
         afterPeer afterReverse outcome,
    offeredContinuation chosen branches = Some (End outcome) ->
    clientOccurrence <> offerOccurrence ->
    fsem02StatefulSourceChoice sourceLabels branches chosen peer
      clientOld clientNext offerOld offerNext clientContext offerContext
      owners clientOccurrence offerOccurrence clientProcess offerProcess =
      Some ((clientReady, offerReady), afterChoice) ->
    fsem02RetireSelectedClientOwner afterChoice
      clientOccurrence clientProcess clientNext = Some afterClient ->
    fsem02RetireExplicitPeerEnd afterClient
      offerOccurrence offerProcess offerNext = Some afterForward ->
    fsem02RetireExplicitPeerEnd afterChoice
      offerOccurrence offerProcess offerNext = Some afterPeer ->
    fsem02RetireSelectedClientOwner afterPeer
      clientOccurrence clientProcess clientNext = Some afterReverse ->
    String.eqb chosen peer = true /\
    linearBindings clientReady clientOld = None /\
    linearBindings clientReady clientNext = Some (endpointType (End outcome)) /\
    linearBindings offerReady offerOld = None /\
    linearBindings offerReady offerNext = Some (endpointType (End outcome)) /\
    afterClient clientOccurrence = None /\
    afterClient offerOccurrence = Some (offerProcess, offerNext) /\
    afterPeer clientOccurrence = Some (clientProcess, clientNext) /\
    afterPeer offerOccurrence = None /\
    (forall spectator,
      spectator <> clientOccurrence ->
      spectator <> offerOccurrence ->
      afterClient spectator = owners spectator /\
      afterPeer spectator = owners spectator) /\
    (forall observed, afterForward observed = afterReverse observed).
Proof.
  intros sourceLabels branches chosen peer clientOld clientNext
    offerOld offerNext clientContext offerContext owners
    clientOccurrence offerOccurrence clientProcess offerProcess
    clientReady offerReady afterChoice afterClient afterForward
    afterPeer afterReverse outcome Hbranch Hdistinct Hchoice
    HclientClose HpeerClose HpeerFirst HclientSecond.
  pose proof (fsem02StatefulSourceChoiceSuccessIsJointAndExactOwners
    sourceLabels branches chosen peer clientOld clientNext offerOld offerNext
    clientContext offerContext owners clientOccurrence offerOccurrence
    clientProcess offerProcess clientReady offerReady afterChoice Hchoice)
    as [Hjoint _].
  pose proof (fsem02JointSourceChoiceSuccessConsumesBothExactPredecessors
    sourceLabels branches chosen peer clientOld clientNext offerOld offerNext
    clientContext offerContext clientReady offerReady (End outcome)
    Hbranch Hjoint)
    as [Hpeer [HclientOld [HclientNext [HofferOld HofferNext]]]].
  pose proof (fsem02ChoiceSourceBothOneSidedClosePrefixes
    sourceLabels branches chosen peer clientOld clientNext offerOld offerNext
    clientContext offerContext owners clientOccurrence offerOccurrence
    clientProcess offerProcess clientReady offerReady afterChoice afterClient
    afterForward afterPeer afterReverse Hdistinct Hchoice HclientClose
    HpeerClose HpeerFirst HclientSecond)
    as [HclientGone [HofferLive [HclientLive [HofferGone [Hframe Hdiamond]]]]].
  repeat split; assumption.
Qed.

(* A source-listed peer label cannot turn an absent protocol branch into
   a successful local Select/Offer transition. This is a rejection, not an
   invented alternate continuation or a source-level disposal authority. *)
Theorem fsem02ChoiceTypedHeadRejectsMissingBranch :
  forall sourceLabels branches chosen peer clientOld clientNext
         offerOld offerNext clientContext offerContext owners
         clientOccurrence offerOccurrence clientProcess offerProcess,
    offeredContinuation chosen branches = None ->
    fsem02StatefulSourceChoice sourceLabels branches chosen peer
      clientOld clientNext offerOld offerNext clientContext offerContext
      owners clientOccurrence offerOccurrence clientProcess offerProcess = None.
Proof.
  intros sourceLabels branches chosen peer clientOld clientNext
    offerOld offerNext clientContext offerContext owners
    clientOccurrence offerOccurrence clientProcess offerProcess Hmissing.
  unfold fsem02StatefulSourceChoice, fsem02JointSourceChoice.
  destruct (String.eqb chosen peer); [|reflexivity].
  destruct (fsem02SourceContainsLabel chosen sourceLabels); [|reflexivity].
  rewrite (unavailable_select_branch_rejects
    chosen branches clientOld clientNext clientContext Hmissing).
  reflexivity.
Qed.
