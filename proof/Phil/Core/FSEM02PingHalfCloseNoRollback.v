From Phil.Core Require Import Syntax Context SessionStep
  FSEM02ProtocolHeadProgression FSEM02PingJointCloseDiamond
  FSEM02PingCloseRefusalRetry.
From Stdlib Require Import Strings.String.

(* FSEM-02, non-normative. Unlike two refused trials, a successful first
   local Close is COMMITTED. Rejecting the live peer's wrong outcome cannot
   restore the retired endpoint. Nominal admission remains an external input. *)

Definition fsem02PingClientCommittedServerRefused
  (outcome badOutcome : Outcome) (clientHead serverHead : Session)
  (clientEndpoint serverEndpoint : Name)
  (clientBefore serverBefore : ResourceContext)
  : option (ResourceContext * ResourceContext) :=
  match fsem02PingTryClientClose true outcome clientHead clientEndpoint
          clientBefore serverBefore with
  | FSEM02PingCloseRefused _ _ => None
  | FSEM02PingCloseCommitted clientAfter serverUnchanged =>
      match fsem02PingTryServerClose false badOutcome serverHead serverEndpoint
              clientAfter serverUnchanged with
      | FSEM02PingCloseRefused clientStill serverStill =>
          Some (clientStill, serverStill)
      | FSEM02PingCloseCommitted _ _ => None
      end
  end.

Definition fsem02PingServerCommittedClientRefused
  (outcome badOutcome : Outcome) (clientHead serverHead : Session)
  (clientEndpoint serverEndpoint : Name)
  (clientBefore serverBefore : ResourceContext)
  : option (ResourceContext * ResourceContext) :=
  match fsem02PingTryServerClose true outcome serverHead serverEndpoint
          clientBefore serverBefore with
  | FSEM02PingCloseRefused _ _ => None
  | FSEM02PingCloseCommitted clientUnchanged serverAfter =>
      match fsem02PingTryClientClose false badOutcome clientHead clientEndpoint
              clientUnchanged serverAfter with
      | FSEM02PingCloseRefused clientStill serverStill =>
          Some (clientStill, serverStill)
      | FSEM02PingCloseCommitted _ _ => None
      end
  end.

Theorem fsem02PingClientCommitThenPeerRefusalRetainsCommit :
  forall good bad ch sh ce se cb sb ca,
    fsem02Progression (FSEM02Close good) ch ce ce cb = StepSucceeded ca ->
    fsem02PingClientCommittedServerRefused good bad ch sh ce se cb sb =
      Some (ca, sb).
Proof.
  intros good bad ch sh ce se cb sb ca Hcommit.
  unfold fsem02PingClientCommittedServerRefused,
    fsem02PingTryClientClose, fsem02PingTryServerClose.
  now rewrite Hcommit.
Qed.

Theorem fsem02PingServerCommitThenPeerRefusalRetainsCommit :
  forall good bad ch sh ce se cb sb sa,
    fsem02Progression (FSEM02Close good) sh se se sb = StepSucceeded sa ->
    fsem02PingServerCommittedClientRefused good bad ch sh ce se cb sb =
      Some (cb, sa).
Proof.
  intros good bad ch sh ce se cb sb sa Hcommit.
  unfold fsem02PingServerCommittedClientRefused,
    fsem02PingTryServerClose, fsem02PingTryClientClose.
  now rewrite Hcommit.
Qed.

Lemma fsem02PingStaleHalfCloseStepFails :
  forall outcome head endpoint context,
    linearBindings context endpoint = None ->
    fsem02Progression (FSEM02Close outcome) head endpoint endpoint context =
      StepFailed.
Proof.
  intros outcome head endpoint context Hmissing.
  destruct (fsem02Progression (FSEM02Close outcome) head
    endpoint endpoint context) as [| next] eqn:Hstep.
  - reflexivity.
  - exfalso.
    exact (stale_linear_predecessor_cannot_succeed
      (FSEM02Close outcome) head endpoint endpoint context next
      Hmissing Hstep).
Qed.

Theorem fsem02PingAdmittedHalfCloseConsumesEndpointAndFramesLoans :
  forall outcome endpoint before after,
    fsem02Progression (FSEM02Close outcome) (End outcome)
      endpoint endpoint before = StepSucceeded after ->
    linearBindings after endpoint = None /\
    sharedLoans after = sharedLoans before.
Proof.
  intros outcome endpoint before after Hcommit.
  assert (Hselected :
    selectedContinuation (FSEM02Close outcome) (End outcome) = Some None).
  { simpl. rewrite String.eqb_refl. reflexivity. }
  pose proof (matched_terminal_close_consumes_without_successor
    (FSEM02Close outcome) (End outcome) endpoint endpoint before after
    Hselected Hcommit) as Hresources.
  destruct Hresources as [_ [Hgone [_ Hloans]]].
  split; assumption.
Qed.

Theorem fsem02PingCommittedClientStaleRetryRefuses :
  forall outcome replay endpoint before after peer,
    fsem02Progression (FSEM02Close outcome) (End outcome)
      endpoint endpoint before = StepSucceeded after ->
    fsem02PingTryClientClose true replay (End outcome) endpoint after peer =
      FSEM02PingCloseRefused after peer.
Proof.
  intros outcome replay endpoint before after peer Hcommit.
  pose proof (fsem02PingAdmittedHalfCloseConsumesEndpointAndFramesLoans
    outcome endpoint before after Hcommit) as [Hgone _].
  unfold fsem02PingTryClientClose.
  rewrite (fsem02PingStaleHalfCloseStepFails
    replay (End outcome) endpoint after Hgone).
  reflexivity.
Qed.

Theorem fsem02PingCommittedServerStaleRetryRefuses :
  forall outcome replay endpoint before after peer,
    fsem02Progression (FSEM02Close outcome) (End outcome)
      endpoint endpoint before = StepSucceeded after ->
    fsem02PingTryServerClose true replay (End outcome) endpoint peer after =
      FSEM02PingCloseRefused peer after.
Proof.
  intros outcome replay endpoint before after peer Hcommit.
  pose proof (fsem02PingAdmittedHalfCloseConsumesEndpointAndFramesLoans
    outcome endpoint before after Hcommit) as [Hgone _].
  unfold fsem02PingTryServerClose.
  rewrite (fsem02PingStaleHalfCloseStepFails
    replay (End outcome) endpoint after Hgone).
  reflexivity.
Qed.

Theorem fsem02PingClientCommittedPeerCanFinish :
  forall outcome ch sh ce se cb sb ca sa,
    fsem02PingClientThenServerClose outcome ch sh ce se cb sb =
      Some (ca, sa) ->
    fsem02PingTryServerClose true outcome sh se ca sb =
      FSEM02PingCloseCommitted ca sa.
Proof.
  intros outcome ch sh ce se cb sb ca sa Hpair.
  pose proof (fsem02PingJointCloseSuccessProjectsBoth
    outcome ch sh ce se cb sb ca sa Hpair) as [_ Hserver].
  unfold fsem02PingTryServerClose.
  now rewrite Hserver.
Qed.

Theorem fsem02PingServerCommittedPeerCanFinish :
  forall outcome ch sh ce se cb sb ca sa,
    fsem02PingServerThenClientClose outcome ch sh ce se cb sb =
      Some (ca, sa) ->
    fsem02PingTryClientClose true outcome ch ce cb sa =
      FSEM02PingCloseCommitted ca sa.
Proof.
  intros outcome ch sh ce se cb sb ca sa Hpair.
  rewrite <- fsem02PingJointTerminalCloseDiamond in Hpair.
  pose proof (fsem02PingJointCloseSuccessProjectsBoth
    outcome ch sh ce se cb sb ca sa Hpair) as [Hclient _].
  unfold fsem02PingTryClientClose.
  now rewrite Hclient.
Qed.
