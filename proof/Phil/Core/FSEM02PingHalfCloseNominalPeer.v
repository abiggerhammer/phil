From Phil.Core Require Import Syntax Context SessionStep
  FSEM02ProtocolHeadProgression FSEM02PingCloseRefusalRetry
  FSEM02PingHalfCloseNoRollback.

(* NON-NORMATIVE FSEM-02. A committed local End Close is irreversible in
   this bounded two-context model. Exact peer protocol-instance and role
   admission are externally supplied facts, not derived from matching local
   Session syntax. A refused peer request never creates a checked step. *)

Inductive FSEM02PingPeerNominalDecision : Type :=
| FSEM02PeerInstanceRefused
| FSEM02PeerRoleRefused
| FSEM02PeerNominalAccepted.

Definition fsem02PingPeerNominalGate
  (peerInstanceOK peerRoleOK : bool) : FSEM02PingPeerNominalDecision :=
  if peerInstanceOK then
    if peerRoleOK then FSEM02PeerNominalAccepted
    else FSEM02PeerRoleRefused
  else FSEM02PeerInstanceRefused.

(* None denotes either a failed first Close or an in-scope peer trial that
   is nominally admitted and therefore not represented as a refusal here.
   It is NOT a successful peer Close or a terminal-root assertion. *)
Definition fsem02PingClientCommittedPeerNominalRefusal
  (peerInstanceOK peerRoleOK : bool) (outcome : Outcome)
  (clientEndpoint : Name) (clientBefore serverBefore : ResourceContext)
  : option (FSEM02PingPeerNominalDecision * (ResourceContext * ResourceContext)) :=
  match fsem02Progression (FSEM02Close outcome) (End outcome)
          clientEndpoint clientEndpoint clientBefore with
  | StepFailed => None
  | StepSucceeded clientAfter =>
      match fsem02PingPeerNominalGate peerInstanceOK peerRoleOK with
      | FSEM02PeerNominalAccepted => None
      | refusal => Some (refusal, (clientAfter, serverBefore))
      end
  end.

Definition fsem02PingServerCommittedPeerNominalRefusal
  (peerInstanceOK peerRoleOK : bool) (outcome : Outcome)
  (serverEndpoint : Name) (clientBefore serverBefore : ResourceContext)
  : option (FSEM02PingPeerNominalDecision * (ResourceContext * ResourceContext)) :=
  match fsem02Progression (FSEM02Close outcome) (End outcome)
          serverEndpoint serverEndpoint serverBefore with
  | StepFailed => None
  | StepSucceeded serverAfter =>
      match fsem02PingPeerNominalGate peerInstanceOK peerRoleOK with
      | FSEM02PeerNominalAccepted => None
      | refusal => Some (refusal, (clientBefore, serverAfter))
      end
  end.

Theorem fsem02PingClientCommittedInstanceRefusalRetainsStateAndLoan :
  forall outcome endpoint clientBefore serverBefore clientAfter peerRoleOK,
    fsem02Progression (FSEM02Close outcome) (End outcome)
      endpoint endpoint clientBefore = StepSucceeded clientAfter ->
    fsem02PingClientCommittedPeerNominalRefusal false peerRoleOK
      outcome endpoint clientBefore serverBefore =
        Some (FSEM02PeerInstanceRefused, (clientAfter, serverBefore)) /\
    linearBindings clientAfter endpoint = None /\
    sharedLoans clientAfter = sharedLoans clientBefore.
Proof.
  intros outcome endpoint cb sb ca peerRoleOK Hcommit.
  pose proof (fsem02PingAdmittedHalfCloseConsumesEndpointAndFramesLoans
    outcome endpoint cb ca Hcommit) as [Hgone Hloan].
  split.
  - unfold fsem02PingClientCommittedPeerNominalRefusal.
    now rewrite Hcommit.
  - split; assumption.
Qed.

Theorem fsem02PingServerCommittedInstanceRefusalRetainsStateAndLoan :
  forall outcome endpoint clientBefore serverBefore serverAfter peerRoleOK,
    fsem02Progression (FSEM02Close outcome) (End outcome)
      endpoint endpoint serverBefore = StepSucceeded serverAfter ->
    fsem02PingServerCommittedPeerNominalRefusal false peerRoleOK
      outcome endpoint clientBefore serverBefore =
        Some (FSEM02PeerInstanceRefused, (clientBefore, serverAfter)) /\
    linearBindings serverAfter endpoint = None /\
    sharedLoans serverAfter = sharedLoans serverBefore.
Proof.
  intros outcome endpoint cb sb sa peerRoleOK Hcommit.
  pose proof (fsem02PingAdmittedHalfCloseConsumesEndpointAndFramesLoans
    outcome endpoint sb sa Hcommit) as [Hgone Hloan].
  split.
  - unfold fsem02PingServerCommittedPeerNominalRefusal.
    now rewrite Hcommit.
  - split; assumption.
Qed.

Theorem fsem02PingClientCommittedRoleRefusalPreservesPeer :
  forall outcome endpoint clientBefore serverBefore clientAfter,
    fsem02Progression (FSEM02Close outcome) (End outcome)
      endpoint endpoint clientBefore = StepSucceeded clientAfter ->
    fsem02PingClientCommittedPeerNominalRefusal true false
      outcome endpoint clientBefore serverBefore =
      Some (FSEM02PeerRoleRefused, (clientAfter, serverBefore)).
Proof.
  intros outcome endpoint cb sb ca Hcommit.
  unfold fsem02PingClientCommittedPeerNominalRefusal.
  now rewrite Hcommit.
Qed.

Theorem fsem02PingServerCommittedRoleRefusalPreservesPeer :
  forall outcome endpoint clientBefore serverBefore serverAfter,
    fsem02Progression (FSEM02Close outcome) (End outcome)
      endpoint endpoint serverBefore = StepSucceeded serverAfter ->
    fsem02PingServerCommittedPeerNominalRefusal true false
      outcome endpoint clientBefore serverBefore =
      Some (FSEM02PeerRoleRefused, (clientBefore, serverAfter)).
Proof.
  intros outcome endpoint cb sb sa Hcommit.
  unfold fsem02PingServerCommittedPeerNominalRefusal.
  now rewrite Hcommit.
Qed.

Theorem fsem02PingPeerInstancePrecedesRole :
  fsem02PingPeerNominalGate false false = FSEM02PeerInstanceRefused.
Proof. reflexivity. Qed.

Theorem fsem02PingClientFirstNominalRefusalThenValidPeerClose :
  forall outcome ce se cb sb ca sa peerRoleOK,
    fsem02Progression (FSEM02Close outcome) (End outcome)
      ce ce cb = StepSucceeded ca ->
    fsem02Progression (FSEM02Close outcome) (End outcome)
      se se sb = StepSucceeded sa ->
    fsem02PingClientCommittedPeerNominalRefusal false peerRoleOK
      outcome ce cb sb =
        Some (FSEM02PeerInstanceRefused, (ca, sb)) /\
    fsem02PingTryServerClose true outcome (End outcome) se ca sb =
      FSEM02PingCloseCommitted ca sa.
Proof.
  intros outcome ce se cb sb ca sa peerRoleOK Hclient Hserver.
  split.
  - unfold fsem02PingClientCommittedPeerNominalRefusal.
    now rewrite Hclient.
  - unfold fsem02PingTryServerClose.
    now rewrite Hserver.
Qed.

Theorem fsem02PingServerFirstNominalRefusalThenValidPeerClose :
  forall outcome ce se cb sb ca sa peerRoleOK,
    fsem02Progression (FSEM02Close outcome) (End outcome)
      ce ce cb = StepSucceeded ca ->
    fsem02Progression (FSEM02Close outcome) (End outcome)
      se se sb = StepSucceeded sa ->
    fsem02PingServerCommittedPeerNominalRefusal false peerRoleOK
      outcome se cb sb =
        Some (FSEM02PeerInstanceRefused, (cb, sa)) /\
    fsem02PingTryClientClose true outcome (End outcome) ce cb sa =
      FSEM02PingCloseCommitted ca sa.
Proof.
  intros outcome ce se cb sb ca sa peerRoleOK Hclient Hserver.
  split.
  - unfold fsem02PingServerCommittedPeerNominalRefusal.
    now rewrite Hserver.
  - unfold fsem02PingTryClientClose.
    now rewrite Hclient.
Qed.
