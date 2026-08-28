From Phil.Core Require Import Syntax Session ProtocolIdentity.

(*
  PHIL-PROT-PROJ-001 — protocol projection and session-polymorphic endpoint use.

  This theorem family deliberately composes already-certified boundaries rather
  than rebuilding them:

  - PHIL-PROT-ID-001 supplies exact protocol instance / role / local-session
    identity and action gating;
  - PHIL-SESSION-DUAL-001 supplies exact binary session duality;
  - PHIL-GEN-INST-001 supplies the accepted generic-instantiation witness used
    below as an opaque premise.

  The protocol-specific claims proved here are:

  - an accepted binary protocol instance retains the exact accepted generic
    discharge and exact protocol-instance revision;
  - the primary projection is the exact instantiated local session and the peer
    projection is its exact dependent dual;
  - undeclared roles do not project, and projection evidence is tied to the
    exact protocol instance and exact role-local session;
  - moving an endpoint occurrence is shape-parametric and preserves its exact
    semantic contract, including an abstract SessionVar;
  - a bare SessionVar exposes no concrete communication head, so generic
    possession alone does not authorize communication;
  - communication after abstraction requires an explicit accepted session
    constraint exposing a concrete head, while exact instance/role identity
    remains unchanged.

  Concrete generic-argument substitution, Haskell Text/Map representation, and
  the implementation of accepted session constraints remain correspondence
  boundaries rather than being silently assumed by this normalized theorem.
*)

Parameter GenericInstantiationWitness : Type.
Parameter AcceptedSessionConstraint : Session -> Session -> Prop.

Record BinaryProtocolInstance : Type := {
  protocolInstanceGenericDischarge : GenericInstantiationWitness;
  binaryProtocolInstanceRevision : ProtocolInstanceRevision;
  binaryProtocolPrimaryRole : ProtocolRoleKey;
  binaryProtocolPeerRole : ProtocolRoleKey;
  binaryProtocolPrimarySession : Session;
  binaryProtocolPeerSession : Session
}.

Definition BinaryInstanceWellFormed
  (instance : BinaryProtocolInstance) : Prop :=
  binaryProtocolPrimaryRole instance <> binaryProtocolPeerRole instance /\
  binaryProtocolPeerSession instance =
    dualSession (binaryProtocolPrimarySession instance).

Definition ExactBinaryInstantiation
  (discharge : GenericInstantiationWitness)
  (revision : ProtocolInstanceRevision)
  (primaryRole peerRole : ProtocolRoleKey)
  (primarySession : Session)
  (instance : BinaryProtocolInstance) : Prop :=
  BinaryInstanceWellFormed instance /\
  protocolInstanceGenericDischarge instance = discharge /\
  binaryProtocolInstanceRevision instance = revision /\
  binaryProtocolPrimaryRole instance = primaryRole /\
  binaryProtocolPeerRole instance = peerRole /\
  binaryProtocolPrimarySession instance = primarySession.

Definition ProjectProtocolRole
  (instance : BinaryProtocolInstance)
  (role : ProtocolRoleKey)
  (session : Session) : Prop :=
  (role = binaryProtocolPrimaryRole instance /\
   session = binaryProtocolPrimarySession instance) \/
  (role = binaryProtocolPeerRole instance /\
   session = binaryProtocolPeerSession instance).

Record ProtocolProjectionEvidence : Type := {
  projectionEvidenceInstance : ProtocolInstanceRevision;
  projectionEvidenceRole : ProtocolRoleKey;
  projectionEvidenceSession : Session
}.

Definition ProjectionEvidenceAccepted
  (instance : BinaryProtocolInstance)
  (evidence : ProtocolProjectionEvidence) : Prop :=
  projectionEvidenceInstance evidence = binaryProtocolInstanceRevision instance /\
  ProjectProtocolRole
    instance
    (projectionEvidenceRole evidence)
    (projectionEvidenceSession evidence).

Theorem exact_instantiation_preserves_generic_discharge :
  forall discharge revision primaryRole peerRole primarySession instance,
    ExactBinaryInstantiation
      discharge revision primaryRole peerRole primarySession instance ->
    protocolInstanceGenericDischarge instance = discharge.
Proof.
  intros discharge revision primaryRole peerRole primarySession instance Hinst.
  unfold ExactBinaryInstantiation in Hinst.
  destruct Hinst as [_ [Hdischarge _]].
  exact Hdischarge.
Qed.

Theorem exact_instantiation_preserves_protocol_revision :
  forall discharge revision primaryRole peerRole primarySession instance,
    ExactBinaryInstantiation
      discharge revision primaryRole peerRole primarySession instance ->
    binaryProtocolInstanceRevision instance = revision.
Proof.
  intros discharge revision primaryRole peerRole primarySession instance Hinst.
  unfold ExactBinaryInstantiation in Hinst.
  destruct Hinst as [_ [_ [Hrevision _]]].
  exact Hrevision.
Qed.

Theorem instantiated_primary_role_projects_exact_session :
  forall discharge revision primaryRole peerRole primarySession instance,
    ExactBinaryInstantiation
      discharge revision primaryRole peerRole primarySession instance ->
    ProjectProtocolRole instance primaryRole primarySession.
Proof.
  intros discharge revision primaryRole peerRole primarySession instance Hinst.
  unfold ExactBinaryInstantiation in Hinst.
  destruct Hinst as
    [_ [_ [_ [HprimaryRole [_ HprimarySession]]]]].
  unfold ProjectProtocolRole.
  left.
  split.
  - symmetry. exact HprimaryRole.
  - symmetry. exact HprimarySession.
Qed.

Theorem instantiated_peer_role_projects_exact_dual :
  forall discharge revision primaryRole peerRole primarySession instance,
    ExactBinaryInstantiation
      discharge revision primaryRole peerRole primarySession instance ->
    ProjectProtocolRole instance peerRole (dualSession primarySession).
Proof.
  intros discharge revision primaryRole peerRole primarySession instance Hinst.
  unfold ExactBinaryInstantiation in Hinst.
  destruct Hinst as
    [[_ Hdual] [_ [_ [_ [HpeerRole HprimarySession]]]]].
  unfold ProjectProtocolRole.
  right.
  split.
  - symmetry. exact HpeerRole.
  - rewrite <- HprimarySession.
    symmetry.
    exact Hdual.
Qed.

Theorem instantiated_role_sessions_are_exact_duals :
  forall discharge revision primaryRole peerRole primarySession instance,
    ExactBinaryInstantiation
      discharge revision primaryRole peerRole primarySession instance ->
    binaryProtocolPeerSession instance =
      dualSession (binaryProtocolPrimarySession instance) /\
    binaryProtocolPrimarySession instance =
      dualSession (binaryProtocolPeerSession instance).
Proof.
  intros discharge revision primaryRole peerRole primarySession instance Hinst.
  unfold ExactBinaryInstantiation in Hinst.
  destruct Hinst as [[_ Hdual] _].
  split.
  - exact Hdual.
  - rewrite Hdual.
    symmetry.
    apply dualSession_involutive.
Qed.

Theorem undeclared_role_cannot_project :
  forall instance role session,
    role <> binaryProtocolPrimaryRole instance ->
    role <> binaryProtocolPeerRole instance ->
    ~ ProjectProtocolRole instance role session.
Proof.
  intros instance role session HnotPrimary HnotPeer Hprojection.
  unfold ProjectProtocolRole in Hprojection.
  destruct Hprojection as [[Hprimary _] | [Hpeer _]].
  - apply HnotPrimary. exact Hprimary.
  - apply HnotPeer. exact Hpeer.
Qed.

Theorem projection_is_unique_for_well_formed_instance :
  forall instance role leftSession rightSession,
    BinaryInstanceWellFormed instance ->
    ProjectProtocolRole instance role leftSession ->
    ProjectProtocolRole instance role rightSession ->
    leftSession = rightSession.
Proof.
  intros instance role leftSession rightSession Hwell Hleft Hright.
  unfold BinaryInstanceWellFormed in Hwell.
  destruct Hwell as [HrolesDistinct _].
  unfold ProjectProtocolRole in Hleft, Hright.
  destruct Hleft as [[HleftRole HleftSession] | [HleftRole HleftSession]];
  destruct Hright as [[HrightRole HrightSession] | [HrightRole HrightSession]].
  - rewrite HleftSession, HrightSession. reflexivity.
  - exfalso.
    apply HrolesDistinct.
    rewrite <- HleftRole.
    exact HrightRole.
  - exfalso.
    apply HrolesDistinct.
    rewrite <- HrightRole.
    exact HleftRole.
  - rewrite HleftSession, HrightSession. reflexivity.
Qed.

Theorem projection_evidence_requires_exact_instance :
  forall instance evidence,
    ProjectionEvidenceAccepted instance evidence ->
    projectionEvidenceInstance evidence = binaryProtocolInstanceRevision instance.
Proof.
  intros instance evidence Haccepted.
  unfold ProjectionEvidenceAccepted in Haccepted.
  exact (proj1 Haccepted).
Qed.

Theorem cross_instance_projection_evidence_rejects :
  forall instance evidence,
    projectionEvidenceInstance evidence <>
      binaryProtocolInstanceRevision instance ->
    ~ ProjectionEvidenceAccepted instance evidence.
Proof.
  intros instance evidence Hdifferent Haccepted.
  apply Hdifferent.
  eapply projection_evidence_requires_exact_instance.
  exact Haccepted.
Qed.

Theorem accepted_projection_evidence_has_unique_session :
  forall instance evidence expectedSession,
    BinaryInstanceWellFormed instance ->
    ProjectionEvidenceAccepted instance evidence ->
    ProjectProtocolRole instance (projectionEvidenceRole evidence) expectedSession ->
    projectionEvidenceSession evidence = expectedSession.
Proof.
  intros instance evidence expectedSession Hwell Haccepted Hexpected.
  unfold ProjectionEvidenceAccepted in Haccepted.
  destruct Haccepted as [_ Hactual].
  eapply projection_is_unique_for_well_formed_instance.
  - exact Hwell.
  - exact Hactual.
  - exact Hexpected.
Qed.

Definition transferProtocolEndpoint
  (endpoint : ProtocolEndpointOccurrence)
  (successor : ProtocolOccurrenceName) : ProtocolEndpointOccurrence :=
  {| protocolOccurrenceName := successor;
     protocolOccurrenceContract := protocolOccurrenceContract endpoint |}.

Theorem generic_endpoint_transfer_preserves_exact_contract :
  forall endpoint successor,
    protocolOccurrenceContract (transferProtocolEndpoint endpoint successor) =
      protocolOccurrenceContract endpoint.
Proof.
  intros endpoint successor.
  reflexivity.
Qed.

Theorem generic_endpoint_transfer_preserves_abstract_session :
  forall endpoint successor variable,
    protocolContractSession (protocolOccurrenceContract endpoint) =
      SessionVar variable ->
    protocolContractSession
      (protocolOccurrenceContract (transferProtocolEndpoint endpoint successor)) =
      SessionVar variable.
Proof.
  intros endpoint successor variable Habstract.
  simpl.
  exact Habstract.
Qed.

Theorem generic_endpoint_transfer_preserves_instance_and_role :
  forall endpoint successor,
    protocolContractInstance
      (protocolOccurrenceContract (transferProtocolEndpoint endpoint successor)) =
      protocolContractInstance (protocolOccurrenceContract endpoint) /\
    protocolContractRole
      (protocolOccurrenceContract (transferProtocolEndpoint endpoint successor)) =
      protocolContractRole (protocolOccurrenceContract endpoint).
Proof.
  intros endpoint successor.
  split; reflexivity.
Qed.

Inductive ConcreteCommunicationHead : Session -> Prop :=
| ConcreteSendHead : forall binder messageTy continuation,
    ConcreteCommunicationHead (Send binder messageTy continuation)
| ConcreteReceiveHead : forall binder messageTy continuation,
    ConcreteCommunicationHead (Receive binder messageTy continuation)
| ConcreteSelectHead : forall branches,
    ConcreteCommunicationHead (Select branches)
| ConcreteOfferHead : forall branches,
    ConcreteCommunicationHead (Offer branches)
| ConcreteEndHead : forall outcome,
    ConcreteCommunicationHead (End outcome).

Definition GenericEndpointActionAllowed
  (request : ProtocolActionRequest)
  (endpoint : ProtocolEndpointOccurrence) : Prop :=
  ConcreteCommunicationHead
    (protocolContractSession (protocolOccurrenceContract endpoint)) /\
  ProtocolActionAllowed request endpoint.

Theorem session_variable_exposes_no_concrete_communication_head :
  forall variable,
    ~ ConcreteCommunicationHead (SessionVar variable).
Proof.
  intros variable Hhead.
  inversion Hhead.
Qed.

Theorem unconstrained_session_variable_cannot_perform_protocol_action :
  forall request endpoint variable,
    protocolContractSession (protocolOccurrenceContract endpoint) =
      SessionVar variable ->
    ~ GenericEndpointActionAllowed request endpoint.
Proof.
  intros request endpoint variable Habstract Hallowed.
  unfold GenericEndpointActionAllowed in Hallowed.
  destruct Hallowed as [Hhead _].
  rewrite Habstract in Hhead.
  inversion Hhead.
Qed.

Definition ConstrainedGenericEndpointActionAllowed
  (request : ProtocolActionRequest)
  (endpoint : ProtocolEndpointOccurrence) : Prop :=
  exists concreteSession,
    AcceptedSessionConstraint
      (protocolContractSession (protocolOccurrenceContract endpoint))
      concreteSession /\
    ConcreteCommunicationHead concreteSession /\
    requestProtocolInstance request =
      protocolContractInstance (protocolOccurrenceContract endpoint) /\
    requestProtocolRole request =
      protocolContractRole (protocolOccurrenceContract endpoint) /\
    LocalActionAllowed concreteSession (requestProtocolAction request).

Theorem generic_communication_after_abstraction_requires_explicit_constraint :
  forall request endpoint,
    ConstrainedGenericEndpointActionAllowed request endpoint ->
    exists concreteSession,
      AcceptedSessionConstraint
        (protocolContractSession (protocolOccurrenceContract endpoint))
        concreteSession /\
      ConcreteCommunicationHead concreteSession /\
      LocalActionAllowed concreteSession (requestProtocolAction request).
Proof.
  intros request endpoint Hallowed.
  unfold ConstrainedGenericEndpointActionAllowed in Hallowed.
  destruct Hallowed as
    [concreteSession [Hconstraint [Hhead [_ [_ Hlocal]]]]].
  exists concreteSession.
  repeat split; assumption.
Qed.

Theorem constrained_generic_action_preserves_exact_protocol_identity :
  forall request endpoint,
    ConstrainedGenericEndpointActionAllowed request endpoint ->
    requestProtocolInstance request =
      protocolContractInstance (protocolOccurrenceContract endpoint) /\
    requestProtocolRole request =
      protocolContractRole (protocolOccurrenceContract endpoint).
Proof.
  intros request endpoint Hallowed.
  unfold ConstrainedGenericEndpointActionAllowed in Hallowed.
  destruct Hallowed as
    [concreteSession [_ [_ [Hinstance [Hrole _]]]]].
  split; assumption.
Qed.
