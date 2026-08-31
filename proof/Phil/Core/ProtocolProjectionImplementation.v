From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import ProtocolProjection.

Set Implicit Arguments.

(*
  PHIL-PROT-PROJ-001 — representation-neutral implementation correspondence.

  Production owns concrete Map/Text/Session lookup and equality, generic-family
  substitution, generic discharge, and resource-context transfer.  This layer
  owns the protocol-specific semantic choices that are reflected from those
  native facts:

  - only a declared protocol role may project;
  - projection evidence must bind the exact protocol instance revision;
  - projection evidence must bind the exact selected local Session; and
  - successful projection/transfer construction preserves the exact semantic
    coordinates rather than inferring identity from equal-looking shape.

  SessionVar communication rejection and accepted-session-constraint truth stay
  with the already-Certified Session/protocol predecessors rather than being
  silently reimplemented here.
*)

Inductive DeclaredProjectionRoleDecision : Type :=
| DeclaredProjectionRoleAccepted
| UndeclaredProjectionRoleRejected.

Definition decideDeclaredProjectionRoleByFact
  (roleDeclared : bool) : DeclaredProjectionRoleDecision :=
  if roleDeclared then
    DeclaredProjectionRoleAccepted
  else
    UndeclaredProjectionRoleRejected.

Inductive ProjectionInstanceDecision : Type :=
| ProjectionInstanceAccepted
| ProjectionInstanceMismatchDecision.

Definition decideProjectionInstanceByFact
  (instanceMatches : bool) : ProjectionInstanceDecision :=
  if instanceMatches then
    ProjectionInstanceAccepted
  else
    ProjectionInstanceMismatchDecision.

Inductive ProjectionSessionDecision : Type :=
| ProjectionSessionAccepted
| ProjectionSessionMismatchDecision.

Definition decideProjectionSessionByFact
  (sessionMatches : bool) : ProjectionSessionDecision :=
  if sessionMatches then
    ProjectionSessionAccepted
  else
    ProjectionSessionMismatchDecision.

Record ProtocolProjectionPlan
  (instanceType roleKeyType sessionType : Type) : Type :=
  mkProtocolProjectionPlan {
    plannedProjectionInstance : instanceType;
    plannedProjectionRole : roleKeyType;
    plannedProjectionSession : sessionType
  }.

Definition planProtocolProjection
  {instanceType roleKeyType sessionType : Type}
  (instanceRevision : instanceType)
  (roleKey : roleKeyType)
  (localSession : sessionType)
  : ProtocolProjectionPlan instanceType roleKeyType sessionType :=
  {| plannedProjectionInstance := instanceRevision;
     plannedProjectionRole := roleKey;
     plannedProjectionSession := localSession |}.

Record TransferredProtocolContractPlan
  (instanceType roleKeyType sessionType : Type) : Type :=
  mkTransferredProtocolContractPlan {
    plannedTransferInstance : instanceType;
    plannedTransferRole : roleKeyType;
    plannedTransferSession : sessionType
  }.

Definition planTransferredProtocolContract
  {instanceType roleKeyType sessionType : Type}
  (instanceRevision : instanceType)
  (roleKey : roleKeyType)
  (localSession : sessionType)
  : TransferredProtocolContractPlan instanceType roleKeyType sessionType :=
  {| plannedTransferInstance := instanceRevision;
     plannedTransferRole := roleKey;
     plannedTransferSession := localSession |}.

Arguments plannedProjectionInstance {instanceType roleKeyType sessionType} _.
Arguments plannedProjectionRole {instanceType roleKeyType sessionType} _.
Arguments plannedProjectionSession {instanceType roleKeyType sessionType} _.
Arguments plannedTransferInstance {instanceType roleKeyType sessionType} _.
Arguments plannedTransferRole {instanceType roleKeyType sessionType} _.
Arguments plannedTransferSession {instanceType roleKeyType sessionType} _.

Theorem declared_role_fact_accepts :
  decideDeclaredProjectionRoleByFact true = DeclaredProjectionRoleAccepted.
Proof. reflexivity. Qed.

Theorem undeclared_role_fact_rejects :
  decideDeclaredProjectionRoleByFact false = UndeclaredProjectionRoleRejected.
Proof. reflexivity. Qed.

Theorem exact_projection_instance_accepts :
  decideProjectionInstanceByFact true = ProjectionInstanceAccepted.
Proof. reflexivity. Qed.

Theorem mismatched_projection_instance_rejects :
  decideProjectionInstanceByFact false = ProjectionInstanceMismatchDecision.
Proof. reflexivity. Qed.

Theorem exact_projection_session_accepts :
  decideProjectionSessionByFact true = ProjectionSessionAccepted.
Proof. reflexivity. Qed.

Theorem mismatched_projection_session_rejects :
  decideProjectionSessionByFact false = ProjectionSessionMismatchDecision.
Proof. reflexivity. Qed.

Theorem declared_role_decision_sound_complete :
  forall instance roleKey roleDeclared,
    (roleDeclared = true <->
      exists projectedSession,
        ProjectProtocolRole instance roleKey projectedSession) ->
    (decideDeclaredProjectionRoleByFact roleDeclared =
       DeclaredProjectionRoleAccepted <->
      exists projectedSession,
        ProjectProtocolRole instance roleKey projectedSession).
Proof.
  intros instance roleKey roleDeclared Hreflection.
  split.
  - intro Haccepted.
    destruct roleDeclared; simpl in Haccepted; try discriminate.
    apply (proj1 Hreflection).
    reflexivity.
  - intro Hdeclared.
    apply (proj2 Hreflection) in Hdeclared.
    rewrite Hdeclared.
    reflexivity.
Qed.

Theorem projection_instance_decision_sound_complete :
  forall (expected actual : ProtocolInstanceRevision) instanceMatches,
    (instanceMatches = true <-> expected = actual) ->
    (decideProjectionInstanceByFact instanceMatches =
       ProjectionInstanceAccepted <-> expected = actual).
Proof.
  intros expected actual instanceMatches Hreflection.
  split.
  - intro Haccepted.
    destruct instanceMatches; simpl in Haccepted; try discriminate.
    apply (proj1 Hreflection).
    reflexivity.
  - intro Hequal.
    apply (proj2 Hreflection) in Hequal.
    rewrite Hequal.
    reflexivity.
Qed.

Theorem projection_session_decision_sound_complete :
  forall (expected actual : Session) sessionMatches,
    (sessionMatches = true <-> expected = actual) ->
    (decideProjectionSessionByFact sessionMatches =
       ProjectionSessionAccepted <-> expected = actual).
Proof.
  intros expected actual sessionMatches Hreflection.
  split.
  - intro Haccepted.
    destruct sessionMatches; simpl in Haccepted; try discriminate.
    apply (proj1 Hreflection).
    reflexivity.
  - intro Hequal.
    apply (proj2 Hreflection) in Hequal.
    rewrite Hequal.
    reflexivity.
Qed.

Theorem protocol_projection_plan_is_exact :
  forall instanceType roleKeyType sessionType
         (instanceRevision : instanceType)
         (roleKey : roleKeyType)
         (localSession : sessionType),
    plannedProjectionInstance
      (planProtocolProjection instanceRevision roleKey localSession) =
      instanceRevision /\
    plannedProjectionRole
      (planProtocolProjection instanceRevision roleKey localSession) = roleKey /\
    plannedProjectionSession
      (planProtocolProjection instanceRevision roleKey localSession) = localSession.
Proof.
  intros.
  repeat split; reflexivity.
Qed.

Theorem transferred_protocol_contract_plan_is_exact :
  forall instanceType roleKeyType sessionType
         (instanceRevision : instanceType)
         (roleKey : roleKeyType)
         (localSession : sessionType),
    plannedTransferInstance
      (planTransferredProtocolContract instanceRevision roleKey localSession) =
      instanceRevision /\
    plannedTransferRole
      (planTransferredProtocolContract instanceRevision roleKey localSession) =
      roleKey /\
    plannedTransferSession
      (planTransferredProtocolContract instanceRevision roleKey localSession) =
      localSession.
Proof.
  intros.
  repeat split; reflexivity.
Qed.
