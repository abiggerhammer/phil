From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import ProtocolIdentity.

Set Implicit Arguments.

(*
  PHIL-PROT-ID-001 — representation-neutral implementation correspondence.

  Production owns concrete Text/Session equality, endpoint-map lookup, resource
  agreement, and execution of the admitted Session action.  This layer owns the
  Certified semantic identity gates:

  - endpoint contract equality is exact instance, then role, then local Session;
  - protocol action identity is exact instance, then role, then current-local-
    state admission; and
  - successful contract construction preserves exactly those three coordinates.

  Occurrence names, transport identity, and runtime representation are
  intentionally absent from the executable decision surface.
*)

Inductive ProtocolContractDecision : Type :=
| ProtocolContractAccepted
| ProtocolContractInstanceMismatchDecision
| ProtocolContractRoleMismatchDecision
| ProtocolContractSessionMismatchDecision.

Definition decideProtocolContractByFacts
  (instanceMatches roleMatches sessionMatches : bool)
  : ProtocolContractDecision :=
  if instanceMatches then
    if roleMatches then
      if sessionMatches then
        ProtocolContractAccepted
      else ProtocolContractSessionMismatchDecision
    else ProtocolContractRoleMismatchDecision
  else ProtocolContractInstanceMismatchDecision.

Inductive ProtocolActionDecision : Type :=
| ProtocolActionAccepted
| ProtocolActionInstanceMismatchDecision
| ProtocolActionRoleMismatchDecision
| ProtocolActionLocalStateRejectedDecision.

Definition decideProtocolActionByFacts
  (instanceMatches roleMatches localStateAllows : bool)
  : ProtocolActionDecision :=
  if instanceMatches then
    if roleMatches then
      if localStateAllows then
        ProtocolActionAccepted
      else ProtocolActionLocalStateRejectedDecision
    else ProtocolActionRoleMismatchDecision
  else ProtocolActionInstanceMismatchDecision.

Record ProtocolContractPlan
  (instance roleKeyType session : Type) : Type :=
  mkProtocolContractPlan {
    plannedProtocolInstance : instance;
    plannedProtocolRole : roleKeyType;
    plannedProtocolSession : session
  }.

Definition planProtocolContract
  {instance roleKeyType session : Type}
  (instanceRevision : instance)
  (roleKey : roleKeyType)
  (localSession : session)
  : ProtocolContractPlan instance roleKeyType session :=
  {| plannedProtocolInstance := instanceRevision;
     plannedProtocolRole := roleKey;
     plannedProtocolSession := localSession |}.

Arguments plannedProtocolInstance {instance roleKeyType session} _.
Arguments plannedProtocolRole {instance roleKeyType session} _.
Arguments plannedProtocolSession {instance roleKeyType session} _.

Theorem exact_contract_facts_accept :
  decideProtocolContractByFacts true true true = ProtocolContractAccepted.
Proof. reflexivity. Qed.

Theorem contract_instance_mismatch_has_precedence :
  forall roleMatches sessionMatches,
    decideProtocolContractByFacts false roleMatches sessionMatches =
      ProtocolContractInstanceMismatchDecision.
Proof. reflexivity. Qed.

Theorem contract_role_mismatch_has_second_precedence :
  forall sessionMatches,
    decideProtocolContractByFacts true false sessionMatches =
      ProtocolContractRoleMismatchDecision.
Proof. reflexivity. Qed.

Theorem contract_session_mismatch_has_third_precedence :
  decideProtocolContractByFacts true true false =
    ProtocolContractSessionMismatchDecision.
Proof. reflexivity. Qed.

Theorem accepted_contract_requires_all_reflected_facts :
  forall instanceMatches roleMatches sessionMatches,
    decideProtocolContractByFacts instanceMatches roleMatches sessionMatches =
      ProtocolContractAccepted ->
    instanceMatches = true /\ roleMatches = true /\ sessionMatches = true.
Proof.
  intros instanceMatches roleMatches sessionMatches Haccepted.
  destruct instanceMatches; simpl in Haccepted; try discriminate.
  destruct roleMatches; simpl in Haccepted; try discriminate.
  destruct sessionMatches; simpl in Haccepted; try discriminate.
  repeat split; reflexivity.
Qed.

Theorem exact_action_facts_accept :
  decideProtocolActionByFacts true true true = ProtocolActionAccepted.
Proof. reflexivity. Qed.

Theorem action_instance_mismatch_has_precedence :
  forall roleMatches localStateAllows,
    decideProtocolActionByFacts false roleMatches localStateAllows =
      ProtocolActionInstanceMismatchDecision.
Proof. reflexivity. Qed.

Theorem action_role_mismatch_has_second_precedence :
  forall localStateAllows,
    decideProtocolActionByFacts true false localStateAllows =
      ProtocolActionRoleMismatchDecision.
Proof. reflexivity. Qed.

Theorem action_local_state_rejection_has_third_precedence :
  decideProtocolActionByFacts true true false =
    ProtocolActionLocalStateRejectedDecision.
Proof. reflexivity. Qed.

Theorem accepted_action_requires_all_reflected_facts :
  forall instanceMatches roleMatches localStateAllows,
    decideProtocolActionByFacts instanceMatches roleMatches localStateAllows =
      ProtocolActionAccepted ->
    instanceMatches = true /\ roleMatches = true /\ localStateAllows = true.
Proof.
  intros instanceMatches roleMatches localStateAllows Haccepted.
  destruct instanceMatches; simpl in Haccepted; try discriminate.
  destruct roleMatches; simpl in Haccepted; try discriminate.
  destruct localStateAllows; simpl in Haccepted; try discriminate.
  repeat split; reflexivity.
Qed.

Theorem protocol_contract_plan_is_exact :
  forall instance roleKeyType session
         (instanceRevision : instance)
         (roleKey : roleKeyType)
         (localSession : session),
    plannedProtocolInstance
      (planProtocolContract instanceRevision roleKey localSession) =
      instanceRevision /\
    plannedProtocolRole
      (planProtocolContract instanceRevision roleKey localSession) = roleKey /\
    plannedProtocolSession
      (planProtocolContract instanceRevision roleKey localSession) = localSession.
Proof.
  intros.
  repeat split; reflexivity.
Qed.

Theorem reflected_contract_decision_is_sound_and_complete :
  forall expected actual instanceMatches roleMatches sessionMatches,
    (instanceMatches = true <->
      protocolContractInstance expected = protocolContractInstance actual) ->
    (roleMatches = true <->
      protocolContractRole expected = protocolContractRole actual) ->
    (sessionMatches = true <->
      protocolContractSession expected = protocolContractSession actual) ->
    (decideProtocolContractByFacts
      instanceMatches roleMatches sessionMatches = ProtocolContractAccepted <->
     ContractMatches expected actual).
Proof.
  intros expected actual instanceMatches roleMatches sessionMatches
    Hinstance Hrole Hsession.
  split.
  - intro Haccepted.
    apply accepted_contract_requires_all_reflected_facts in Haccepted.
    destruct Haccepted as [Hi [Hr Hs]].
    unfold ContractMatches.
    repeat split.
    + apply (proj1 Hinstance). exact Hi.
    + apply (proj1 Hrole). exact Hr.
    + apply (proj1 Hsession). exact Hs.
  - intro Hmatches.
    unfold ContractMatches in Hmatches.
    destruct Hmatches as [Hi [Hr Hs]].
    apply (proj2 Hinstance) in Hi.
    apply (proj2 Hrole) in Hr.
    apply (proj2 Hsession) in Hs.
    subst instanceMatches roleMatches sessionMatches.
    reflexivity.
Qed.

Theorem reflected_action_decision_is_sound_and_complete :
  forall request endpoint instanceMatches roleMatches localStateAllows,
    (instanceMatches = true <->
      requestProtocolInstance request =
        protocolContractInstance (protocolOccurrenceContract endpoint)) ->
    (roleMatches = true <->
      requestProtocolRole request =
        protocolContractRole (protocolOccurrenceContract endpoint)) ->
    (localStateAllows = true <->
      LocalActionAllowed
        (protocolContractSession (protocolOccurrenceContract endpoint))
        (requestProtocolAction request)) ->
    (decideProtocolActionByFacts
      instanceMatches roleMatches localStateAllows = ProtocolActionAccepted <->
     ProtocolActionAllowed request endpoint).
Proof.
  intros request endpoint instanceMatches roleMatches localStateAllows
    Hinstance Hrole Hlocal.
  split.
  - intro Haccepted.
    apply accepted_action_requires_all_reflected_facts in Haccepted.
    destruct Haccepted as [Hi [Hr Hl]].
    unfold ProtocolActionAllowed.
    repeat split.
    + apply (proj1 Hinstance). exact Hi.
    + apply (proj1 Hrole). exact Hr.
    + apply (proj1 Hlocal). exact Hl.
  - intro Hallowed.
    unfold ProtocolActionAllowed in Hallowed.
    destruct Hallowed as [Hi [Hr Hl]].
    apply (proj2 Hinstance) in Hi.
    apply (proj2 Hrole) in Hr.
    apply (proj2 Hlocal) in Hl.
    subst instanceMatches roleMatches localStateAllows.
    reflexivity.
Qed.
