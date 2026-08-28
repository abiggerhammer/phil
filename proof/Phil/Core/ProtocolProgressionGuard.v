From Stdlib Require Import Lists.List Arith.PeanoNat.

Import ListNotations.

From Phil.Core Require Import Syntax ProtocolIdentity.

(*
  PHIL-PROT-STEP-001 — exact protocol progression and guarded-transition
  authority.

  This normalized theorem composes two already-certified lower layers instead
  of rebuilding them:

  - PHIL-PROT-ID-001 supplies exact protocol instance / role / current-session
    action authority;
  - PHIL-SESSION-STEP-001 supplies the linear resource effect of an admitted
    session transition.

  The progression half below models the protocol-metadata occurrence map that
  sits beside that resource theorem. A successful continuation removes the exact
  predecessor occurrence and installs exactly one fresh successor carrying the
  same protocol instance/role and the successor Session supplied by the session
  calculus. A close removes the predecessor and installs nothing. Session-shape
  equality never revives the consumed occurrence because liveness is indexed by
  occurrence identity, not by Session syntax.

  The guard half treats assurance truth as an imported authority relation. A
  guard is satisfied only by the exact required obligation revision being both
  present and certified. Structural protocol legality, a branch label, or a
  transition name does not manufacture that authority; conversely, certified
  guard evidence cannot make a structurally illegal Core action legal.
*)

Definition ProtocolLiveContext :=
  ProtocolOccurrenceName -> option ProtocolEndpointContract.

Definition removeOccurrence
  (name : ProtocolOccurrenceName)
  (context : ProtocolLiveContext) : ProtocolLiveContext :=
  fun query =>
    if Nat.eqb query name then None else context query.

Definition installOccurrence
  (name : ProtocolOccurrenceName)
  (contract : ProtocolEndpointContract)
  (context : ProtocolLiveContext) : ProtocolLiveContext :=
  fun query =>
    if Nat.eqb query name then Some contract else context query.

Definition continuedContract
  (predecessor : ProtocolEndpointContract)
  (successorSession : Session) : ProtocolEndpointContract :=
  {| protocolContractInstance := protocolContractInstance predecessor;
     protocolContractRole := protocolContractRole predecessor;
     protocolContractSession := successorSession |}.

Inductive ProtocolProgressionResult : Type :=
| ProtocolProgressionRejected : ProtocolProgressionResult
| ProtocolProgressionContinued :
    ProtocolLiveContext -> ProtocolEndpointOccurrence -> ProtocolProgressionResult
| ProtocolProgressionClosed :
    ProtocolLiveContext -> ProtocolProgressionResult.

Definition continueProtocolOccurrence
  (predecessor successor : ProtocolOccurrenceName)
  (successorSession : Session)
  (context : ProtocolLiveContext) : ProtocolProgressionResult :=
  match context predecessor with
  | None => ProtocolProgressionRejected
  | Some predecessorContract =>
      if Nat.eqb predecessor successor then
        ProtocolProgressionRejected
      else
        match context successor with
        | Some _ => ProtocolProgressionRejected
        | None =>
            let successorContract :=
              continuedContract predecessorContract successorSession in
            let next :=
              installOccurrence successor successorContract
                (removeOccurrence predecessor context) in
            ProtocolProgressionContinued
              next
              {| protocolOccurrenceName := successor;
                 protocolOccurrenceContract := successorContract |}
        end
  end.

Definition closeProtocolOccurrence
  (predecessor : ProtocolOccurrenceName)
  (context : ProtocolLiveContext) : ProtocolProgressionResult :=
  match context predecessor with
  | None => ProtocolProgressionRejected
  | Some _ =>
      ProtocolProgressionClosed (removeOccurrence predecessor context)
  end.

Theorem successful_continuation_requires_distinct_fresh_successor :
  forall predecessor successor successorSession context next liveSuccessor,
    continueProtocolOccurrence predecessor successor successorSession context =
      ProtocolProgressionContinued next liveSuccessor ->
    Nat.eqb predecessor successor = false /\
    context successor = None.
Proof.
  intros predecessor successor successorSession context next liveSuccessor Hstep.
  unfold continueProtocolOccurrence in Hstep.
  destruct (context predecessor) as [predecessorContract |] eqn:Hpredecessor.
  - destruct (Nat.eqb predecessor successor) eqn:Hdistinct.
    + discriminate.
    + destruct (context successor) as [occupied |] eqn:Hsuccessor.
      * discriminate.
      * inversion Hstep; subst.
        split; reflexivity.
  - discriminate.
Qed.

Theorem successful_continuation_removes_predecessor :
  forall predecessor successor successorSession context next liveSuccessor,
    continueProtocolOccurrence predecessor successor successorSession context =
      ProtocolProgressionContinued next liveSuccessor ->
    next predecessor = None.
Proof.
  intros predecessor successor successorSession context next liveSuccessor Hstep.
  unfold continueProtocolOccurrence in Hstep.
  destruct (context predecessor) as [predecessorContract |] eqn:Hpredecessor.
  - destruct (Nat.eqb predecessor successor) eqn:Hdistinct.
    + discriminate.
    + destruct (context successor) as [occupied |] eqn:Hsuccessor.
      * discriminate.
      * inversion Hstep; subst.
        unfold installOccurrence, removeOccurrence.
        rewrite Hdistinct, Nat.eqb_refl.
        reflexivity.
  - discriminate.
Qed.

Theorem successful_continuation_installs_exact_successor :
  forall predecessor successor successorSession context next liveSuccessor,
    continueProtocolOccurrence predecessor successor successorSession context =
      ProtocolProgressionContinued next liveSuccessor ->
    exists predecessorContract,
      context predecessor = Some predecessorContract /\
      next successor =
        Some (continuedContract predecessorContract successorSession) /\
      protocolOccurrenceName liveSuccessor = successor /\
      protocolOccurrenceContract liveSuccessor =
        continuedContract predecessorContract successorSession.
Proof.
  intros predecessor successor successorSession context next liveSuccessor Hstep.
  unfold continueProtocolOccurrence in Hstep.
  destruct (context predecessor) as [predecessorContract |] eqn:Hpredecessor.
  - destruct (Nat.eqb predecessor successor) eqn:Hdistinct.
    + discriminate.
    + destruct (context successor) as [occupied |] eqn:Hsuccessor.
      * discriminate.
      * inversion Hstep; subst.
        exists predecessorContract.
        split.
        -- reflexivity.
        -- split.
           ++ unfold installOccurrence.
              rewrite Nat.eqb_refl.
              reflexivity.
           ++ split; reflexivity.
  - discriminate.
Qed.

Theorem successful_continuation_preserves_exact_instance_and_role :
  forall predecessor successor successorSession context next liveSuccessor,
    continueProtocolOccurrence predecessor successor successorSession context =
      ProtocolProgressionContinued next liveSuccessor ->
    exists predecessorContract,
      context predecessor = Some predecessorContract /\
      protocolContractInstance (protocolOccurrenceContract liveSuccessor) =
        protocolContractInstance predecessorContract /\
      protocolContractRole (protocolOccurrenceContract liveSuccessor) =
        protocolContractRole predecessorContract /\
      protocolContractSession (protocolOccurrenceContract liveSuccessor) =
        successorSession.
Proof.
  intros predecessor successor successorSession context next liveSuccessor Hstep.
  pose proof
    (successful_continuation_installs_exact_successor
      predecessor successor successorSession context next liveSuccessor Hstep)
    as Hexact.
  destruct Hexact as
    [predecessorContract [Hpredecessor [_ [_ Hcontract]]]].
  exists predecessorContract.
  split.
  - exact Hpredecessor.
  - rewrite Hcontract.
    simpl.
    repeat split; reflexivity.
Qed.

Theorem successful_continuation_preserves_unrelated_occurrences :
  forall predecessor successor successorSession context next liveSuccessor other,
    continueProtocolOccurrence predecessor successor successorSession context =
      ProtocolProgressionContinued next liveSuccessor ->
    Nat.eqb other predecessor = false ->
    Nat.eqb other successor = false ->
    next other = context other.
Proof.
  intros predecessor successor successorSession context next liveSuccessor other
    Hstep HotherPredecessor HotherSuccessor.
  unfold continueProtocolOccurrence in Hstep.
  destruct (context predecessor) as [predecessorContract |] eqn:Hpredecessor.
  - destruct (Nat.eqb predecessor successor) eqn:Hdistinct.
    + discriminate.
    + destruct (context successor) as [occupied |] eqn:Hsuccessor.
      * discriminate.
      * inversion Hstep; subst.
        unfold installOccurrence, removeOccurrence.
        rewrite HotherSuccessor, HotherPredecessor.
        reflexivity.
  - discriminate.
Qed.

Theorem successful_continuation_makes_predecessor_stale :
  forall predecessor successor successorSession context next liveSuccessor,
    continueProtocolOccurrence predecessor successor successorSession context =
      ProtocolProgressionContinued next liveSuccessor ->
    forall attemptedSuccessor attemptedSession,
      continueProtocolOccurrence
        predecessor attemptedSuccessor attemptedSession next =
        ProtocolProgressionRejected.
Proof.
  intros predecessor successor successorSession context next liveSuccessor
    Hstep attemptedSuccessor attemptedSession.
  pose proof
    (successful_continuation_removes_predecessor
      predecessor successor successorSession context next liveSuccessor Hstep)
    as Hgone.
  unfold continueProtocolOccurrence.
  rewrite Hgone.
  reflexivity.
Qed.

Theorem same_name_successor_rejects :
  forall predecessor successorSession context predecessorContract,
    context predecessor = Some predecessorContract ->
    continueProtocolOccurrence
      predecessor predecessor successorSession context =
      ProtocolProgressionRejected.
Proof.
  intros predecessor successorSession context predecessorContract Hlive.
  unfold continueProtocolOccurrence.
  rewrite Hlive, Nat.eqb_refl.
  reflexivity.
Qed.

Theorem occupied_successor_rejects :
  forall predecessor successor successorSession context
         predecessorContract successorContract,
    context predecessor = Some predecessorContract ->
    Nat.eqb predecessor successor = false ->
    context successor = Some successorContract ->
    continueProtocolOccurrence
      predecessor successor successorSession context =
      ProtocolProgressionRejected.
Proof.
  intros predecessor successor successorSession context
    predecessorContract successorContract Hpredecessor Hdistinct Hsuccessor.
  unfold continueProtocolOccurrence.
  rewrite Hpredecessor, Hdistinct, Hsuccessor.
  reflexivity.
Qed.

Theorem successful_close_removes_predecessor :
  forall predecessor context next,
    closeProtocolOccurrence predecessor context =
      ProtocolProgressionClosed next ->
    next predecessor = None.
Proof.
  intros predecessor context next Hstep.
  unfold closeProtocolOccurrence in Hstep.
  destruct (context predecessor) as [predecessorContract |] eqn:Hpredecessor.
  - inversion Hstep; subst.
    unfold removeOccurrence.
    rewrite Nat.eqb_refl.
    reflexivity.
  - discriminate.
Qed.

Theorem successful_close_makes_predecessor_stale :
  forall predecessor context next,
    closeProtocolOccurrence predecessor context =
      ProtocolProgressionClosed next ->
    closeProtocolOccurrence predecessor next = ProtocolProgressionRejected.
Proof.
  intros predecessor context next Hstep.
  pose proof
    (successful_close_removes_predecessor predecessor context next Hstep)
    as Hgone.
  unfold closeProtocolOccurrence.
  rewrite Hgone.
  reflexivity.
Qed.

(* Exact guarded-transition authority. *)

Definition RevisionId := nat.

Inductive ProtocolGuardOrigin : Type :=
| ProtocolDeclaredGuard : ProtocolGuardOrigin
| ArchitectureStrengtheningGuard : ProtocolGuardOrigin.

Record ProtocolTransitionGuard : Type := {
  protocolGuardOrigin : ProtocolGuardOrigin;
  protocolGuardRevision : RevisionId
}.

(*
  These relations are the proof-side seam to PHIL-DISCH-BOUNDARY-001 and the
  assurance verifier. [GuardRevisionCertified] means the exact revision has
  competent accepted evidence under the verified manifest/validity context; it
  is intentionally not defined from branch labels or transition names here.
*)
Parameter GuardRevisionPresent : RevisionId -> Prop.
Parameter GuardRevisionCertified : RevisionId -> Prop.

Definition ExactGuardSatisfied (guard : ProtocolTransitionGuard) : Prop :=
  GuardRevisionPresent (protocolGuardRevision guard) /\
  GuardRevisionCertified (protocolGuardRevision guard).

Definition GuardedProtocolActionAllowed
  (guards : list ProtocolTransitionGuard)
  (request : ProtocolActionRequest)
  (endpoint : ProtocolEndpointOccurrence) : Prop :=
  NoDup guards /\
  Forall ExactGuardSatisfied guards /\
  ProtocolActionAllowed request endpoint.

Theorem guarded_action_requires_every_exact_guard :
  forall guards request endpoint guard,
    GuardedProtocolActionAllowed guards request endpoint ->
    In guard guards ->
    ExactGuardSatisfied guard.
Proof.
  intros guards request endpoint guard Hallowed Hin.
  unfold GuardedProtocolActionAllowed in Hallowed.
  destruct Hallowed as [_ [Hall _]].
  rewrite Forall_forall in Hall.
  apply Hall.
  exact Hin.
Qed.

Theorem guarded_action_requires_exact_guard_revision :
  forall guards request endpoint guard,
    GuardedProtocolActionAllowed guards request endpoint ->
    In guard guards ->
    GuardRevisionPresent (protocolGuardRevision guard) /\
    GuardRevisionCertified (protocolGuardRevision guard).
Proof.
  intros guards request endpoint guard Hallowed Hin.
  pose proof
    (guarded_action_requires_every_exact_guard
      guards request endpoint guard Hallowed Hin)
    as Hguard.
  exact Hguard.
Qed.

Theorem structural_action_or_label_does_not_supply_guard_authority :
  forall guard request endpoint,
    ProtocolActionAllowed request endpoint ->
    ~ ExactGuardSatisfied guard ->
    ~ GuardedProtocolActionAllowed [guard] request endpoint.
Proof.
  intros guard request endpoint Hstructural Hmissing Hguarded.
  apply Hmissing.
  eapply guarded_action_requires_every_exact_guard.
  - exact Hguarded.
  - simpl. left. reflexivity.
Qed.

Theorem another_guard_revision_cannot_substitute :
  forall required supplied request endpoint,
    protocolGuardRevision required <> protocolGuardRevision supplied ->
    ExactGuardSatisfied supplied ->
    ~ ExactGuardSatisfied required ->
    ~ GuardedProtocolActionAllowed [required] request endpoint.
Proof.
  intros required supplied request endpoint
    Hdifferent Hsupplied HrequiredMissing Hguarded.
  apply HrequiredMissing.
  eapply guarded_action_requires_every_exact_guard.
  - exact Hguarded.
  - simpl. left. reflexivity.
Qed.

Theorem protocol_and_architecture_guards_compose_conjunctively :
  forall protocolGuard architectureGuard request endpoint,
    GuardedProtocolActionAllowed
      [protocolGuard; architectureGuard] request endpoint ->
    ExactGuardSatisfied protocolGuard /\
    ExactGuardSatisfied architectureGuard.
Proof.
  intros protocolGuard architectureGuard request endpoint Hguarded.
  split.
  - eapply guarded_action_requires_every_exact_guard.
    + exact Hguarded.
    + simpl. left. reflexivity.
  - eapply guarded_action_requires_every_exact_guard.
    + exact Hguarded.
    + simpl. right. left. reflexivity.
Qed.

Theorem duplicate_guard_requirements_are_not_nodup :
  forall guard : ProtocolTransitionGuard,
    ~ NoDup [guard; guard].
Proof.
  intros guard Hnodup.
  inversion Hnodup as [| first rest Hnotin Hrest].
  apply Hnotin.
  simpl.
  left.
  reflexivity.
Qed.

Theorem duplicate_guard_requirements_reject :
  forall guard request endpoint,
    ~ GuardedProtocolActionAllowed [guard; guard] request endpoint.
Proof.
  intros guard request endpoint Hguarded.
  unfold GuardedProtocolActionAllowed in Hguarded.
  destruct Hguarded as [Hnodup _].
  eapply duplicate_guard_requirements_are_not_nodup.
  exact Hnodup.
Qed.

Theorem guard_evidence_cannot_legalize_structurally_illegal_action :
  forall guards request endpoint,
    ~ ProtocolActionAllowed request endpoint ->
    ~ GuardedProtocolActionAllowed guards request endpoint.
Proof.
  intros guards request endpoint Hillegal Hguarded.
  apply Hillegal.
  unfold GuardedProtocolActionAllowed in Hguarded.
  destruct Hguarded as [_ [_ Hcore]].
  exact Hcore.
Qed.

Theorem guarded_action_still_requires_exact_protocol_identity :
  forall guards request endpoint,
    GuardedProtocolActionAllowed guards request endpoint ->
    requestProtocolInstance request =
      protocolContractInstance (protocolOccurrenceContract endpoint) /\
    requestProtocolRole request =
      protocolContractRole (protocolOccurrenceContract endpoint).
Proof.
  intros guards request endpoint Hguarded.
  unfold GuardedProtocolActionAllowed in Hguarded.
  destruct Hguarded as [_ [_ Hcore]].
  split.
  - eapply protocol_action_requires_exact_instance.
    exact Hcore.
  - eapply protocol_action_requires_exact_role.
    exact Hcore.
Qed.

Theorem guarded_action_still_requires_current_local_state_admission :
  forall guards request endpoint,
    GuardedProtocolActionAllowed guards request endpoint ->
    LocalActionAllowed
      (protocolContractSession (protocolOccurrenceContract endpoint))
      (requestProtocolAction request).
Proof.
  intros guards request endpoint Hguarded.
  unfold GuardedProtocolActionAllowed in Hguarded.
  destruct Hguarded as [_ [_ Hcore]].
  eapply protocol_action_requires_current_local_state_admission.
  exact Hcore.
Qed.
