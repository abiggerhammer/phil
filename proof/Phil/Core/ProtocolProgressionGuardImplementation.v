From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import ProtocolProgressionGuard.

Set Implicit Arguments.

(*
  PHIL-PROT-STEP-001 — representation-neutral implementation correspondence.

  The existing production stack already delegates structural action legality to
  the PHIL-PROT-ID-001-bound Protocol checker and evidence truth/acceptance to
  the assurance verifier.  This layer owns only the remaining protocol-step
  choices over native reflected facts:

    - predecessor liveness / distinct successor / successor freshness;
    - close predecessor liveness;
    - exact instance/role/successor-session metadata reconstruction;
    - duplicate guard-list rejection; and
    - exact present+certified admission for each required guard revision.

  Concrete Map/Set/Text/Session representation, resource-context mutation,
  Session execution, manifest verification, evidence truth, and diagnostics
  remain explicit native or predecessor boundaries.
*)

Inductive ProtocolContinuationDecision : Type :=
| ProtocolContinuationAccepted
| ProtocolContinuationPredecessorMissingDecision
| ProtocolContinuationSameNameDecision
| ProtocolContinuationSuccessorOccupiedDecision.

Definition decideProtocolContinuationByFacts
  (predecessorLive namesDistinct successorFresh : bool)
  : ProtocolContinuationDecision :=
  if predecessorLive then
    if namesDistinct then
      if successorFresh then
        ProtocolContinuationAccepted
      else ProtocolContinuationSuccessorOccupiedDecision
    else ProtocolContinuationSameNameDecision
  else ProtocolContinuationPredecessorMissingDecision.

Inductive ProtocolCloseDecision : Type :=
| ProtocolCloseAccepted
| ProtocolClosePredecessorMissingDecision.

Definition decideProtocolCloseByFact
  (predecessorLive : bool) : ProtocolCloseDecision :=
  if predecessorLive then ProtocolCloseAccepted
  else ProtocolClosePredecessorMissingDecision.

Record ProtocolSuccessorContractPlan
  (instanceType roleType sessionType : Type) : Type :=
  mkProtocolSuccessorContractPlan {
    plannedSuccessorInstance : instanceType;
    plannedSuccessorRole : roleType;
    plannedSuccessorSession : sessionType
  }.

Definition planProtocolSuccessorContract
  {instanceType roleType sessionType : Type}
  (instanceRevision : instanceType)
  (role : roleType)
  (successorSession : sessionType)
  : ProtocolSuccessorContractPlan instanceType roleType sessionType :=
  {| plannedSuccessorInstance := instanceRevision;
     plannedSuccessorRole := role;
     plannedSuccessorSession := successorSession |}.

Inductive ProtocolGuardListDecision : Type :=
| ProtocolGuardListAccepted
| ProtocolGuardListDuplicateDecision.

Definition decideProtocolGuardListByFact
  (guardsUnique : bool) : ProtocolGuardListDecision :=
  if guardsUnique then ProtocolGuardListAccepted
  else ProtocolGuardListDuplicateDecision.

Inductive ProtocolGuardRequirementDecision : Type :=
| ProtocolGuardRequirementAccepted
| ProtocolGuardRevisionMissingDecision
| ProtocolGuardRevisionNotCertifiedDecision.

Definition decideProtocolGuardRequirementByFacts
  (revisionPresent revisionCertified : bool)
  : ProtocolGuardRequirementDecision :=
  if revisionPresent then
    if revisionCertified then ProtocolGuardRequirementAccepted
    else ProtocolGuardRevisionNotCertifiedDecision
  else ProtocolGuardRevisionMissingDecision.

Theorem continuation_exact_facts_accept :
  decideProtocolContinuationByFacts true true true =
    ProtocolContinuationAccepted.
Proof. reflexivity. Qed.

Theorem continuation_missing_predecessor_has_first_precedence :
  forall namesDistinct successorFresh,
    decideProtocolContinuationByFacts false namesDistinct successorFresh =
      ProtocolContinuationPredecessorMissingDecision.
Proof. reflexivity. Qed.

Theorem continuation_same_name_has_second_precedence :
  forall successorFresh,
    decideProtocolContinuationByFacts true false successorFresh =
      ProtocolContinuationSameNameDecision.
Proof. reflexivity. Qed.

Theorem continuation_occupied_successor_has_third_precedence :
  decideProtocolContinuationByFacts true true false =
    ProtocolContinuationSuccessorOccupiedDecision.
Proof. reflexivity. Qed.

Theorem continuation_acceptance_requires_all_reflected_facts :
  forall predecessorLive namesDistinct successorFresh,
    decideProtocolContinuationByFacts
      predecessorLive namesDistinct successorFresh = ProtocolContinuationAccepted ->
    predecessorLive = true /\ namesDistinct = true /\ successorFresh = true.
Proof.
  intros predecessorLive namesDistinct successorFresh Hdecision.
  destruct predecessorLive, namesDistinct, successorFresh;
    simpl in Hdecision; try discriminate; repeat split; reflexivity.
Qed.

Theorem all_reflected_continuation_facts_are_sufficient :
  forall predecessorLive namesDistinct successorFresh,
    predecessorLive = true ->
    namesDistinct = true ->
    successorFresh = true ->
    decideProtocolContinuationByFacts
      predecessorLive namesDistinct successorFresh = ProtocolContinuationAccepted.
Proof.
  intros predecessorLive namesDistinct successorFresh
    Hpredecessor Hdistinct Hfresh.
  rewrite Hpredecessor, Hdistinct, Hfresh.
  reflexivity.
Qed.

Theorem close_live_predecessor_accepts :
  decideProtocolCloseByFact true = ProtocolCloseAccepted.
Proof. reflexivity. Qed.

Theorem close_stale_predecessor_rejects :
  decideProtocolCloseByFact false = ProtocolClosePredecessorMissingDecision.
Proof. reflexivity. Qed.

Theorem successor_plan_preserves_exact_protocol_coordinates :
  forall (instanceType roleType sessionType : Type)
         (instanceRevision : instanceType)
         (role : roleType)
         (successorSession : sessionType),
    plannedSuccessorInstance
      (planProtocolSuccessorContract instanceRevision role successorSession) =
        instanceRevision /\
    plannedSuccessorRole
      (planProtocolSuccessorContract instanceRevision role successorSession) = role /\
    plannedSuccessorSession
      (planProtocolSuccessorContract instanceRevision role successorSession) =
        successorSession.
Proof.
  intros. repeat split; reflexivity.
Qed.

Theorem unique_guard_list_accepts :
  decideProtocolGuardListByFact true = ProtocolGuardListAccepted.
Proof. reflexivity. Qed.

Theorem duplicate_guard_list_rejects :
  decideProtocolGuardListByFact false = ProtocolGuardListDuplicateDecision.
Proof. reflexivity. Qed.

Theorem exact_present_certified_guard_accepts :
  decideProtocolGuardRequirementByFacts true true =
    ProtocolGuardRequirementAccepted.
Proof. reflexivity. Qed.

Theorem missing_guard_revision_has_first_precedence :
  forall revisionCertified,
    decideProtocolGuardRequirementByFacts false revisionCertified =
      ProtocolGuardRevisionMissingDecision.
Proof. reflexivity. Qed.

Theorem uncertified_guard_revision_rejects :
  decideProtocolGuardRequirementByFacts true false =
    ProtocolGuardRevisionNotCertifiedDecision.
Proof. reflexivity. Qed.

Theorem guard_acceptance_requires_presence_and_certification :
  forall revisionPresent revisionCertified,
    decideProtocolGuardRequirementByFacts revisionPresent revisionCertified =
      ProtocolGuardRequirementAccepted ->
    revisionPresent = true /\ revisionCertified = true.
Proof.
  intros revisionPresent revisionCertified Hdecision.
  destruct revisionPresent, revisionCertified;
    simpl in Hdecision; try discriminate; split; reflexivity.
Qed.

Theorem present_and_certified_guard_is_sufficient :
  forall revisionPresent revisionCertified,
    revisionPresent = true ->
    revisionCertified = true ->
    decideProtocolGuardRequirementByFacts revisionPresent revisionCertified =
      ProtocolGuardRequirementAccepted.
Proof.
  intros revisionPresent revisionCertified Hpresent Hcertified.
  rewrite Hpresent, Hcertified.
  reflexivity.
Qed.
