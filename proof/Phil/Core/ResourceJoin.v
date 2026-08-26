From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List.
Import ListNotations.

From Phil.Core Require Import Syntax Context ContextJoin ProcessJoin.

(*
  PHIL-RES-JOIN-001 — generalized continuing resource-join conservation.

  ContextJoin.v and ProcessJoin.v establish the Core default join discipline:
  terminal paths do not contribute a continuing ResourceContext, every Continue
  path is normalized to one joined context, and the linear binding map of that
  joined context agrees exactly with every continuing predecessor.

  The normalized projection relation below captures the stronger state-slot
  discipline used by Phase 1 Systems lowering.  Every live linear owner must be
  represented by exactly one post-state slot, every post-state owner must have
  been live on that predecessor edge, and fixed-subject slots are justified by
  exact semantic-subject continuity or explicit accepted succession evidence.
  Type equality is intentionally irrelevant to subject identity.
*)

Definition ResourceSubject : Type := nat.
Definition ResourceOwner : Type := nat.
Definition ResourceSlot : Type := nat.
Definition ResourceTy : Type := nat.

Definition OwnerSet : Type := ResourceOwner -> bool.
Definition SlotBinding : Type := ResourceSlot -> option ResourceOwner.
Definition SubjectOf : Type := ResourceOwner -> ResourceSubject.
Definition TypeOf : Type := ResourceOwner -> ResourceTy.
Definition SuccessionEvidence : Type := ResourceSubject -> ResourceSubject -> Prop.

Inductive ResourceSlotRequirement : Type :=
| AnyResourceSubject
| FixedResourceSubject (subject : ResourceSubject).

Definition subjectAdmissible
  (succession : SuccessionEvidence)
  (subjects : SubjectOf)
  (requirement : ResourceSlotRequirement)
  (owner : ResourceOwner) : Prop :=
  match requirement with
  | AnyResourceSubject => True
  | FixedResourceSubject expected =>
      subjects owner = expected \/ succession (subjects owner) expected
  end.

Definition ExactlyOnceBound
  (bindings : SlotBinding)
  (owner : ResourceOwner) : Prop :=
  exists slot,
    bindings slot = Some owner /\
    forall other,
      bindings other = Some owner ->
      other = slot.

Record ResourceProjection : Type := mkResourceProjection {
  projectionIncomingLinear : OwnerSet;
  projectionBindings : SlotBinding;
  projectionRequirements : ResourceSlot -> ResourceSlotRequirement;
  projectionSubjectOf : SubjectOf;
  projectionTypeOf : TypeOf
}.

Definition ResourceProjectionSuccess
  (succession : SuccessionEvidence)
  (projection : ResourceProjection) : Prop :=
  (forall owner,
    projectionIncomingLinear projection owner = true ->
    ExactlyOnceBound (projectionBindings projection) owner) /\
  (forall slot owner,
    projectionBindings projection slot = Some owner ->
    projectionIncomingLinear projection owner = true) /\
  (forall slot owner,
    projectionBindings projection slot = Some owner ->
    subjectAdmissible
      succession
      (projectionSubjectOf projection)
      (projectionRequirements projection slot)
      owner).

(* Every and only live linear predecessor owners occur in the post-state. *)
Theorem resource_projection_linear_owner_set_exact :
  forall succession projection owner,
    ResourceProjectionSuccess succession projection ->
    (projectionIncomingLinear projection owner = true <->
      exists slot, projectionBindings projection slot = Some owner).
Proof.
  intros succession projection owner Hsuccess.
  destruct Hsuccess as [Hcovered [HnoInvent Hsubjects]].
  split.
  - intro Hincoming.
    destruct (Hcovered owner Hincoming) as [slot [Hbound Hunique]].
    exists slot.
    exact Hbound.
  - intros [slot Hbound].
    eapply HnoInvent.
    exact Hbound.
Qed.

(* A live linear owner can occupy only one state slot. *)
Theorem resource_projection_linear_owner_bound_once :
  forall succession projection owner firstSlot secondSlot,
    ResourceProjectionSuccess succession projection ->
    projectionIncomingLinear projection owner = true ->
    projectionBindings projection firstSlot = Some owner ->
    projectionBindings projection secondSlot = Some owner ->
    firstSlot = secondSlot.
Proof.
  intros succession projection owner firstSlot secondSlot
    Hsuccess Hincoming Hfirst Hsecond.
  destruct Hsuccess as [Hcovered [HnoInvent Hsubjects]].
  destruct (Hcovered owner Hincoming) as [slot [Hbound Hunique]].
  transitivity slot.
  - apply Hunique.
    exact Hfirst.
  - symmetry.
    apply Hunique.
    exact Hsecond.
Qed.

(* Omitting a live linear predecessor owner contradicts a successful join. *)
Theorem resource_projection_rejects_linear_omission :
  forall succession projection owner,
    ResourceProjectionSuccess succession projection ->
    projectionIncomingLinear projection owner = true ->
    (forall slot, projectionBindings projection slot <> Some owner) ->
    False.
Proof.
  intros succession projection owner Hsuccess Hincoming Homitted.
  pose proof
    (proj1
      (resource_projection_linear_owner_set_exact
        succession projection owner Hsuccess)
      Hincoming) as [slot Hbound].
  apply (Homitted slot).
  exact Hbound.
Qed.

(* A post-state binding cannot invent a fresh linear owner. *)
Theorem resource_projection_rejects_invented_linear_owner :
  forall succession projection slot owner,
    ResourceProjectionSuccess succession projection ->
    projectionBindings projection slot = Some owner ->
    projectionIncomingLinear projection owner = false ->
    False.
Proof.
  intros succession projection slot owner Hsuccess Hbound Habsent.
  destruct Hsuccess as [Hcovered [HnoInvent Hsubjects]].
  pose proof (HnoInvent slot owner Hbound) as Hincoming.
  rewrite Habsent in Hincoming.
  discriminate.
Qed.

(* Fixed slots are exactly continuity-or-succession checks. *)
Theorem fixed_subject_characterization :
  forall succession subjects expected owner,
    subjectAdmissible succession subjects (FixedResourceSubject expected) owner <->
    subjects owner = expected \/ succession (subjects owner) expected.
Proof.
  intros succession subjects expected owner.
  unfold subjectAdmissible.
  reflexivity.
Qed.

Theorem fixed_subject_accepts_exact_continuity :
  forall succession subjects expected owner,
    subjects owner = expected ->
    subjectAdmissible succession subjects (FixedResourceSubject expected) owner.
Proof.
  intros succession subjects expected owner Hsame.
  unfold subjectAdmissible.
  left.
  exact Hsame.
Qed.

Theorem fixed_subject_accepts_explicit_succession :
  forall succession subjects expected owner,
    succession (subjects owner) expected ->
    subjectAdmissible succession subjects (FixedResourceSubject expected) owner.
Proof.
  intros succession subjects expected owner Hsuccession.
  unfold subjectAdmissible.
  right.
  exact Hsuccession.
Qed.

Theorem successful_fixed_slot_is_subject_justified :
  forall succession projection slot owner expected,
    ResourceProjectionSuccess succession projection ->
    projectionBindings projection slot = Some owner ->
    projectionRequirements projection slot = FixedResourceSubject expected ->
    projectionSubjectOf projection owner = expected \/
      succession (projectionSubjectOf projection owner) expected.
Proof.
  intros succession projection slot owner expected Hsuccess Hbound Hrequirement.
  destruct Hsuccess as [Hcovered [HnoInvent Hsubjects]].
  specialize (Hsubjects slot owner Hbound).
  rewrite Hrequirement in Hsubjects.
  exact Hsubjects.
Qed.

(* Equal type cannot repair absent subject identity/succession evidence. *)
Theorem equal_type_does_not_justify_wrong_subject :
  forall succession projection slot owner expected expectedType,
    ResourceProjectionSuccess succession projection ->
    projectionBindings projection slot = Some owner ->
    projectionRequirements projection slot = FixedResourceSubject expected ->
    projectionTypeOf projection owner = expectedType ->
    projectionSubjectOf projection owner <> expected ->
    ~ succession (projectionSubjectOf projection owner) expected ->
    False.
Proof.
  intros succession projection slot owner expected expectedType
    Hsuccess Hbound Hrequirement Htype Hwrong HnoSuccession.
  pose proof
    (successful_fixed_slot_is_subject_justified
      succession projection slot owner expected
      Hsuccess Hbound Hrequirement) as Hjustified.
  destruct Hjustified as [Hsame | Hsuccession].
  - apply Hwrong.
    exact Hsame.
  - apply HnoSuccession.
    exact Hsuccession.
Qed.

(*
  An abstract post-state slot selects one branch-local owner; different
  mutually-exclusive predecessors need not manufacture one shared identity.
*)
Inductive BranchOwnerSelection
  (left right : ResourceOwner) : ResourceOwner -> Prop :=
| BranchOwnerLeft : BranchOwnerSelection left right left
| BranchOwnerRight : BranchOwnerSelection left right right.

Theorem branch_owner_selection_is_bounded :
  forall left right selected,
    BranchOwnerSelection left right selected ->
    selected = left \/ selected = right.
Proof.
  intros left right selected Hselection.
  inversion Hselection; subst.
  - left. reflexivity.
  - right. reflexivity.
Qed.

Theorem abstract_slot_accepts_mutually_exclusive_owner :
  forall succession subjects left right selected,
    left <> right ->
    BranchOwnerSelection left right selected ->
    subjectAdmissible succession subjects AnyResourceSubject selected.
Proof.
  intros succession subjects left right selected Hdifferent Hselection.
  unfold subjectAdmissible.
  exact I.
Qed.

(* The Core default join conserves the complete linear binding map exactly. *)
Theorem core_join_conserves_linear_bindings :
  forall contexts joined context,
    ContextJoinSuccess contexts joined ->
    In context contexts ->
    SameBindingMap
      (linearBindings joined)
      (linearBindings context).
Proof.
  exact context_join_linear_converges.
Qed.

(*
  Process joining composes with ContextJoin: every Continue path is projected
  onto one joined context whose linear bindings agree with every continuing
  predecessor context.  Terminal paths never need to satisfy this premise.
*)
Theorem process_join_conserves_continuing_linear_bindings :
  forall flows output path context,
    ProcessJoinSuccess flows output ->
    In path (flattenBranches flows) ->
    joinControl path = Continue ->
    In context (continuingContexts (flattenBranches flows)) ->
    exists joined,
      ContextJoinSuccess (continuingContexts (flattenBranches flows)) joined /\
      In (normalizeContinue joined path) output /\
      SameBindingMap
        (linearBindings joined)
        (linearBindings context).
Proof.
  intros flows output path context Hjoin Hpath Hcontinue Hcontext.
  destruct
    (process_join_normalizes_every_continue
      flows output path Hjoin Hpath Hcontinue)
    as [joined [HcontextJoin [Houtput [Hcontrol [Hresources Hpayload]]]]].
  exists joined.
  split.
  - exact HcontextJoin.
  - split.
    + exact Houtput.
    + eapply context_join_linear_converges.
      * exact HcontextJoin.
      * exact Hcontext.
Qed.
