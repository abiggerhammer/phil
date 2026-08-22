From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool.
Import ListNotations.

(* Deterministic pre-solver competence model for Phil.Core.Focusing. *)

(* PHIL-FOCUS-COERCE-001 ---------------------------------------------------- *)

Inductive RefinementSort : Type :=
| SortNat : RefinementSort
| SortUInt : nat -> RefinementSort
| SortBool : RefinementSort
| SortOther : nat -> RefinementSort.

Definition refinementSort_eq_dec :
  forall left right : RefinementSort, {left = right} + {left <> right}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

Inductive RefinementTerm : Type :=
| TermVar : nat -> RefinementSort -> RefinementTerm
| TermNat : nat -> RefinementTerm
| TermUInt : nat -> nat -> RefinementTerm
| TermBool : bool -> RefinementTerm
| TermToNat : RefinementTerm -> RefinementTerm.

Definition termSort (term : RefinementTerm) : RefinementSort :=
  match term with
  | TermVar _ sort => sort
  | TermNat _ => SortNat
  | TermUInt width _ => SortUInt width
  | TermBool _ => SortBool
  | TermToNat _ => SortNat
  end.

Inductive CoercionStep : Type :=
| InsertedUIntToNat : RefinementTerm -> CoercionStep.

Inductive ElaborationResult : Type :=
| Elaborated : RefinementTerm -> list CoercionStep -> ElaborationResult
| ElaborationRejected : ElaborationResult.

Definition elaborateAs
  (expected : RefinementSort)
  (term : RefinementTerm) : ElaborationResult :=
  let actual := termSort term in
  match refinementSort_eq_dec actual expected with
  | left _ => Elaborated term []
  | right _ =>
      match expected, actual with
      | SortNat, SortUInt _ =>
          Elaborated (TermToNat term) [InsertedUIntToNat term]
      | _, _ => ElaborationRejected
      end
  end.

Theorem elaborate_matching_sort_is_identity :
  forall expected term,
    termSort term = expected ->
    elaborateAs expected term = Elaborated term [].
Proof.
  intros expected term Hsort.
  unfold elaborateAs.
  destruct (refinementSort_eq_dec (termSort term) expected) as [Heq | Hneq].
  - reflexivity.
  - contradiction.
Qed.

Theorem elaborate_uint_as_nat_is_exact :
  forall width term,
    termSort term = SortUInt width ->
    elaborateAs SortNat term =
      Elaborated (TermToNat term) [InsertedUIntToNat term].
Proof.
  intros width term Hsort.
  unfold elaborateAs. rewrite Hsort.
  destruct (refinementSort_eq_dec (SortUInt width) SortNat) as [Heq | Hneq].
  - discriminate.
  - reflexivity.
Qed.

Theorem elaborate_nat_as_uint_rejects :
  forall width term,
    termSort term = SortNat ->
    elaborateAs (SortUInt width) term = ElaborationRejected.
Proof.
  intros width term Hsort.
  unfold elaborateAs. rewrite Hsort.
  destruct (refinementSort_eq_dec SortNat (SortUInt width)) as [Heq | Hneq].
  - discriminate.
  - reflexivity.
Qed.

Fixpoint elaborateArguments
  (expected : list RefinementSort)
  (arguments : list RefinementTerm) : option (list RefinementTerm) :=
  match expected, arguments with
  | [], [] => Some []
  | expectedSort :: expectedRest, argument :: argumentRest =>
      match elaborateAs expectedSort argument,
            elaborateArguments expectedRest argumentRest with
      | Elaborated argument' _, Some rest => Some (argument' :: rest)
      | _, _ => None
      end
  | _, _ => None
  end.

(* PHIL-FOCUS-CLAIM-001 ----------------------------------------------------- *)

Definition ClaimId := nat.

Inductive FocusProposition : Type :=
| FocusTruth : FocusProposition
| FocusFalsehood : FocusProposition
| FocusAtom : ClaimId -> list RefinementTerm -> FocusProposition
| FocusConjunction : FocusProposition -> FocusProposition -> FocusProposition
| FocusOther : nat -> FocusProposition.

Inductive ClaimDefinition : Type :=
| OpaqueDefinition : ClaimDefinition
| TransparentDefinition :
    (list RefinementTerm -> FocusProposition) -> ClaimDefinition.

Record ClaimDeclaration : Type := mkClaimDeclaration
  { claimParameterSorts : list RefinementSort
  ; claimDefinition : ClaimDefinition
  ; claimWellScoped : bool
  }.

Definition ClaimEnvironment := ClaimId -> option ClaimDeclaration.

Inductive ClaimFocusResult : Type :=
| FocusedOpaqueClaim : list RefinementTerm -> ClaimFocusResult
| ExpandedTransparentClaim : FocusProposition -> ClaimFocusResult
| ClaimFocusRejected : ClaimFocusResult.

Definition focusClaim
  (environment : ClaimEnvironment)
  (expansionStack : list ClaimId)
  (claim : ClaimId)
  (arguments : list RefinementTerm) : ClaimFocusResult :=
  match environment claim with
  | None => ClaimFocusRejected
  | Some declaration =>
      match elaborateArguments (claimParameterSorts declaration) arguments with
      | None => ClaimFocusRejected
      | Some arguments' =>
          match claimDefinition declaration with
          | OpaqueDefinition => FocusedOpaqueClaim arguments'
          | TransparentDefinition body =>
              if claimWellScoped declaration then
                if in_dec Nat.eq_dec claim expansionStack then ClaimFocusRejected
                else ExpandedTransparentClaim (body arguments')
              else ClaimFocusRejected
          end
      end
  end.

Theorem unknown_claim_rejects :
  forall environment stack claim arguments,
    environment claim = None ->
    focusClaim environment stack claim arguments = ClaimFocusRejected.
Proof.
  intros environment stack claim arguments Hunknown.
  unfold focusClaim. rewrite Hunknown. reflexivity.
Qed.

Theorem invalid_claim_arguments_reject :
  forall environment stack claim arguments declaration,
    environment claim = Some declaration ->
    elaborateArguments (claimParameterSorts declaration) arguments = None ->
    focusClaim environment stack claim arguments = ClaimFocusRejected.
Proof.
  intros environment stack claim arguments declaration Hdecl Harguments.
  unfold focusClaim. rewrite Hdecl, Harguments. reflexivity.
Qed.

Theorem opaque_claim_preserves_declared_identity :
  forall environment stack claim arguments declaration arguments',
    environment claim = Some declaration ->
    claimDefinition declaration = OpaqueDefinition ->
    elaborateArguments (claimParameterSorts declaration) arguments = Some arguments' ->
    focusClaim environment stack claim arguments = FocusedOpaqueClaim arguments'.
Proof.
  intros environment stack claim arguments declaration arguments'
    Hdecl Hopaque Harguments.
  unfold focusClaim. rewrite Hdecl, Harguments, Hopaque. reflexivity.
Qed.

Theorem transparent_claim_expands_exact_declared_body :
  forall environment stack claim arguments declaration arguments' body,
    environment claim = Some declaration ->
    claimDefinition declaration = TransparentDefinition body ->
    claimWellScoped declaration = true ->
    elaborateArguments (claimParameterSorts declaration) arguments = Some arguments' ->
    ~ In claim stack ->
    focusClaim environment stack claim arguments =
      ExpandedTransparentClaim (body arguments').
Proof.
  intros environment stack claim arguments declaration arguments' body
    Hdecl Htransparent Hscoped Harguments Hfresh.
  unfold focusClaim. rewrite Hdecl, Harguments, Htransparent, Hscoped.
  destruct (in_dec Nat.eq_dec claim stack) as [Hin | Hnotin].
  - contradiction.
  - reflexivity.
Qed.

Theorem recursive_transparent_claim_rejects :
  forall environment stack claim arguments declaration arguments' body,
    environment claim = Some declaration ->
    claimDefinition declaration = TransparentDefinition body ->
    claimWellScoped declaration = true ->
    elaborateArguments (claimParameterSorts declaration) arguments = Some arguments' ->
    In claim stack ->
    focusClaim environment stack claim arguments = ClaimFocusRejected.
Proof.
  intros environment stack claim arguments declaration arguments' body
    Hdecl Htransparent Hscoped Harguments Hrecursive.
  unfold focusClaim. rewrite Hdecl, Harguments, Htransparent, Hscoped.
  destruct (in_dec Nat.eq_dec claim stack) as [Hin | Hnotin].
  - reflexivity.
  - contradiction.
Qed.

Theorem ill_scoped_transparent_claim_rejects :
  forall environment stack claim arguments declaration arguments' body,
    environment claim = Some declaration ->
    claimDefinition declaration = TransparentDefinition body ->
    claimWellScoped declaration = false ->
    elaborateArguments (claimParameterSorts declaration) arguments = Some arguments' ->
    focusClaim environment stack claim arguments = ClaimFocusRejected.
Proof.
  intros environment stack claim arguments declaration arguments' body
    Hdecl Htransparent Hscoped Harguments.
  unfold focusClaim. rewrite Hdecl, Harguments, Htransparent, Hscoped.
  reflexivity.
Qed.

(* PHIL-FOCUS-PREREQ-001 ---------------------------------------------------- *)

Inductive FocusMechanism : Type :=
| FocusByDefinition : FocusMechanism
| FocusByEvidence : nat -> FocusMechanism
| FocusNeedsDecisionProcedure : FocusMechanism
| FocusNeedsExplicitMechanism : FocusMechanism
| FocusStaticallyFalse : FocusMechanism.

Record FocusedRequirement : Type := mkFocusedRequirement
  { requirementOriginal : nat
  ; requirementCanonical : nat
  ; requirementMechanism : FocusMechanism
  }.

Record FocusPlan : Type := mkFocusPlan
  { planPrerequisites : list FocusedRequirement
  ; planGoal : FocusedRequirement
  }.

Fixpoint collectSideCanonicalKeys (plans : list FocusPlan) : list nat :=
  match plans with
  | [] => []
  | plan :: rest =>
      map requirementCanonical (planPrerequisites plan)
        ++ requirementCanonical (planGoal plan) :: collectSideCanonicalKeys rest
  end.

Definition assembledPrerequisiteKeys (plans : list FocusPlan) : list nat :=
  nodup Nat.eq_dec (collectSideCanonicalKeys plans).

Lemma side_goal_is_collected :
  forall plans plan,
    In plan plans ->
    In (requirementCanonical (planGoal plan)) (collectSideCanonicalKeys plans).
Proof.
  induction plans as [| head rest IH]; intros plan Hin.
  - contradiction.
  - simpl in Hin. destruct Hin as [Hequal | Hin].
    + subst head. simpl. apply in_or_app. right. simpl. left. reflexivity.
    + simpl. apply in_or_app. right. simpl. right. apply IH. exact Hin.
Qed.

Lemma side_prerequisite_is_collected :
  forall plans plan prerequisite,
    In plan plans ->
    In prerequisite (planPrerequisites plan) ->
    In (requirementCanonical prerequisite) (collectSideCanonicalKeys plans).
Proof.
  induction plans as [| head rest IH]; intros plan prerequisite Hplan Hprerequisite.
  - contradiction.
  - simpl in Hplan. destruct Hplan as [Hequal | Hplan].
    + subst head. simpl. apply in_or_app. left. apply in_map. exact Hprerequisite.
    + simpl. apply in_or_app. right. simpl. right. eapply IH; eauto.
Qed.

Theorem side_goal_survives_deduplicated_assembly :
  forall plans plan,
    In plan plans ->
    In (requirementCanonical (planGoal plan)) (assembledPrerequisiteKeys plans).
Proof.
  intros plans plan Hplan. unfold assembledPrerequisiteKeys.
  apply (proj2 (nodup_In Nat.eq_dec
    (collectSideCanonicalKeys plans)
    (requirementCanonical (planGoal plan)))).
  now apply side_goal_is_collected with (plan := plan).
Qed.

Theorem nested_side_prerequisite_survives_deduplicated_assembly :
  forall plans plan prerequisite,
    In plan plans ->
    In prerequisite (planPrerequisites plan) ->
    In (requirementCanonical prerequisite) (assembledPrerequisiteKeys plans).
Proof.
  intros plans plan prerequisite Hplan Hprerequisite.
  unfold assembledPrerequisiteKeys.
  apply (proj2 (nodup_In Nat.eq_dec
    (collectSideCanonicalKeys plans)
    (requirementCanonical prerequisite))).
  eapply side_prerequisite_is_collected; eauto.
Qed.

(* PHIL-FOCUS-MECH-001 ------------------------------------------------------ *)

Inductive CanonicalGoal : Type :=
| CanonicalTruth : CanonicalGoal
| CanonicalFalsehood : CanonicalGoal
| CanonicalOpaque : nat -> CanonicalGoal
| CanonicalTransparent : nat -> CanonicalGoal.

Definition classifyRequirement
  (goal : CanonicalGoal)
  (matchingEvidence : option nat) : FocusMechanism :=
  match goal with
  | CanonicalTruth => FocusByDefinition
  | _ =>
      match matchingEvidence with
      | Some evidence => FocusByEvidence evidence
      | None =>
          match goal with
          | CanonicalFalsehood => FocusStaticallyFalse
          | CanonicalOpaque _ => FocusNeedsExplicitMechanism
          | CanonicalTransparent _ => FocusNeedsDecisionProcedure
          | CanonicalTruth => FocusByDefinition
          end
      end
  end.

Theorem truth_is_definitionally_discharged :
  forall evidence,
    classifyRequirement CanonicalTruth evidence = FocusByDefinition.
Proof. intros evidence. reflexivity. Qed.

Theorem matching_evidence_precedes_later_boundaries :
  forall goal evidence,
    goal <> CanonicalTruth ->
    classifyRequirement goal (Some evidence) = FocusByEvidence evidence.
Proof.
  intros goal evidence HnotTruth. destruct goal; simpl.
  - contradiction.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem falsehood_without_evidence_rejects :
  classifyRequirement CanonicalFalsehood None = FocusStaticallyFalse.
Proof. reflexivity. Qed.

Theorem unresolved_opaque_goal_needs_explicit_mechanism :
  forall claim,
    classifyRequirement (CanonicalOpaque claim) None = FocusNeedsExplicitMechanism.
Proof. intros claim. reflexivity. Qed.

Theorem unresolved_transparent_goal_stops_at_decision_boundary :
  forall claim,
    classifyRequirement (CanonicalTransparent claim) None = FocusNeedsDecisionProcedure.
Proof. intros claim. reflexivity. Qed.

(* PHIL-FOCUS-BRANCH-001 ---------------------------------------------------- *)

Definition Label := nat.
Definition SameLabelSet (declared handlers : list Label) : Prop :=
  forall label, In label declared <-> In label handlers.
Definition BranchCheckSuccess (declared handlers : list Label) : Prop :=
  NoDup declared /\ NoDup handlers /\ SameLabelSet declared handlers.
Definition MissingHandler (declared handlers : list Label) (label : Label) : Prop :=
  In label declared /\ ~ In label handlers.
Definition ExtraHandler (declared handlers : list Label) (label : Label) : Prop :=
  In label handlers /\ ~ In label declared.

Theorem successful_branch_check_is_exact :
  forall declared handlers,
    BranchCheckSuccess declared handlers ->
    NoDup declared /\ NoDup handlers /\ SameLabelSet declared handlers.
Proof. intros declared handlers Hsuccess. exact Hsuccess. Qed.

Theorem duplicate_declared_label_prevents_success :
  forall declared handlers,
    ~ NoDup declared -> ~ BranchCheckSuccess declared handlers.
Proof.
  intros declared handlers Hduplicate Hsuccess.
  apply Hduplicate. exact (proj1 Hsuccess).
Qed.

Theorem duplicate_handler_label_prevents_success :
  forall declared handlers,
    ~ NoDup handlers -> ~ BranchCheckSuccess declared handlers.
Proof.
  intros declared handlers Hduplicate Hsuccess.
  apply Hduplicate. exact (proj1 (proj2 Hsuccess)).
Qed.

Theorem missing_handler_prevents_success :
  forall declared handlers label,
    MissingHandler declared handlers label ->
    ~ BranchCheckSuccess declared handlers.
Proof.
  intros declared handlers label [Hdeclared Hmissing] Hsuccess.
  destruct Hsuccess as [_ [_ Hsame]].
  apply Hmissing. apply (proj1 (Hsame label)). exact Hdeclared.
Qed.

Theorem extra_handler_prevents_success :
  forall declared handlers label,
    ExtraHandler declared handlers label ->
    ~ BranchCheckSuccess declared handlers.
Proof.
  intros declared handlers label [Hhandler Hextra] Hsuccess.
  destruct Hsuccess as [_ [_ Hsame]].
  apply Hextra. apply (proj2 (Hsame label)). exact Hhandler.
Qed.

Theorem exact_duplicate_free_coverage_is_success :
  forall declared handlers,
    NoDup declared -> NoDup handlers -> SameLabelSet declared handlers ->
    BranchCheckSuccess declared handlers.
Proof.
  intros declared handlers Hdeclared Hhandlers Hsame.
  split.
  - exact Hdeclared.
  - split.
    + exact Hhandlers.
    + exact Hsame.
Qed.
