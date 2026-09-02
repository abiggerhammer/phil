From Phil.Core Require Import GenericStructural CallableMode.

(*
  PHIL-CALL-MODE-STRENGTHEN-001 — explicit closure-mode strengthening.

  PHIL-CALL-MODE-001 remains authority for the capture-derived minimum mode.
  This theorem family governs only the newer CALL-017 declaration layer:

  - omitted declarations select the exact capture-derived minimum;
  - an explicit declaration may equal that minimum without extra authority;
  - a strictly stronger declaration requires an explicit nonempty semantic
    lifecycle or authority justification bound to the exact callable contract;
  - an explicit declaration may never weaken the capture-derived minimum; and
  - target implementation facts cannot strengthen source closure mode.

  Concrete InterfaceRevision/Text equality, source elaboration, and truth of
  the referenced lifecycle/authority obligation remain correspondence or
  predecessor boundaries.
*)

Definition CallableModeContractRevision := nat.

Inductive ClosureModeJustification : Type :=
| LifecycleModeJustification
    (revision : CallableModeContractRevision)
    (detailPresent : bool)
| AuthorityModeJustification
    (revision : CallableModeContractRevision)
    (detailPresent : bool)
| TargetImplementationModeJustification.

Inductive ClosureModeDeclaration : Type :=
| DerivedClosureMode
| ExplicitClosureMode
    (declared : Mode)
    (justification : option ClosureModeJustification).

Record CheckedClosureMode : Type := mkCheckedClosureMode {
  checkedMinimumMode : Mode;
  checkedSelectedMode : Mode;
  checkedModeJustification : option ClosureModeJustification
}.

Definition SemanticStrengtheningJustification
  (contractRevision : CallableModeContractRevision)
  (justification : option ClosureModeJustification) : Prop :=
  match justification with
  | Some (LifecycleModeJustification revision detailPresent) =>
      revision = contractRevision /\ detailPresent = true
  | Some (AuthorityModeJustification revision detailPresent) =>
      revision = contractRevision /\ detailPresent = true
  | Some TargetImplementationModeJustification => False
  | None => False
  end.

Definition ClosureModeDeclarationValid
  (contractRevision : CallableModeContractRevision)
  (captureMinimum : Mode)
  (declaration : ClosureModeDeclaration)
  (checked : CheckedClosureMode) : Prop :=
  checkedMinimumMode checked = captureMinimum /\
  match declaration with
  | DerivedClosureMode =>
      checkedSelectedMode checked = captureMinimum /\
      checkedModeJustification checked = None
  | ExplicitClosureMode declared justification =>
      checkedSelectedMode checked = declared /\
      checkedModeJustification checked = justification /\
      modeLe captureMinimum declared = true /\
      (declared = captureMinimum \/
       SemanticStrengtheningJustification contractRevision justification)
  end.

Theorem omitted_closure_mode_uses_capture_minimum :
  forall contractRevision captureMinimum checked,
    ClosureModeDeclarationValid
      contractRevision captureMinimum DerivedClosureMode checked ->
    checkedMinimumMode checked = captureMinimum /\
    checkedSelectedMode checked = captureMinimum /\
    checkedModeJustification checked = None.
Proof.
  intros contractRevision captureMinimum checked Hvalid.
  unfold ClosureModeDeclarationValid in Hvalid.
  exact Hvalid.
Qed.

Theorem accepted_explicit_closure_mode_never_weakens_capture_minimum :
  forall contractRevision captureMinimum declared justification checked,
    ClosureModeDeclarationValid
      contractRevision
      captureMinimum
      (ExplicitClosureMode declared justification)
      checked ->
    modeLe captureMinimum declared = true.
Proof.
  intros contractRevision captureMinimum declared justification checked Hvalid.
  unfold ClosureModeDeclarationValid in Hvalid.
  destruct Hvalid as [_ [_ [_ [Hnonweakening _]]]].
  exact Hnonweakening.
Qed.

Theorem explicit_equal_mode_needs_no_strengthening_justification :
  forall contractRevision captureMinimum justification,
    ClosureModeDeclarationValid
      contractRevision
      captureMinimum
      (ExplicitClosureMode captureMinimum justification)
      (mkCheckedClosureMode captureMinimum captureMinimum justification).
Proof.
  intros contractRevision captureMinimum justification.
  unfold ClosureModeDeclarationValid.
  simpl.
  repeat split; try reflexivity.
  - destruct captureMinimum; reflexivity.
  - left. reflexivity.
Qed.

Theorem strict_closure_mode_strengthening_requires_semantic_justification :
  forall contractRevision captureMinimum declared justification checked,
    declared <> captureMinimum ->
    ClosureModeDeclarationValid
      contractRevision
      captureMinimum
      (ExplicitClosureMode declared justification)
      checked ->
    SemanticStrengtheningJustification contractRevision justification.
Proof.
  intros contractRevision captureMinimum declared justification checked Hstrict Hvalid.
  unfold ClosureModeDeclarationValid in Hvalid.
  destruct Hvalid as [_ [_ [_ [_ Hreason]]]].
  destruct Hreason as [Hequal | Hsemantic].
  - contradiction.
  - exact Hsemantic.
Qed.

Theorem lifecycle_strengthening_is_bound_to_exact_contract :
  forall contractRevision captureMinimum declared revision detailPresent checked,
    declared <> captureMinimum ->
    ClosureModeDeclarationValid
      contractRevision
      captureMinimum
      (ExplicitClosureMode declared
        (Some (LifecycleModeJustification revision detailPresent)))
      checked ->
    revision = contractRevision /\ detailPresent = true.
Proof.
  intros contractRevision captureMinimum declared revision detailPresent checked Hstrict Hvalid.
  pose proof
    (strict_closure_mode_strengthening_requires_semantic_justification
      contractRevision captureMinimum declared
      (Some (LifecycleModeJustification revision detailPresent))
      checked Hstrict Hvalid)
    as Hsemantic.
  exact Hsemantic.
Qed.

Theorem authority_strengthening_is_bound_to_exact_contract :
  forall contractRevision captureMinimum declared revision detailPresent checked,
    declared <> captureMinimum ->
    ClosureModeDeclarationValid
      contractRevision
      captureMinimum
      (ExplicitClosureMode declared
        (Some (AuthorityModeJustification revision detailPresent)))
      checked ->
    revision = contractRevision /\ detailPresent = true.
Proof.
  intros contractRevision captureMinimum declared revision detailPresent checked Hstrict Hvalid.
  pose proof
    (strict_closure_mode_strengthening_requires_semantic_justification
      contractRevision captureMinimum declared
      (Some (AuthorityModeJustification revision detailPresent))
      checked Hstrict Hvalid)
    as Hsemantic.
  exact Hsemantic.
Qed.

Theorem target_implementation_cannot_strengthen_source_closure_mode :
  forall contractRevision captureMinimum declared checked,
    declared <> captureMinimum ->
    ~ ClosureModeDeclarationValid
        contractRevision
        captureMinimum
        (ExplicitClosureMode declared
          (Some TargetImplementationModeJustification))
        checked.
Proof.
  intros contractRevision captureMinimum declared checked Hstrict Hvalid.
  pose proof
    (strict_closure_mode_strengthening_requires_semantic_justification
      contractRevision captureMinimum declared
      (Some TargetImplementationModeJustification)
      checked Hstrict Hvalid)
    as Hsemantic.
  exact Hsemantic.
Qed.

Theorem wrong_contract_cannot_justify_lifecycle_strengthening :
  forall contractRevision captureMinimum declared revision detailPresent checked,
    declared <> captureMinimum ->
    revision <> contractRevision ->
    ~ ClosureModeDeclarationValid
        contractRevision
        captureMinimum
        (ExplicitClosureMode declared
          (Some (LifecycleModeJustification revision detailPresent)))
        checked.
Proof.
  intros contractRevision captureMinimum declared revision detailPresent checked
    Hstrict Hwrong Hvalid.
  pose proof
    (lifecycle_strengthening_is_bound_to_exact_contract
      contractRevision captureMinimum declared revision detailPresent checked
      Hstrict Hvalid)
    as Hbound.
  destruct Hbound as [Hequal _].
  exact (Hwrong Hequal).
Qed.

Theorem empty_lifecycle_reason_cannot_justify_strengthening :
  forall contractRevision captureMinimum declared checked,
    declared <> captureMinimum ->
    ~ ClosureModeDeclarationValid
        contractRevision
        captureMinimum
        (ExplicitClosureMode declared
          (Some (LifecycleModeJustification contractRevision false)))
        checked.
Proof.
  intros contractRevision captureMinimum declared checked Hstrict Hvalid.
  pose proof
    (lifecycle_strengthening_is_bound_to_exact_contract
      contractRevision captureMinimum declared contractRevision false checked
      Hstrict Hvalid)
    as Hbound.
  destruct Hbound as [_ Hdetail].
  discriminate Hdetail.
Qed.

Theorem weakening_declaration_cannot_certify :
  forall contractRevision captureMinimum declared justification checked,
    modeLe captureMinimum declared = false ->
    ~ ClosureModeDeclarationValid
        contractRevision
        captureMinimum
        (ExplicitClosureMode declared justification)
        checked.
Proof.
  intros contractRevision captureMinimum declared justification checked Hweak Hvalid.
  pose proof
    (accepted_explicit_closure_mode_never_weakens_capture_minimum
      contractRevision captureMinimum declared justification checked Hvalid)
    as Hnonweakening.
  rewrite Hweak in Hnonweakening.
  discriminate Hnonweakening.
Qed.

Theorem selected_mode_does_not_reclassify_capture_minimum :
  forall contractRevision captureMinimum declaration checked,
    ClosureModeDeclarationValid
      contractRevision captureMinimum declaration checked ->
    checkedMinimumMode checked = captureMinimum.
Proof.
  intros contractRevision captureMinimum declaration checked Hvalid.
  unfold ClosureModeDeclarationValid in Hvalid.
  exact (proj1 Hvalid).
Qed.
