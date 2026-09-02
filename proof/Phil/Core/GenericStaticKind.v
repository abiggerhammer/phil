From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.

Import ListNotations.

(*
  PHIL-GEN-KIND-001 — exact generic static-actual kind selection (GEN-013).

  Parsing has already selected one concrete static-actual form.  A name-shaped
  reference is interpreted only through the declared parameter kind: acceptance
  never retries the same spelling under another semantic category.  This model
  keeps concrete names and SemanticForm values opaque as naturals and proves the
  exact category/arity/ambiguity properties exercised by the production checker.
*)

Inductive GenericStaticKind : Type :=
| GenericTypeKind
| GenericIndexKind
| GenericSessionKind
| GenericMessageKind
| GenericEffectsKind
| GenericProviderContractKind
| GenericCallableContractKind
| GenericBoundaryContractKind
| GenericArchitectureDependencyKind.

Definition genericStaticKindEqb
  (first second : GenericStaticKind) : bool :=
  match first, second with
  | GenericTypeKind, GenericTypeKind => true
  | GenericIndexKind, GenericIndexKind => true
  | GenericSessionKind, GenericSessionKind => true
  | GenericMessageKind, GenericMessageKind => true
  | GenericEffectsKind, GenericEffectsKind => true
  | GenericProviderContractKind, GenericProviderContractKind => true
  | GenericCallableContractKind, GenericCallableContractKind => true
  | GenericBoundaryContractKind, GenericBoundaryContractKind => true
  | GenericArchitectureDependencyKind, GenericArchitectureDependencyKind => true
  | _, _ => false
  end.

Lemma genericStaticKindEqb_refl :
  forall kind,
    genericStaticKindEqb kind kind = true.
Proof.
  intros kind.
  destruct kind; reflexivity.
Qed.

Lemma genericStaticKindEqb_eq :
  forall first second,
    genericStaticKindEqb first second = true ->
    first = second.
Proof.
  intros first second Hequal.
  destruct first, second; simpl in Hequal; try discriminate; reflexivity.
Qed.

Record StaticParameter : Type := mkStaticParameter {
  parameterKey : nat;
  parameterKind : GenericStaticKind
}.

Inductive StaticActual : Type :=
| DirectStaticActual (actualKind : GenericStaticKind) (semanticForm : nat)
| ReferencedStaticActual (referenceName : nat).

Record StaticReferenceCandidate : Type := mkStaticReferenceCandidate {
  candidateName : nat;
  candidateKind : GenericStaticKind;
  candidateSemanticForm : nat
}.

Record CheckedStaticActual : Type := mkCheckedStaticActual {
  checkedParameterKey : nat;
  checkedStaticKind : GenericStaticKind;
  checkedSemanticForm : nat
}.

Definition candidateMatches
  (expectedKind : GenericStaticKind)
  (referenceName : nat)
  (candidate : StaticReferenceCandidate) : bool :=
  andb
    (Nat.eqb (candidateName candidate) referenceName)
    (genericStaticKindEqb (candidateKind candidate) expectedKind).

Definition matchingCandidates
  (expectedKind : GenericStaticKind)
  (referenceName : nat)
  (references : list StaticReferenceCandidate) : list StaticReferenceCandidate :=
  filter (candidateMatches expectedKind referenceName) references.

Definition ReferenceResolves
  (references : list StaticReferenceCandidate)
  (expectedKind : GenericStaticKind)
  (referenceName semanticForm : nat) : Prop :=
  exists candidate,
    matchingCandidates expectedKind referenceName references = [candidate] /\
    candidateSemanticForm candidate = semanticForm.

Definition ReferenceAmbiguous
  (references : list StaticReferenceCandidate)
  (expectedKind : GenericStaticKind)
  (referenceName : nat) : Prop :=
  2 <= length (matchingCandidates expectedKind referenceName references).

Theorem reference_resolution_uses_declared_kind :
  forall references expectedKind referenceName semanticForm,
    ReferenceResolves references expectedKind referenceName semanticForm ->
    exists candidate,
      In candidate references /\
      candidateName candidate = referenceName /\
      candidateKind candidate = expectedKind /\
      candidateSemanticForm candidate = semanticForm.
Proof.
  intros references expectedKind referenceName semanticForm Hresolves.
  destruct Hresolves as [candidate [Hmatching Hsemantic]].
  assert (HinFiltered :
    In candidate (matchingCandidates expectedKind referenceName references)).
  {
    rewrite Hmatching.
    simpl.
    auto.
  }
  unfold matchingCandidates in HinFiltered.
  apply filter_In in HinFiltered.
  destruct HinFiltered as [HinReferences Hmatches].
  unfold candidateMatches in Hmatches.
  apply andb_true_iff in Hmatches.
  destruct Hmatches as [Hname Hkind].
  apply Nat.eqb_eq in Hname.
  apply genericStaticKindEqb_eq in Hkind.
  exists candidate.
  repeat split; assumption.
Qed.

Theorem unresolved_reference_cannot_resolve :
  forall references expectedKind referenceName semanticForm,
    matchingCandidates expectedKind referenceName references = [] ->
    ~ ReferenceResolves references expectedKind referenceName semanticForm.
Proof.
  intros references expectedKind referenceName semanticForm Hnone Hresolves.
  destruct Hresolves as [candidate [Hone _]].
  rewrite Hnone in Hone.
  discriminate.
Qed.

Theorem wrong_kind_reference_cannot_fallback :
  forall references expectedKind referenceName semanticForm,
    (forall candidate,
      In candidate references ->
      candidateName candidate = referenceName ->
      candidateKind candidate <> expectedKind) ->
    ~ ReferenceResolves references expectedKind referenceName semanticForm.
Proof.
  intros references expectedKind referenceName semanticForm Hwrong Hresolves.
  destruct (reference_resolution_uses_declared_kind
    references expectedKind referenceName semanticForm Hresolves)
    as [candidate [Hin [Hname [Hkind _]]]].
  apply (Hwrong candidate Hin Hname).
  exact Hkind.
Qed.

Theorem ambiguous_same_kind_reference_cannot_resolve :
  forall references expectedKind referenceName semanticForm,
    ReferenceAmbiguous references expectedKind referenceName ->
    ~ ReferenceResolves references expectedKind referenceName semanticForm.
Proof.
  intros references expectedKind referenceName semanticForm Hambiguous Hresolves.
  unfold ReferenceAmbiguous in Hambiguous.
  destruct Hresolves as [candidate [Hmatching _]].
  rewrite Hmatching in Hambiguous.
  simpl in Hambiguous.
  lia.
Qed.

Inductive StaticActualAccepts
  (references : list StaticReferenceCandidate) :
  StaticParameter -> StaticActual -> CheckedStaticActual -> Prop :=
| directStaticActualAccepted :
    forall parameter semanticForm,
      StaticActualAccepts references
        parameter
        (DirectStaticActual (parameterKind parameter) semanticForm)
        (mkCheckedStaticActual
          (parameterKey parameter)
          (parameterKind parameter)
          semanticForm)
| referencedStaticActualAccepted :
    forall parameter referenceName semanticForm,
      ReferenceResolves
        references
        (parameterKind parameter)
        referenceName
        semanticForm ->
      StaticActualAccepts references
        parameter
        (ReferencedStaticActual referenceName)
        (mkCheckedStaticActual
          (parameterKey parameter)
          (parameterKind parameter)
          semanticForm).

Theorem accepted_static_actual_preserves_parameter_identity :
  forall references parameter actual checked,
    StaticActualAccepts references parameter actual checked ->
    checkedParameterKey checked = parameterKey parameter /\
    checkedStaticKind checked = parameterKind parameter.
Proof.
  intros references parameter actual checked Haccepted.
  inversion Haccepted; subst; split; reflexivity.
Qed.

Theorem direct_wrong_kind_actual_rejects :
  forall references parameter actualKind semanticForm checked,
    actualKind <> parameterKind parameter ->
    ~ StaticActualAccepts references
        parameter
        (DirectStaticActual actualKind semanticForm)
        checked.
Proof.
  intros references parameter actualKind semanticForm checked Hwrong Haccepted.
  inversion Haccepted; subst.
  apply Hwrong.
  reflexivity.
Qed.

Theorem accepted_reference_uses_expected_kind_only :
  forall references parameter referenceName checked,
    StaticActualAccepts references
      parameter
      (ReferencedStaticActual referenceName)
      checked ->
    ReferenceResolves
      references
      (parameterKind parameter)
      referenceName
      (checkedSemanticForm checked).
Proof.
  intros references parameter referenceName checked Haccepted.
  inversion Haccepted; subst.
  assumption.
Qed.

Inductive StaticTelescopeAccepts
  (references : list StaticReferenceCandidate) :
  list StaticParameter -> list StaticActual -> list CheckedStaticActual -> Prop :=
| staticTelescopeNil :
    StaticTelescopeAccepts references [] [] []
| staticTelescopeCons :
    forall parameter actual checked parameters actuals checkedActuals,
      StaticActualAccepts references parameter actual checked ->
      StaticTelescopeAccepts references parameters actuals checkedActuals ->
      StaticTelescopeAccepts references
        (parameter :: parameters)
        (actual :: actuals)
        (checked :: checkedActuals).

Theorem accepted_telescope_has_exact_arity :
  forall references parameters actuals checkedActuals,
    StaticTelescopeAccepts references parameters actuals checkedActuals ->
    length parameters = length actuals /\
    length parameters = length checkedActuals.
Proof.
  intros references parameters actuals checkedActuals Haccepted.
  induction Haccepted.
  - simpl. auto.
  - destruct IHHaccepted as [Hactuals Hchecked].
    simpl.
    split; f_equal; assumption.
Qed.

Definition parameterShape
  (parameters : list StaticParameter) : list (nat * GenericStaticKind) :=
  map (fun parameter => (parameterKey parameter, parameterKind parameter)) parameters.

Definition checkedShape
  (checkedActuals : list CheckedStaticActual) : list (nat * GenericStaticKind) :=
  map
    (fun checked => (checkedParameterKey checked, checkedStaticKind checked))
    checkedActuals.

Theorem accepted_telescope_preserves_declared_shape :
  forall references parameters actuals checkedActuals,
    StaticTelescopeAccepts references parameters actuals checkedActuals ->
    checkedShape checkedActuals = parameterShape parameters.
Proof.
  intros references parameters actuals checkedActuals Haccepted.
  induction Haccepted.
  - reflexivity.
  - unfold checkedShape, parameterShape in *.
    simpl.
    destruct (accepted_static_actual_preserves_parameter_identity
      references parameter actual checked H) as [Hkey Hkind].
    rewrite Hkey, Hkind, IHHaccepted.
    reflexivity.
Qed.
