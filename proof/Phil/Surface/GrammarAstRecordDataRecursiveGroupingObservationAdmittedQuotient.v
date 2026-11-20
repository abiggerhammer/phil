From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingTaggedAdmission
  GrammarAstRecordDataRecursiveGroupingProductionObservables
  GrammarAstRecordDataRecursiveGroupingObservationSeparation
  GrammarAstRecordDataRecursiveGroupingObservationPER
  GrammarAstRecordDataRecursiveGroupingObservationPERDomain.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: turn the partial observation
  equivalence on public Record/Data tag+tree keys into an ordinary
  equivalence on the subtype carrying actual successful admissions.
  Observational equivalence is explicitly weaker than exact-key
  equality, and never admits malformed public intermediate carriers.
  This is a proof-side construction; no production Haskell AST binding,
  G2/G4, trusted semantic change, or Phase 1 closure is claimed.
*)

Record Phase1SurfaceAdmittedObservationKey : Type := {
  phase1_admitted_observation_key : Phase1SurfaceDeclarationSpine;
  phase1_admitted_observation_refined :
    Phase1SurfaceRecursiveGroupingImplementationRecordDataDeclaration;
  phase1_admitted_observation_certificate :
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      phase1_admitted_observation_key =
      Some phase1_admitted_observation_refined
}.

Definition phase1_surface_admitted_observation
  (entry : Phase1SurfaceAdmittedObservationKey)
  : Phase1SurfaceRecursiveGroupingObservedRecordData :=
  phase1_surface_observe_recursive_grouping_record_data
    (phase1_admitted_observation_refined entry).

Definition phase1_surface_admitted_observation_equiv
  (left right : Phase1SurfaceAdmittedObservationKey) : Prop :=
  phase1_surface_admitted_observation left =
    phase1_surface_admitted_observation right.

Theorem phase1_surface_admitted_observation_equiv_iff_public_related :
  forall left right,
    phase1_surface_admitted_observation_equiv left right <->
    phase1_surface_recursive_grouping_observation_related
      (phase1_admitted_observation_key left)
      (phase1_admitted_observation_key right).
Proof.
  intros left right.
  split.
  - intros Hobs.
    exists (phase1_admitted_observation_refined left),
      (phase1_admitted_observation_refined right).
    split; [exact (phase1_admitted_observation_certificate left) |].
    split; [exact (phase1_admitted_observation_certificate right) |].
    exact Hobs.
  - intros [left_refined [right_refined [Hleft [Hright Hobs]]]].
    pose proof (phase1_admitted_observation_certificate left) as Hleft'.
    pose proof (phase1_admitted_observation_certificate right) as Hright'.
    rewrite Hleft in Hleft'.
    rewrite Hright in Hright'.
    inversion Hleft'; subst left_refined.
    inversion Hright'; subst right_refined.
    exact Hobs.
Qed.

Theorem phase1_surface_admitted_observation_equiv_reflexive :
  forall entry, phase1_surface_admitted_observation_equiv entry entry.
Proof.
  intros entry.
  reflexivity.
Qed.

Theorem phase1_surface_admitted_observation_equiv_symmetric :
  forall left right,
    phase1_surface_admitted_observation_equiv left right ->
    phase1_surface_admitted_observation_equiv right left.
Proof.
  intros left right Hobs.
  symmetry.
  exact Hobs.
Qed.

Theorem phase1_surface_admitted_observation_equiv_transitive :
  forall left middle right,
    phase1_surface_admitted_observation_equiv left middle ->
    phase1_surface_admitted_observation_equiv middle right ->
    phase1_surface_admitted_observation_equiv left right.
Proof.
  intros left middle right Hlm Hmr.
  transitivity (phase1_surface_admitted_observation middle);
    assumption.
Qed.

Theorem phase1_surface_admitted_observation_equiv_preserves_tag :
  forall left right,
    phase1_surface_admitted_observation_equiv left right ->
    phase1_declaration_spine_tag
      (phase1_admitted_observation_key left) =
    phase1_declaration_spine_tag
      (phase1_admitted_observation_key right).
Proof.
  intros left right Hobs.
  eapply phase1_surface_recursive_grouping_observation_related_preserves_tag.
  apply (proj1
    (phase1_surface_admitted_observation_equiv_iff_public_related
      left right)).
  exact Hobs.
Qed.

Theorem phase1_surface_admitted_observation_equiv_not_exact_key_equality :
  exists left right,
    phase1_surface_admitted_observation_equiv left right /\
    phase1_admitted_observation_key left <>
      phase1_admitted_observation_key right.
Proof.
  destruct phase1_surface_admitted_observation_collides_on_distinct_exact_keys
    as [left [right [Hleft [Hright [Hobs Hneq]]]]].
  exists
    {| phase1_admitted_observation_key :=
         phase1_surface_recursive_grouping_implementation_declaration_spine left;
       phase1_admitted_observation_refined := left;
       phase1_admitted_observation_certificate := Hleft |},
    {| phase1_admitted_observation_key :=
         phase1_surface_recursive_grouping_implementation_declaration_spine right;
       phase1_admitted_observation_refined := right;
       phase1_admitted_observation_certificate := Hright |}.
  split; simpl; assumption.
Qed.

Theorem phase1_surface_rejected_key_has_no_admitted_observation_representative :
  forall rejected,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      rejected = None ->
    ~ (exists entry : Phase1SurfaceAdmittedObservationKey,
        phase1_admitted_observation_key entry = rejected).
Proof.
  intros rejected Hreject [entry Hkey].
  pose proof (phase1_admitted_observation_certificate entry) as Hcert.
  rewrite Hkey in Hcert.
  rewrite Hreject in Hcert.
  discriminate Hcert.
Qed.
