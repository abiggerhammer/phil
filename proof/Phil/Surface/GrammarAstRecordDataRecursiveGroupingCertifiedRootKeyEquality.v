From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingTaggedAdmissionInjectivity
  GrammarAstRecordDataRecursiveGroupingCertifiedAdmissionFibers
  GrammarAstRecordDataRecursiveGroupingCertifiedFiberEquality.

Open Scope string_scope.

(*
  Bounded G3: a pair of independently canonical Record-or-Data root
  derivations admits implementation values with equal values iff their
  declaration tags and selected trees both agree. The two same-root
  cases compose certified fiber equality; mixed roots compose certified
  fiber disjointness. Source derivation witnesses are mandatory.

  This does not validate arbitrary public tag/tree carriers, establish
  production parser binding, or discharge G2/G4 or whole-source claims.
  Absence and present-empty requirements remain distinguishable.
*)

Theorem phase1_surface_certified_record_data_root_admission_key_equality_iff :
  forall left_path left_input left_rest left_tree left_tag
         right_path right_input right_rest right_tree right_tag,
    ((Derives phase1_surface_rules left_path (ENonterminal "record_decl")
        left_input left_rest left_tree /\
      left_tag = Phase1RecordDeclaration) \/
     (Derives phase1_surface_rules left_path (ENonterminal "data_decl")
        left_input left_rest left_tree /\
      left_tag = Phase1DataDeclaration)) ->
    ((Derives phase1_surface_rules right_path (ENonterminal "record_decl")
        right_input right_rest right_tree /\
      right_tag = Phase1RecordDeclaration) \/
     (Derives phase1_surface_rules right_path (ENonterminal "data_decl")
        right_input right_rest right_tree /\
      right_tag = Phase1DataDeclaration)) ->
    exists left_refined right_refined,
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        {| phase1_declaration_spine_tag := left_tag;
           phase1_declaration_spine_selected_tree := left_tree |} =
        Some left_refined /\
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        {| phase1_declaration_spine_tag := right_tag;
           phase1_declaration_spine_selected_tree := right_tree |} =
        Some right_refined /\
      (left_refined = right_refined <->
        left_tag = right_tag /\ left_tree = right_tree).
Proof.
  intros left_path left_input left_rest left_tree left_tag
    right_path right_input right_rest right_tree right_tag
    Hleft Hright.
  destruct Hleft as [[Hleft Hleft_tag] | [Hleft Hleft_tag]];
    destruct Hright as [[Hright Hright_tag] | [Hright Hright_tag]];
    subst left_tag right_tag.
  - destruct (phase1_surface_certified_record_root_fiber_equality_iff
      left_path left_input left_rest left_tree
      right_path right_input right_rest right_tree Hleft Hright)
      as [left_refined [right_refined
        [Hleft_normalize [Hright_normalize Hiff]]]].
    exists left_refined, right_refined.
    split; [exact Hleft_normalize |].
    split; [exact Hright_normalize |].
    split.
    + intro Hequal.
      split; [reflexivity |].
      exact ((proj1 Hiff) Hequal).
    + intros [_ Htree].
      exact ((proj2 Hiff) Htree).
  - destruct (phase1_surface_certified_record_data_admission_fibers_disjoint
      left_path left_input left_rest left_tree
      right_path right_input right_rest right_tree Hleft Hright)
      as [record_refined [data_refined
        [Hrecord_normalize [Hdata_normalize Hdistinct]]]].
    exists record_refined, data_refined.
    split; [exact Hrecord_normalize |].
    split; [exact Hdata_normalize |].
    split.
    + intro Hequal.
      exfalso.
      exact (Hdistinct Hequal).
    + intros [Htag _].
      discriminate Htag.
  - destruct (phase1_surface_certified_record_data_admission_fibers_disjoint
      right_path right_input right_rest right_tree
      left_path left_input left_rest left_tree Hright Hleft)
      as [record_refined [data_refined
        [Hrecord_normalize [Hdata_normalize Hdistinct]]]].
    exists data_refined, record_refined.
    split; [exact Hdata_normalize |].
    split; [exact Hrecord_normalize |].
    split.
    + intro Hequal.
      exfalso.
      apply Hdistinct.
      symmetry.
      exact Hequal.
    + intros [Htag _].
      discriminate Htag.
  - destruct (phase1_surface_certified_data_root_fiber_equality_iff
      left_path left_input left_rest left_tree
      right_path right_input right_rest right_tree Hleft Hright)
      as [left_refined [right_refined
        [Hleft_normalize [Hright_normalize Hiff]]]].
    exists left_refined, right_refined.
    split; [exact Hleft_normalize |].
    split; [exact Hright_normalize |].
    split.
    + intro Hequal.
      split; [reflexivity |].
      exact ((proj1 Hiff) Hequal).
    + intros [_ Htree].
      exact ((proj2 Hiff) Htree).
Qed.

Example phase1_surface_certified_root_key_absent_requirements_admitted :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    phase1_surface_tagged_absent_requirements_spine =
    Some (Phase1RecursiveGroupingImplementationRecordDeclaration
      phase1_surface_impl_absent_requirements_record).
Proof.
  exact phase1_surface_tagged_absent_requirements_still_accepted.
Qed.

Example phase1_surface_certified_root_key_requirements_presence_distinct :
  forall absent present,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      phase1_surface_tagged_absent_requirements_spine = Some absent ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      phase1_surface_tagged_present_empty_requirements_spine = Some present ->
    absent <> present.
Proof.
  exact phase1_surface_absent_present_empty_fiber_values_remain_unequal.
Qed.

Example phase1_surface_certified_root_key_malformed_literal_rejected :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
       phase1_declaration_spine_selected_tree := PTLiteral "Nat" |} = None.
Proof.
  exact phase1_surface_wrong_literal_record_fiber_rejected.
Qed.
