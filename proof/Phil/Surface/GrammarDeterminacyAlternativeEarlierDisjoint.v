From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Strings.String Lia.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyNullableFirst
  GrammarDeterminacyFollowOverlap
  GrammarDeterminacyOracleAssemblyCoverage
  GrammarDeterminacyOracleAssemblyReflection.

Import ListNotations.
Open Scope string_scope.

(*
  Mechanical FIRST-disjointness foundation for the resolver-None half of the
  final PHIL-SURFACE-DETERM-001 alternative conversion.

  At a resolver root, global pairwise-FIRST disjointness is intentionally
  false: those are exactly the certified overlap sites.  For a selected branch
  we only need disjointness from *earlier* branches.  This file checks that
  property per branch and records the small set of later indices for which it
  is false.  Those exception indices are precisely the resolver-backed overlap
  alternatives; the successor semantic slice will eliminate them when the
  certified resolver returns None.
*)

Fixpoint earlier_first_disjointb
  (selected : EbnfExpression)
  (items : list EbnfExpression)
  (count : nat) : bool :=
  match count, items with
  | O, _ => true
  | S remaining, [] => false
  | S remaining, head :: rest =>
      andb
        (expression_first_disjointb head selected)
        (earlier_first_disjointb selected rest remaining)
  end.

Definition selected_earlier_first_disjointb
  (items : list EbnfExpression)
  (index : nat) : bool :=
  match nth_error items index with
  | Some selected => earlier_first_disjointb selected items index
  | None => false
  end.

Lemma earlier_first_disjointb_nth_lt :
  forall items selected count earlier_index earlier,
    earlier_first_disjointb selected items count = true ->
    earlier_index < count ->
    nth_error items earlier_index = Some earlier ->
    expression_first_disjointb earlier selected = true.
Proof.
  intros items selected count.
  revert items.
  induction count as [| count IH];
    intros items earlier_index earlier Hcheck Hlt Hnth.
  - lia.
  - destruct items as [| head rest].
    + discriminate Hcheck.
    + simpl in Hcheck.
      apply andb_true_iff in Hcheck as [Hhead Hrest].
      destruct earlier_index as [| earlier_index].
      * simpl in Hnth.
        inversion Hnth; subst head.
        exact Hhead.
      * simpl in Hnth.
        eapply IH.
        -- exact Hrest.
        -- apply Nat.succ_lt_mono in Hlt. exact Hlt.
        -- exact Hnth.
Qed.

Theorem selected_earlier_first_disjointb_sound :
  forall items index selected earlier_index earlier,
    selected_earlier_first_disjointb items index = true ->
    nth_error items index = Some selected ->
    earlier_index < index ->
    nth_error items earlier_index = Some earlier ->
    token_intersection
      (first_expression
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        earlier)
      (first_expression
        phase1_surface_nullable_facts
        phase1_surface_first_facts
        selected) = [].
Proof.
  intros items index selected earlier_index earlier
    Hcheck Hselected Hlt Hearlier.
  unfold selected_earlier_first_disjointb in Hcheck.
  rewrite Hselected in Hcheck.
  apply expression_first_disjointb_sound.
  eapply earlier_first_disjointb_nth_lt.
  - exact Hcheck.
  - exact Hlt.
  - exact Hearlier.
Qed.

Definition nat_memb (needle : nat) (haystack : list nat) : bool :=
  existsb (Nat.eqb needle) haystack.

Definition alternative_exception_coverageb
  (items : list EbnfExpression)
  (exceptions : list nat) : bool :=
  forallb
    (fun index =>
      orb
        (nat_memb index exceptions)
        (selected_earlier_first_disjointb items index))
    (seq 0 (length items)).

Lemma alternative_exception_coverage_selected :
  forall items exceptions index selected,
    alternative_exception_coverageb items exceptions = true ->
    nth_error items index = Some selected ->
    nat_memb index exceptions = true \/
    selected_earlier_first_disjointb items index = true.
Proof.
  intros items exceptions index selected Hcoverage Hselected.
  unfold alternative_exception_coverageb in Hcoverage.
  apply forallb_forall in Hcoverage.
  assert (Hlt : index < length items).
  {
    apply nth_error_Some.
    rewrite Hselected.
    discriminate.
  }
  assert (Hin : In index (seq 0 (length items))).
  {
    apply in_seq.
    lia.
  }
  specialize (Hcoverage index Hin).
  apply orb_true_iff in Hcoverage.
  exact Hcoverage.
Qed.

Definition phase1_surface_resolver_declaration_items : list EbnfExpression :=
  match lookupRule "declaration" phase1_surface_rules with
  | Some (EAlternative items) => items
  | _ => []
  end.

Definition phase1_surface_resolver_generic_requirement_items : list EbnfExpression :=
  match lookupRule "generic_requirement" phase1_surface_rules with
  | Some (EAlternative items) => items
  | _ => []
  end.

Definition phase1_surface_resolver_pattern_items : list EbnfExpression :=
  match lookupRule "pattern" phase1_surface_rules with
  | Some (EAlternative items) => items
  | _ => []
  end.

Definition phase1_surface_resolver_primary_expression_items : list EbnfExpression :=
  match lookupRule "primary_expression" phase1_surface_rules with
  | Some (EAlternative items) => items
  | _ => []
  end.

Definition phase1_surface_resolver_proposition_atom_items : list EbnfExpression :=
  match lookupRule "proposition_atom" phase1_surface_rules with
  | Some (EAlternative items) => items
  | _ => []
  end.

Definition phase1_surface_resolver_static_argument_items : list EbnfExpression :=
  match lookupRule "static_argument" phase1_surface_rules with
  | Some (EAlternative items) => items
  | _ => []
  end.

Lemma phase1_surface_resolver_declaration_lookup_exact :
  lookupRule "declaration" phase1_surface_rules =
    Some (EAlternative phase1_surface_resolver_declaration_items).
Proof. vm_compute. reflexivity. Qed.

Lemma phase1_surface_resolver_generic_requirement_lookup_exact :
  lookupRule "generic_requirement" phase1_surface_rules =
    Some (EAlternative phase1_surface_resolver_generic_requirement_items).
Proof. vm_compute. reflexivity. Qed.

Lemma phase1_surface_resolver_pattern_lookup_exact :
  lookupRule "pattern" phase1_surface_rules =
    Some (EAlternative phase1_surface_resolver_pattern_items).
Proof. vm_compute. reflexivity. Qed.

Lemma phase1_surface_resolver_primary_expression_lookup_exact :
  lookupRule "primary_expression" phase1_surface_rules =
    Some (EAlternative phase1_surface_resolver_primary_expression_items).
Proof. vm_compute. reflexivity. Qed.

Lemma phase1_surface_resolver_proposition_atom_lookup_exact :
  lookupRule "proposition_atom" phase1_surface_rules =
    Some (EAlternative phase1_surface_resolver_proposition_atom_items).
Proof. vm_compute. reflexivity. Qed.

Lemma phase1_surface_resolver_static_argument_lookup_exact :
  lookupRule "static_argument" phase1_surface_rules =
    Some (EAlternative phase1_surface_resolver_static_argument_items).
Proof. vm_compute. reflexivity. Qed.

Definition declaration_resolver_exception_indices : list nat := [6; 7].
Definition generic_requirement_resolver_exception_indices : list nat := [4; 8].
Definition pattern_resolver_exception_indices : list nat := [2].
Definition primary_expression_resolver_exception_indices : list nat := [1].
Definition proposition_atom_resolver_exception_indices : list nat := [1; 2; 3; 4].
Definition static_argument_resolver_exception_indices : list nat := [2; 3].

Theorem phase1_surface_declaration_resolver_exception_coverage :
  alternative_exception_coverageb
    phase1_surface_resolver_declaration_items
    declaration_resolver_exception_indices = true.
Proof. vm_compute. reflexivity. Qed.

Theorem phase1_surface_generic_requirement_resolver_exception_coverage :
  alternative_exception_coverageb
    phase1_surface_resolver_generic_requirement_items
    generic_requirement_resolver_exception_indices = true.
Proof. vm_compute. reflexivity. Qed.

Theorem phase1_surface_pattern_resolver_exception_coverage :
  alternative_exception_coverageb
    phase1_surface_resolver_pattern_items
    pattern_resolver_exception_indices = true.
Proof. vm_compute. reflexivity. Qed.

Theorem phase1_surface_primary_expression_resolver_exception_coverage :
  alternative_exception_coverageb
    phase1_surface_resolver_primary_expression_items
    primary_expression_resolver_exception_indices = true.
Proof. vm_compute. reflexivity. Qed.

Theorem phase1_surface_proposition_atom_resolver_exception_coverage :
  alternative_exception_coverageb
    phase1_surface_resolver_proposition_atom_items
    proposition_atom_resolver_exception_indices = true.
Proof. vm_compute. reflexivity. Qed.

Theorem phase1_surface_static_argument_resolver_exception_coverage :
  alternative_exception_coverageb
    phase1_surface_resolver_static_argument_items
    static_argument_resolver_exception_indices = true.
Proof. vm_compute. reflexivity. Qed.
