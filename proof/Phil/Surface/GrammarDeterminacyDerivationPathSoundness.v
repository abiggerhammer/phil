From Stdlib Require Import Arith.PeanoNat Lists.List Lia.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDeterminacyPredictiveOracle.

Import ListNotations.

(*
  Path-context foundation for the final ordinary-derivation -> predictive-oracle
  bridge.

  Expression derivations carry their exact SyntaxPath directly. Sequence
  derivations are slightly subtler: their judgment keeps the remaining item
  suffix together with an absolute sequence index. The final mutual induction
  therefore needs a stable relation between that suffix/index pair and the
  whole ESequence stored at phase1_surface_expression_at_path.
*)

Definition phase1_surface_expression_path_context
  (path : SyntaxPath)
  (expression : EbnfExpression) : Prop :=
  phase1_surface_expression_at_path path = Some expression.

Definition phase1_surface_sequence_path_context
  (path : SyntaxPath)
  (index : nat)
  (items : list EbnfExpression) : Prop :=
  exists prefix,
    List.length prefix = index /\
    phase1_surface_expression_at_path path =
      Some (ESequence (prefix ++ items)).

Lemma nth_error_prefix_head :
  forall (A : Type) (prefix : list A) item suffix,
    nth_error (prefix ++ item :: suffix) (List.length prefix) = Some item.
Proof.
  intros A prefix.
  induction prefix as [| head prefix IH]; intros item suffix.
  - reflexivity.
  - simpl.
    exact (IH item suffix).
Qed.

Theorem phase1_surface_root_expression_path_context :
  phase1_surface_expression_path_context
    [] phase1_surface_root_expression.
Proof.
  reflexivity.
Qed.

Lemma phase1_surface_nonterminal_child_path_context :
  forall path name body,
    phase1_surface_expression_path_context path (ENonterminal name) ->
    lookupRule name phase1_surface_rules = Some body ->
    phase1_surface_expression_path_context
      (descend path (AtNonterminal name)) body.
Proof.
  intros path name body Hpath Hlookup.
  unfold phase1_surface_expression_path_context in *.
  rewrite (phase1_surface_expression_at_descend
    path (ENonterminal name) (AtNonterminal name) Hpath).
  unfold step_expression.
  rewrite String.eqb_refl.
  exact Hlookup.
Qed.

Lemma phase1_surface_alternative_child_path_context :
  forall path items index item,
    phase1_surface_expression_path_context path (EAlternative items) ->
    nth_error items index = Some item ->
    phase1_surface_expression_path_context
      (descend path (AtAlternative index)) item.
Proof.
  intros path items index item Hpath Hnth.
  unfold phase1_surface_expression_path_context in *.
  rewrite (phase1_surface_expression_at_descend
    path (EAlternative items) (AtAlternative index) Hpath).
  unfold step_expression.
  exact Hnth.
Qed.

Lemma phase1_surface_optional_child_path_context :
  forall path body,
    phase1_surface_expression_path_context path (EOptional body) ->
    phase1_surface_expression_path_context
      (descend path AtOptionalBody) body.
Proof.
  intros path body Hpath.
  unfold phase1_surface_expression_path_context in *.
  rewrite (phase1_surface_expression_at_descend
    path (EOptional body) AtOptionalBody Hpath).
  reflexivity.
Qed.

Lemma phase1_surface_repetition_child_path_context :
  forall path body,
    phase1_surface_expression_path_context path (ERepetition body) ->
    phase1_surface_expression_path_context
      (descend path AtRepetitionBody) body.
Proof.
  intros path body Hpath.
  unfold phase1_surface_expression_path_context in *.
  rewrite (phase1_surface_expression_at_descend
    path (ERepetition body) AtRepetitionBody Hpath).
  reflexivity.
Qed.

Lemma phase1_surface_sequence_initial_path_context :
  forall path items,
    phase1_surface_expression_path_context path (ESequence items) ->
    phase1_surface_sequence_path_context path 0 items.
Proof.
  intros path items Hpath.
  exists [].
  split.
  - reflexivity.
  - simpl.
    exact Hpath.
Qed.

Lemma phase1_surface_sequence_head_path_context :
  forall path index item items,
    phase1_surface_sequence_path_context path index (item :: items) ->
    phase1_surface_expression_path_context
      (descend path (AtSequence index)) item.
Proof.
  intros path index item items Hcontext.
  destruct Hcontext as [prefix [Hlength Hpath]].
  unfold phase1_surface_expression_path_context.
  rewrite (phase1_surface_expression_at_descend
    path (ESequence (prefix ++ item :: items))
    (AtSequence index) Hpath).
  unfold step_expression.
  rewrite <- Hlength.
  apply nth_error_prefix_head.
Qed.

Lemma phase1_surface_sequence_tail_path_context :
  forall path index item items,
    phase1_surface_sequence_path_context path index (item :: items) ->
    phase1_surface_sequence_path_context path (S index) items.
Proof.
  intros path index item items Hcontext.
  destruct Hcontext as [prefix [Hlength Hpath]].
  exists (prefix ++ [item]).
  split.
  - rewrite List.length_app.
    simpl.
    lia.
  - replace ((prefix ++ [item]) ++ items)
      with (prefix ++ item :: items).
    + exact Hpath.
    + rewrite <- List.app_assoc.
      reflexivity.
Qed.

Lemma phase1_surface_sequence_nil_path_context_shape :
  forall path index,
    phase1_surface_sequence_path_context path index [] ->
    exists prefix,
      List.length prefix = index /\
      phase1_surface_expression_at_path path = Some (ESequence prefix).
Proof.
  intros path index Hcontext.
  destruct Hcontext as [prefix [Hlength Hpath]].
  exists prefix.
  split.
  - exact Hlength.
  - rewrite List.app_nil_r in Hpath.
    exact Hpath.
Qed.

Theorem phase1_surface_complete_derivation_root_path_context :
  forall tokens tree,
    Phase1CompleteDerivation tokens tree ->
    phase1_surface_expression_path_context
      [] (ENonterminal phase1_surface_start).
Proof.
  intros tokens tree Hderive.
  exact phase1_surface_root_expression_path_context.
Qed.
