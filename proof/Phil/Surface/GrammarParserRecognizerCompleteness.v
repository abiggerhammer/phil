From Stdlib Require Import Lia Lists.List Strings.String.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationOracle
  GrammarDeterminacyPredictiveOracle
  GrammarDeterminacyMutualPredictiveBridge
  GrammarParserRecognizer.

Import ListNotations.
Open Scope string_scope.

(*
  Eventual completeness for the Grammar-v1 reference recognizer.

  A successful oracle-resolved derivation has a finite proof tree.  This theorem
  assigns that tree a sufficient recognizer fuel indirectly: there exists a
  threshold such that every threshold-plus-extra run returns the exact same
  rest/result pair.  The statement is deliberately stronger than mere existence
  of one lucky fuel value and avoids making any production parser strategy part
  of Grammar-v1 semantics.
*)

Theorem oracle_parse_fuel_eventually_complete :
  forall oracle rules goal input rest result,
    OracleDerives oracle rules goal input rest result ->
    exists required,
      forall extra,
        oracle_parse_fuel (required + extra)
          oracle rules goal input = Some (rest, result).
Proof.
  intros oracle rules goal input rest result Hderive.
  fix IH 7.
  destruct Hderive as
    [ path literal tail
    | path class lexeme tail
    | path name body input rest tree Hlookup Hbody
    | path items input rest trees Hitems
    | path items index item input rest tree Hdecision Hnth Hitem
    | path body input Hdecision
    | path body input rest tree Hdecision Hbody
    | path body input rest trees Hrepeat
    | path index input
    | path index item items input middle rest tree trees Hhead Htail
    | path body input Hdecision
    | path body input middle rest tree trees Hdecision Hbody Hprogress Htail
    ].
  - exists 1.
    intros extra.
    simpl.
    rewrite String.eqb_refl.
    reflexivity.
  - exists 1.
    intros extra.
    simpl.
    rewrite String.eqb_refl.
    reflexivity.
  - destruct (IH _ _ _ _ _ _ Hbody) as [required Hcomplete].
    exists (S required).
    intros extra.
    simpl.
    rewrite Hlookup.
    rewrite (Hcomplete extra).
    reflexivity.
  - destruct (IH _ _ _ _ _ _ Hitems) as [required Hcomplete].
    exists (S required).
    intros extra.
    simpl.
    rewrite (Hcomplete extra).
    reflexivity.
  - destruct (IH _ _ _ _ _ _ Hitem) as [required Hcomplete].
    exists (S required).
    intros extra.
    simpl.
    rewrite Hdecision.
    rewrite Hnth.
    rewrite (Hcomplete extra).
    reflexivity.
  - exists 1.
    intros extra.
    simpl.
    rewrite Hdecision.
    reflexivity.
  - destruct (IH _ _ _ _ _ _ Hbody) as [required Hcomplete].
    exists (S required).
    intros extra.
    simpl.
    rewrite Hdecision.
    rewrite (Hcomplete extra).
    reflexivity.
  - destruct (IH _ _ _ _ _ _ Hrepeat) as [required Hcomplete].
    exists (S required).
    intros extra.
    simpl.
    rewrite (Hcomplete extra).
    reflexivity.
  - exists 1.
    intros extra.
    simpl.
    reflexivity.
  - destruct (IH _ _ _ _ _ _ Hhead) as [head_required Hhead_complete].
    destruct (IH _ _ _ _ _ _ Htail) as [tail_required Htail_complete].
    exists (S (head_required + tail_required)).
    intros extra.
    simpl.
    replace ((head_required + tail_required) + extra)
      with (head_required + (tail_required + extra)) by lia.
    rewrite (Hhead_complete (tail_required + extra)).
    replace (head_required + (tail_required + extra))
      with (tail_required + (head_required + extra)) by lia.
    rewrite (Htail_complete (head_required + extra)).
    reflexivity.
  - exists 1.
    intros extra.
    simpl.
    rewrite Hdecision.
    reflexivity.
  - destruct (IH _ _ _ _ _ _ Hbody) as [body_required Hbody_complete].
    destruct (IH _ _ _ _ _ _ Htail) as [tail_required Htail_complete].
    exists (S (body_required + tail_required)).
    intros extra.
    simpl.
    rewrite Hdecision.
    replace ((body_required + tail_required) + extra)
      with (body_required + (tail_required + extra)) by lia.
    rewrite (Hbody_complete (tail_required + extra)).
    destruct (list_eq_dec concrete_token_eq_dec input middle)
      as [Hequal | Hdifferent].
    + exfalso.
      apply Hprogress.
      exact Hequal.
    + replace (body_required + (tail_required + extra))
        with (tail_required + (body_required + extra)) by lia.
      rewrite (Htail_complete (body_required + extra)).
      reflexivity.
Qed.

Theorem phase1_surface_predictive_parse_eventually_complete :
  forall tokens tree,
    OracleResolvedPhase1CompleteDerivation
      phase1_surface_predictive_oracle tokens tree ->
    exists required,
      forall extra,
        phase1_surface_predictive_parse_fuel (required + extra) tokens =
          Some ([], ResultTree tree).
Proof.
  intros tokens tree Hderive.
  unfold OracleResolvedPhase1CompleteDerivation,
    OracleResolvedExpression in Hderive.
  unfold phase1_surface_predictive_parse_fuel.
  eapply oracle_parse_fuel_eventually_complete.
  exact Hderive.
Qed.

Corollary phase1_surface_complete_derivation_eventually_recognized :
  forall tokens tree,
    Phase1CompleteDerivation tokens tree ->
    exists required,
      forall extra,
        phase1_surface_predictive_parse_fuel (required + extra) tokens =
          Some ([], ResultTree tree).
Proof.
  intros tokens tree Hderive.
  apply phase1_surface_predictive_parse_eventually_complete.
  apply phase1_surface_complete_derivation_predictive_oracle.
  exact Hderive.
Qed.
