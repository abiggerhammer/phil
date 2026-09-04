From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Strings.String Lia.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationLookahead
  GrammarDeterminacyStructuralResolvers.

Import ListNotations.
Open Scope string_scope.

(*
  Delimiter-balance foundation for the structural resolver soundness proof.

  The scanners from GrammarDeterminacyStructuralResolvers distinguish commas,
  closes, and relation operators only at their current top level.  To skip a
  nested nonterminal safely, the final structural bridge therefore needs one
  global fact: every complete Grammar-v1 nonterminal consumes a delimiter-
  balanced token prefix.

  The checker below is an abstract interpretation of the generated EBNF.  It
  treats a nonterminal reference as an identity transformer and checks every
  generated rule body against that assumption.  Soundness is then proved by
  induction over ordinary derivations: a recursive nonterminal call is smaller
  derivation evidence, while the checked rule table supplies the body balance
  fact needed by the induction hypothesis.
*)

Definition delimiter_balance_step
  (depth : nat)
  (token : ConcreteToken) : option nat :=
  match token with
  | TLiteral literal =>
      if delimiter_open_literalb literal
      then Some (S depth)
      else if delimiter_close_literalb literal
      then
        match depth with
        | O => None
        | S remaining_depth => Some remaining_depth
        end
      else Some depth
  | TLexical _ _ => Some depth
  end.

Fixpoint delimiter_balance_scan
  (depth : nat)
  (tokens : list ConcreteToken) : option nat :=
  match tokens with
  | [] => Some depth
  | token :: rest =>
      match delimiter_balance_step depth token with
      | Some next_depth => delimiter_balance_scan next_depth rest
      | None => None
      end
  end.

Definition option_nat_isb
  (value : option nat)
  (expected : nat) : bool :=
  match value with
  | Some actual => Nat.eqb actual expected
  | None => false
  end.

Lemma option_nat_isb_true :
  forall value expected,
    option_nat_isb value expected = true ->
    value = Some expected.
Proof.
  intros value expected Hvalue.
  destruct value as [actual |]; simpl in Hvalue; try discriminate.
  apply Nat.eqb_eq in Hvalue.
  subst actual.
  reflexivity.
Qed.

Lemma option_nat_isb_some_refl :
  forall value,
    option_nat_isb (Some value) value = true.
Proof.
  intros value.
  unfold option_nat_isb.
  now rewrite Nat.eqb_refl.
Qed.

Fixpoint delimiter_effect_fuel
  (fuel depth : nat)
  (expression : EbnfExpression) : option nat :=
  match fuel with
  | O => None
  | S child_fuel =>
      match expression with
      | ELiteral literal =>
          delimiter_balance_step depth (TLiteral literal)
      | ELexicalClass _ => Some depth
      | ENonterminal _ => Some depth
      | ESequence items =>
          List.fold_left
            (fun state item =>
              match state with
              | Some current_depth =>
                  delimiter_effect_fuel child_fuel current_depth item
              | None => None
              end)
            items (Some depth)
      | EAlternative items =>
          if forallb
            (fun item =>
              option_nat_isb
                (delimiter_effect_fuel child_fuel depth item)
                depth)
            items
          then Some depth
          else None
      | EOptional body =>
          if option_nat_isb
            (delimiter_effect_fuel child_fuel depth body) depth
          then Some depth
          else None
      | ERepetition body =>
          if option_nat_isb
            (delimiter_effect_fuel child_fuel depth body) depth
          then Some depth
          else None
      end
  end.

Definition delimiter_sequence_effect_fuel
  (fuel depth : nat)
  (items : list EbnfExpression) : option nat :=
  List.fold_left
    (fun state item =>
      match state with
      | Some current_depth =>
          delimiter_effect_fuel fuel current_depth item
      | None => None
      end)
    items (Some depth).

Definition delimiter_alternative_balanced_fuel
  (fuel depth : nat)
  (items : list EbnfExpression) : bool :=
  forallb
    (fun item =>
      option_nat_isb (delimiter_effect_fuel fuel depth item) depth)
    items.

Lemma delimiter_effect_sequence_step :
  forall fuel depth items,
    delimiter_effect_fuel (S fuel) depth (ESequence items) =
    delimiter_sequence_effect_fuel fuel depth items.
Proof.
  reflexivity.
Qed.

Lemma delimiter_effect_alternative_step :
  forall fuel depth items,
    delimiter_effect_fuel (S fuel) depth (EAlternative items) =
    if delimiter_alternative_balanced_fuel fuel depth items
    then Some depth
    else None.
Proof.
  reflexivity.
Qed.

Lemma delimiter_effect_optional_step :
  forall fuel depth body,
    delimiter_effect_fuel (S fuel) depth (EOptional body) =
    if option_nat_isb (delimiter_effect_fuel fuel depth body) depth
    then Some depth
    else None.
Proof.
  reflexivity.
Qed.

Lemma delimiter_effect_repetition_step :
  forall fuel depth body,
    delimiter_effect_fuel (S fuel) depth (ERepetition body) =
    if option_nat_isb (delimiter_effect_fuel fuel depth body) depth
    then Some depth
    else None.
Proof.
  reflexivity.
Qed.

Lemma delimiter_balance_step_shift :
  forall depth token final_depth extra,
    delimiter_balance_step depth token = Some final_depth ->
    delimiter_balance_step (depth + extra) token =
      Some (final_depth + extra).
Proof.
  intros depth token final_depth extra Hstep.
  destruct token as [literal | class_name lexeme].
  - unfold delimiter_balance_step in *.
    destruct (delimiter_open_literalb literal) eqn:Hopen.
    + inversion Hstep; subst final_depth.
      reflexivity.
    + destruct (delimiter_close_literalb literal) eqn:Hclose.
      * destruct depth as [| depth].
        -- discriminate Hstep.
        -- inversion Hstep; subst final_depth.
           reflexivity.
      * inversion Hstep; subst final_depth.
        reflexivity.
  - inversion Hstep; subst final_depth.
    reflexivity.
Qed.

Lemma delimiter_balance_scan_app :
  forall depth first second middle_depth,
    delimiter_balance_scan depth first = Some middle_depth ->
    delimiter_balance_scan depth (first ++ second) =
      delimiter_balance_scan middle_depth second.
Proof.
  intros depth first.
  revert depth.
  induction first as [| token first IH];
    intros depth second middle_depth Hscan.
  - simpl in Hscan.
    inversion Hscan; subst middle_depth.
    reflexivity.
  - simpl in Hscan |- *.
    destruct (delimiter_balance_step depth token)
      as [next_depth |] eqn:Hstep; try discriminate.
    eapply IH.
    exact Hscan.
Qed.

Lemma delimiter_effect_fuel_shift :
  forall fuel expression depth final_depth extra,
    delimiter_effect_fuel fuel depth expression = Some final_depth ->
    delimiter_effect_fuel fuel (depth + extra) expression =
      Some (final_depth + extra).
Proof.
  induction fuel as [| fuel IH];
    intros expression depth final_depth extra Heffect.
  - discriminate Heffect.
  - destruct expression as
      [literal | class_name | name | items | items | body | body].
    + change
        (delimiter_balance_step depth (TLiteral literal) = Some final_depth)
        in Heffect.
      change
        (delimiter_balance_step (depth + extra) (TLiteral literal) =
          Some (final_depth + extra)).
      eapply delimiter_balance_step_shift.
      exact Heffect.
    + inversion Heffect; subst final_depth.
      reflexivity.
    + inversion Heffect; subst final_depth.
      reflexivity.
    + rewrite delimiter_effect_sequence_step in Heffect |- *.
      unfold delimiter_sequence_effect_fuel in *.
      revert depth final_depth Heffect.
      induction items as [| item items IHitems];
        intros depth final_depth Heffect.
      * simpl in Heffect |- *.
        inversion Heffect; subst final_depth.
        reflexivity.
      * simpl in Heffect |- *.
        destruct (delimiter_effect_fuel fuel depth item)
          as [middle_depth |] eqn:Hitem; try discriminate.
        pose proof
          (IH item depth middle_depth extra Hitem)
          as Hitem_shift.
        rewrite Hitem_shift.
        eapply IHitems.
        exact Heffect.
    + rewrite delimiter_effect_alternative_step in Heffect |- *.
      destruct
        (delimiter_alternative_balanced_fuel fuel depth items)
        eqn:Hall; try discriminate.
      inversion Heffect; subst final_depth.
      assert (Hall_shift :
        delimiter_alternative_balanced_fuel
          fuel (depth + extra) items = true).
      {
        unfold delimiter_alternative_balanced_fuel in *.
        apply forallb_forall.
        intros item Hin.
        apply forallb_forall in Hall.
        specialize (Hall item Hin).
        apply option_nat_isb_true in Hall.
        pose proof
          (IH item depth depth extra Hall)
          as Hitem_shift.
        rewrite Hitem_shift.
        apply option_nat_isb_some_refl.
      }
      rewrite Hall_shift.
      reflexivity.
    + rewrite delimiter_effect_optional_step in Heffect |- *.
      destruct
        (option_nat_isb (delimiter_effect_fuel fuel depth body) depth)
        eqn:Hbody; try discriminate.
      inversion Heffect; subst final_depth.
      apply option_nat_isb_true in Hbody.
      pose proof
        (IH body depth depth extra Hbody)
        as Hbody_shift.
      rewrite Hbody_shift.
      rewrite option_nat_isb_some_refl.
      reflexivity.
    + rewrite delimiter_effect_repetition_step in Heffect |- *.
      destruct
        (option_nat_isb (delimiter_effect_fuel fuel depth body) depth)
        eqn:Hbody; try discriminate.
      inversion Heffect; subst final_depth.
      apply option_nat_isb_true in Hbody.
      pose proof
        (IH body depth depth extra Hbody)
        as Hbody_shift.
      rewrite Hbody_shift.
      rewrite option_nat_isb_some_refl.
      reflexivity.
Qed.

Definition delimiter_fuel : nat := 256.

Definition delimiter_rule_body_balancedb
  (rule : GrammarRule) : bool :=
  option_nat_isb
    (delimiter_effect_fuel delimiter_fuel 0 (snd rule)) 0.

Theorem phase1_surface_all_rule_bodies_are_delimiter_balanced :
  forallb delimiter_rule_body_balancedb phase1_surface_rules = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma forallb_lookup_rule_body :
  forall (predicate : EbnfExpression -> bool) rules name body,
    forallb (fun rule => predicate (snd rule)) rules = true ->
    lookupRule name rules = Some body ->
    predicate body = true.
Proof.
  intros predicate rules.
  induction rules as [| [candidate candidate_body] rest IH];
    intros name body Hall Hlookup.
  - discriminate Hlookup.
  - simpl in Hall.
    apply andb_true_iff in Hall as [Hhead Hrest].
    simpl in Hlookup.
    destruct (String.eqb name candidate) eqn:Hname.
    + inversion Hlookup; subst body.
      exact Hhead.
    + eapply IH; eauto.
Qed.

Lemma phase1_surface_lookup_rule_delimiter_effect_zero :
  forall name body,
    lookupRule name phase1_surface_rules = Some body ->
    delimiter_effect_fuel delimiter_fuel 0 body = Some 0.
Proof.
  intros name body Hlookup.
  pose proof
    (forallb_lookup_rule_body
      delimiter_rule_body_balancedb
      phase1_surface_rules name body
      phase1_surface_all_rule_bodies_are_delimiter_balanced
      Hlookup)
    as Hbalanced.
  unfold delimiter_rule_body_balancedb in Hbalanced.
  apply option_nat_isb_true in Hbalanced.
  exact Hbalanced.
Qed.

Theorem phase1_surface_delimiter_effect_sound :
  (forall path expression input rest tree,
    Derives phase1_surface_rules path expression input rest tree ->
    forall fuel depth final_depth,
      delimiter_effect_fuel fuel depth expression = Some final_depth ->
      exists consumed,
        input = consumed ++ rest /\
        delimiter_balance_scan depth consumed = Some final_depth) /\
  (forall path index items input rest trees,
    DerivesSequence phase1_surface_rules path index items input rest trees ->
    forall fuel depth final_depth,
      delimiter_sequence_effect_fuel fuel depth items = Some final_depth ->
      exists consumed,
        input = consumed ++ rest /\
        delimiter_balance_scan depth consumed = Some final_depth) /\
  (forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    forall fuel depth,
      delimiter_effect_fuel fuel depth body = Some depth ->
      exists consumed,
        input = consumed ++ rest /\
        delimiter_balance_scan depth consumed = Some depth).
Proof.
  apply Derivation_mutind.
  - intros path literal tail fuel depth final_depth Heffect.
    destruct fuel as [| fuel]; try discriminate Heffect.
    exists [TLiteral literal].
    split; first reflexivity.
    simpl in Heffect |- *.
    rewrite Heffect.
    reflexivity.
  - intros path class_name lexeme tail fuel depth final_depth Heffect.
    destruct fuel as [| fuel]; try discriminate Heffect.
    inversion Heffect; subst final_depth.
    exists [TLexical class_name lexeme].
    split; reflexivity.
  - intros path name body input rest tree Hlookup Hderive IH
      fuel depth final_depth Heffect.
    destruct fuel as [| fuel]; try discriminate Heffect.
    inversion Heffect; subst final_depth.
    pose proof
      (phase1_surface_lookup_rule_delimiter_effect_zero
        name body Hlookup)
      as Hbody_zero.
    pose proof
      (delimiter_effect_fuel_shift
        delimiter_fuel body 0 0 depth Hbody_zero)
      as Hbody_depth.
    simpl in Hbody_depth.
    eapply IH.
    exact Hbody_depth.
  - intros path items input rest trees Hderive IH
      fuel depth final_depth Heffect.
    destruct fuel as [| fuel]; try discriminate Heffect.
    rewrite delimiter_effect_sequence_step in Heffect.
    eapply IH.
    exact Heffect.
  - intros path items index item input rest tree Hnth Hderive IH
      fuel depth final_depth Heffect.
    destruct fuel as [| fuel]; try discriminate Heffect.
    rewrite delimiter_effect_alternative_step in Heffect.
    destruct
      (delimiter_alternative_balanced_fuel fuel depth items)
      eqn:Hall; try discriminate Heffect.
    inversion Heffect; subst final_depth.
    apply forallb_forall in Hall.
    assert (Hin : In item items).
    { eapply nth_error_In. exact Hnth. }
    specialize (Hall item Hin).
    apply option_nat_isb_true in Hall.
    eapply IH.
    exact Hall.
  - intros path body input fuel depth final_depth Heffect.
    destruct fuel as [| fuel]; try discriminate Heffect.
    rewrite delimiter_effect_optional_step in Heffect.
    destruct
      (option_nat_isb (delimiter_effect_fuel fuel depth body) depth)
      eqn:Hbody; try discriminate Heffect.
    inversion Heffect; subst final_depth.
    exists [].
    split; reflexivity.
  - intros path body input rest tree Hderive IH
      fuel depth final_depth Heffect.
    destruct fuel as [| fuel]; try discriminate Heffect.
    rewrite delimiter_effect_optional_step in Heffect.
    destruct
      (option_nat_isb (delimiter_effect_fuel fuel depth body) depth)
      eqn:Hbody; try discriminate Heffect.
    inversion Heffect; subst final_depth.
    apply option_nat_isb_true in Hbody.
    eapply IH.
    exact Hbody.
  - intros path body input rest trees Hderive IH
      fuel depth final_depth Heffect.
    destruct fuel as [| fuel]; try discriminate Heffect.
    rewrite delimiter_effect_repetition_step in Heffect.
    destruct
      (option_nat_isb (delimiter_effect_fuel fuel depth body) depth)
      eqn:Hbody; try discriminate Heffect.
    inversion Heffect; subst final_depth.
    apply option_nat_isb_true in Hbody.
    eapply IH.
    exact Hbody.
  - intros path index input fuel depth final_depth Heffect.
    unfold delimiter_sequence_effect_fuel in Heffect.
    simpl in Heffect.
    inversion Heffect; subst final_depth.
    exists [].
    split; reflexivity.
  - intros path index item items input middle rest tree trees
      Hitem IHitem Hitems IHitems
      fuel depth final_depth Heffect.
    unfold delimiter_sequence_effect_fuel in Heffect.
    simpl in Heffect.
    destruct (delimiter_effect_fuel fuel depth item)
      as [middle_depth |] eqn:Hitem_effect; try discriminate Heffect.
    change
      (delimiter_sequence_effect_fuel
        fuel middle_depth items = Some final_depth)
      in Heffect.
    destruct (IHitem fuel depth middle_depth Hitem_effect)
      as [first [Hfirst_input Hfirst_scan]].
    destruct (IHitems fuel middle_depth final_depth Heffect)
      as [second [Hsecond_input Hsecond_scan]].
    exists (first ++ second).
    split.
    + eapply prefix_compose; eauto.
    + rewrite
        (delimiter_balance_scan_app
          depth first second middle_depth Hfirst_scan).
      exact Hsecond_scan.
  - intros path body input fuel depth Hbody_effect.
    exists [].
    split; reflexivity.
  - intros path body input middle rest tree trees
      Hbody IHbody Hprogress Hrest IHrest
      fuel depth Hbody_effect.
    destruct (IHbody fuel depth depth Hbody_effect)
      as [first [Hfirst_input Hfirst_scan]].
    destruct (IHrest fuel depth Hbody_effect)
      as [second [Hsecond_input Hsecond_scan]].
    exists (first ++ second).
    split.
    + eapply prefix_compose; eauto.
    + rewrite
        (delimiter_balance_scan_app
          depth first second depth Hfirst_scan).
      exact Hsecond_scan.
Qed.

Corollary phase1_surface_nonterminal_derivation_is_delimiter_balanced :
  forall path name input rest tree,
    Derives phase1_surface_rules path (ENonterminal name)
      input rest tree ->
    exists consumed,
      input = consumed ++ rest /\
      delimiter_balance_scan 0 consumed = Some 0.
Proof.
  intros path name input rest tree Hderive.
  eapply (proj1 phase1_surface_delimiter_effect_sound).
  - exact Hderive.
  - unfold delimiter_fuel.
    reflexivity.
Qed.
