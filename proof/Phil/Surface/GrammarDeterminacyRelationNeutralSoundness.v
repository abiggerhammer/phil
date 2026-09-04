From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Strings.String Lia.

From Phil.Surface Require Import
  Grammar
  GrammarDerivation
  GrammarDerivationLookahead
  GrammarDeterminacyDelimiterBalance
  GrammarDeterminacyStructuralResolvers
  GrammarDeterminacyStructuralScannerSoundness.

Import ListNotations.
Open Scope string_scope.

(*
  Semantic foundation for the relation-led proposition_atom resolver sites.

  The relation scanner only treats relation operators and proposition-atom
  boundaries specially at depth zero. Delimiter balance therefore makes every
  complete nonterminal safe when entered at positive depth. At depth zero we
  compute a greatest stable set of nonterminals whose rule bodies are relation-
  neutral, treating positive-depth calls as balanced identity transformers.
*)

Definition relation_neutral_string_mem
  (needle : string)
  (haystack : list string) : bool :=
  existsb (String.eqb needle) haystack.

Lemma relation_neutral_string_mem_true :
  forall needle haystack,
    relation_neutral_string_mem needle haystack = true ->
    In needle haystack.
Proof.
  intros needle haystack Hmem.
  unfold relation_neutral_string_mem in Hmem.
  apply existsb_exists in Hmem.
  destruct Hmem as [candidate [Hin Heq]].
  apply String.eqb_eq in Heq.
  subst candidate.
  exact Hin.
Qed.

Lemma relation_neutral_step_from_delimiter_shift :
  forall depth token final_depth extra,
    delimiter_balance_step depth token = Some final_depth ->
    relation_neutral_step (depth + S extra) token =
      Some (final_depth + S extra).
Proof.
  intros depth token final_depth extra Hstep.
  destruct token as [literal | class_name lexeme].
  - unfold delimiter_balance_step in Hstep.
    unfold relation_neutral_step.
    assert (Hpositive :
      Nat.eqb (depth + S extra) 0 = false).
    {
      apply Nat.eqb_neq.
      lia.
    }
    rewrite !Hpositive.
    simpl.
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

Lemma delimiter_balance_scan_relation_neutral_shift :
  forall depth tokens final_depth extra,
    delimiter_balance_scan depth tokens = Some final_depth ->
    relation_neutral_scan (depth + S extra) tokens =
      Some (final_depth + S extra).
Proof.
  intros depth tokens.
  revert depth.
  induction tokens as [| token tokens IH];
    intros depth final_depth extra Hscan.
  - simpl in Hscan.
    inversion Hscan; subst final_depth.
    reflexivity.
  - simpl in Hscan.
    destruct (delimiter_balance_step depth token)
      as [next_depth |] eqn:Hstep; try discriminate Hscan.
    simpl.
    rewrite
      (relation_neutral_step_from_delimiter_shift
        depth token next_depth extra Hstep).
    eapply IH.
    exact Hscan.
Qed.

Corollary delimiter_balanced_prefix_is_relation_neutral_positive :
  forall tokens extra,
    delimiter_balance_scan 0 tokens = Some 0 ->
    relation_neutral_scan (S extra) tokens = Some (S extra).
Proof.
  intros tokens extra Hscan.
  pose proof
    (delimiter_balance_scan_relation_neutral_shift
      0 tokens 0 extra Hscan)
    as Hshift.
  exact Hshift.
Qed.

Lemma relation_neutral_scan_app :
  forall depth first second middle_depth,
    relation_neutral_scan depth first = Some middle_depth ->
    relation_neutral_scan depth (first ++ second) =
      relation_neutral_scan middle_depth second.
Proof.
  intros depth first.
  revert depth.
  induction first as [| token first IH];
    intros depth second middle_depth Hscan.
  - simpl in Hscan.
    inversion Hscan; subst middle_depth.
    reflexivity.
  - simpl in Hscan |- *.
    destruct (relation_neutral_step depth token)
      as [next_depth |] eqn:Hstep; try discriminate Hscan.
    eapply IH.
    exact Hscan.
Qed.

Fixpoint relation_neutral_effect_fuel
  (safe_names : list string)
  (fuel depth : nat)
  (expression : EbnfExpression) : option nat :=
  match fuel with
  | O => None
  | S child_fuel =>
      match expression with
      | ELiteral literal =>
          relation_neutral_step depth (TLiteral literal)
      | ELexicalClass _ => Some depth
      | ENonterminal name =>
          match depth with
          | O =>
              if relation_neutral_string_mem name safe_names
              then Some O
              else None
          | S _ => Some depth
          end
      | ESequence items =>
          List.fold_left
            (fun state item =>
              match state with
              | Some current_depth =>
                  relation_neutral_effect_fuel
                    safe_names child_fuel current_depth item
              | None => None
              end)
            items (Some depth)
      | EAlternative items =>
          if forallb
            (fun item =>
              option_nat_isb
                (relation_neutral_effect_fuel
                  safe_names child_fuel depth item)
                depth)
            items
          then Some depth
          else None
      | EOptional body =>
          if option_nat_isb
            (relation_neutral_effect_fuel
              safe_names child_fuel depth body)
            depth
          then Some depth
          else None
      | ERepetition body =>
          if option_nat_isb
            (relation_neutral_effect_fuel
              safe_names child_fuel depth body)
            depth
          then Some depth
          else None
      end
  end.

Definition relation_neutral_sequence_effect_fuel
  (safe_names : list string)
  (fuel depth : nat)
  (items : list EbnfExpression) : option nat :=
  List.fold_left
    (fun state item =>
      match state with
      | Some current_depth =>
          relation_neutral_effect_fuel
            safe_names fuel current_depth item
      | None => None
      end)
    items (Some depth).

Definition relation_neutral_alternativeb
  (safe_names : list string)
  (fuel depth : nat)
  (items : list EbnfExpression) : bool :=
  forallb
    (fun item =>
      option_nat_isb
        (relation_neutral_effect_fuel safe_names fuel depth item)
        depth)
    items.

Lemma relation_neutral_sequence_fold_none :
  forall safe_names fuel items,
    List.fold_left
      (fun state item =>
        match state with
        | Some current_depth =>
            relation_neutral_effect_fuel
              safe_names fuel current_depth item
        | None => None
        end)
      items None = None.
Proof.
  intros safe_names fuel items.
  induction items as [| item items IH].
  - reflexivity.
  - simpl.
    exact IH.
Qed.

Lemma relation_neutral_effect_sequence_step :
  forall safe_names fuel depth items,
    relation_neutral_effect_fuel
      safe_names (S fuel) depth (ESequence items) =
    relation_neutral_sequence_effect_fuel
      safe_names fuel depth items.
Proof.
  reflexivity.
Qed.

Lemma relation_neutral_effect_alternative_step :
  forall safe_names fuel depth items,
    relation_neutral_effect_fuel
      safe_names (S fuel) depth (EAlternative items) =
    if relation_neutral_alternativeb
      safe_names fuel depth items
    then Some depth
    else None.
Proof.
  reflexivity.
Qed.

Lemma relation_neutral_effect_optional_step :
  forall safe_names fuel depth body,
    relation_neutral_effect_fuel
      safe_names (S fuel) depth (EOptional body) =
    if option_nat_isb
      (relation_neutral_effect_fuel
        safe_names fuel depth body)
      depth
    then Some depth
    else None.
Proof.
  reflexivity.
Qed.

Lemma relation_neutral_effect_repetition_step :
  forall safe_names fuel depth body,
    relation_neutral_effect_fuel
      safe_names (S fuel) depth (ERepetition body) =
    if option_nat_isb
      (relation_neutral_effect_fuel
        safe_names fuel depth body)
      depth
    then Some depth
    else None.
Proof.
  reflexivity.
Qed.

Lemma relation_neutral_effect_nonterminal_zero_step :
  forall safe_names fuel name,
    relation_neutral_effect_fuel
      safe_names (S fuel) 0 (ENonterminal name) =
    if relation_neutral_string_mem name safe_names
    then Some 0
    else None.
Proof.
  reflexivity.
Qed.

Lemma relation_neutral_effect_nonterminal_positive_step :
  forall safe_names fuel depth name,
    relation_neutral_effect_fuel
      safe_names (S fuel) (S depth) (ENonterminal name) =
    Some (S depth).
Proof.
  reflexivity.
Qed.

Definition relation_neutral_fuel : nat := 256.

Definition phase1_surface_relation_rule_names : list string :=
  map fst phase1_surface_rules.

Definition phase1_surface_relation_neutral_candidateb
  (safe_names : list string)
  (name : string) : bool :=
  match lookupRule name phase1_surface_rules with
  | Some body =>
      option_nat_isb
        (relation_neutral_effect_fuel
          safe_names relation_neutral_fuel 0 body)
        0
  | None => false
  end.

Definition phase1_surface_relation_neutral_pass
  (safe_names : list string) : list string :=
  filter
    (phase1_surface_relation_neutral_candidateb safe_names)
    safe_names.

Fixpoint iterate_relation_neutral_names
  (fuel : nat)
  (safe_names : list string) : list string :=
  match fuel with
  | O => safe_names
  | S remaining =>
      iterate_relation_neutral_names
        remaining
        (phase1_surface_relation_neutral_pass safe_names)
  end.

Definition phase1_surface_relation_neutral_names : list string :=
  iterate_relation_neutral_names 64 phase1_surface_relation_rule_names.

Theorem phase1_surface_relation_neutral_names_are_stable :
  phase1_surface_relation_neutral_pass
    phase1_surface_relation_neutral_names =
  phase1_surface_relation_neutral_names.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem phase1_surface_additive_expression_is_relation_neutral_name :
  relation_neutral_string_mem
    "additive_expression" phase1_surface_relation_neutral_names = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem phase1_surface_claim_application_is_relation_neutral_name :
  relation_neutral_string_mem
    "claim_application" phase1_surface_relation_neutral_names = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_relation_neutral_pass_member_candidate :
  forall safe_names name,
    phase1_surface_relation_neutral_pass safe_names = safe_names ->
    In name safe_names ->
    phase1_surface_relation_neutral_candidateb safe_names name = true.
Proof.
  intros safe_names name Hstable Hin.
  assert (Hin_pass :
    In name (phase1_surface_relation_neutral_pass safe_names)).
  {
    rewrite Hstable.
    exact Hin.
  }
  unfold phase1_surface_relation_neutral_pass in Hin_pass.
  apply filter_In in Hin_pass as [_ Hcandidate].
  exact Hcandidate.
Qed.

Opaque relation_neutral_effect_fuel.

Lemma phase1_surface_relation_neutral_name_body_effect_zero :
  forall name body,
    In name phase1_surface_relation_neutral_names ->
    lookupRule name phase1_surface_rules = Some body ->
    relation_neutral_effect_fuel
      phase1_surface_relation_neutral_names
      relation_neutral_fuel 0 body = Some 0.
Proof.
  intros name body Hin Hlookup.
  pose proof
    (phase1_surface_relation_neutral_pass_member_candidate
      phase1_surface_relation_neutral_names name
      phase1_surface_relation_neutral_names_are_stable Hin)
    as Hcandidate.
  unfold phase1_surface_relation_neutral_candidateb in Hcandidate.
  rewrite Hlookup in Hcandidate.
  apply option_nat_isb_true in Hcandidate.
  exact Hcandidate.
Qed.

Transparent relation_neutral_effect_fuel.

Theorem phase1_surface_relation_neutral_effect_sound :
  (forall path expression input rest tree,
    Derives phase1_surface_rules path expression input rest tree ->
    forall fuel depth final_depth,
      relation_neutral_effect_fuel
        phase1_surface_relation_neutral_names
        fuel depth expression = Some final_depth ->
      exists consumed,
        input = List.app consumed rest /\
        relation_neutral_scan depth consumed = Some final_depth) /\
  (forall path index items input rest trees,
    DerivesSequence phase1_surface_rules path index items input rest trees ->
    forall fuel depth final_depth,
      relation_neutral_sequence_effect_fuel
        phase1_surface_relation_neutral_names
        fuel depth items = Some final_depth ->
      exists consumed,
        input = List.app consumed rest /\
        relation_neutral_scan depth consumed = Some final_depth) /\
  (forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    forall fuel depth,
      relation_neutral_effect_fuel
        phase1_surface_relation_neutral_names
        fuel depth body = Some depth ->
      exists consumed,
        input = List.app consumed rest /\
        relation_neutral_scan depth consumed = Some depth).
Proof.
  apply Derivation_mutind.
  - intros path literal tail fuel depth final_depth Heffect.
    destruct fuel as [| fuel]; try discriminate Heffect.
    exists [TLiteral literal].
    split.
    + reflexivity.
    + change
        (relation_neutral_step depth (TLiteral literal) =
          Some final_depth)
        in Heffect.
      change
        (match relation_neutral_step depth (TLiteral literal) with
         | Some next_depth => Some next_depth
         | None => None
         end = Some final_depth).
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
    destruct depth as [| depth].
    + rewrite relation_neutral_effect_nonterminal_zero_step in Heffect.
      destruct
        (relation_neutral_string_mem
          name phase1_surface_relation_neutral_names)
        eqn:Hsafe; try discriminate Heffect.
      inversion Heffect; subst final_depth.
      apply relation_neutral_string_mem_true in Hsafe.
      pose proof
        (phase1_surface_relation_neutral_name_body_effect_zero
          name body Hsafe Hlookup)
        as Hbody_effect.
      eapply IH.
      exact Hbody_effect.
    + rewrite relation_neutral_effect_nonterminal_positive_step in Heffect.
      inversion Heffect; subst final_depth.
      assert (Houter :
        Derives phase1_surface_rules path
          (ENonterminal name) input rest
          (PTNonterminal name tree)).
      {
        eapply derives_nonterminal.
        - exact Hlookup.
        - exact Hderive.
      }
      destruct
        (phase1_surface_nonterminal_derivation_is_delimiter_balanced
          path name input rest
          (PTNonterminal name tree) Houter)
        as [consumed [Hinput Hbalanced]].
      exists consumed.
      split.
      * exact Hinput.
      * eapply delimiter_balanced_prefix_is_relation_neutral_positive.
        exact Hbalanced.
  - intros path items input rest trees Hderive IH
      fuel depth final_depth Heffect.
    destruct fuel as [| fuel]; try discriminate Heffect.
    rewrite relation_neutral_effect_sequence_step in Heffect.
    eapply IH.
    exact Heffect.
  - intros path items index item input rest tree Hnth Hderive IH
      fuel depth final_depth Heffect.
    destruct fuel as [| fuel]; try discriminate Heffect.
    rewrite relation_neutral_effect_alternative_step in Heffect.
    destruct
      (relation_neutral_alternativeb
        phase1_surface_relation_neutral_names
        fuel depth items)
      eqn:Hall; try discriminate Heffect.
    inversion Heffect; subst final_depth.
    unfold relation_neutral_alternativeb in Hall.
    rewrite forallb_forall in Hall.
    assert (Hin : In item items).
    {
      eapply nth_error_In.
      exact Hnth.
    }
    specialize (Hall item Hin).
    apply option_nat_isb_true in Hall.
    eapply IH.
    exact Hall.
  - intros path body input fuel depth final_depth Heffect.
    destruct fuel as [| fuel]; try discriminate Heffect.
    rewrite relation_neutral_effect_optional_step in Heffect.
    destruct
      (option_nat_isb
        (relation_neutral_effect_fuel
          phase1_surface_relation_neutral_names
          fuel depth body)
        depth)
      eqn:Hbody; try discriminate Heffect.
    inversion Heffect; subst final_depth.
    exists [].
    split; reflexivity.
  - intros path body input rest tree Hderive IH
      fuel depth final_depth Heffect.
    destruct fuel as [| fuel]; try discriminate Heffect.
    rewrite relation_neutral_effect_optional_step in Heffect.
    destruct
      (option_nat_isb
        (relation_neutral_effect_fuel
          phase1_surface_relation_neutral_names
          fuel depth body)
        depth)
      eqn:Hbody; try discriminate Heffect.
    inversion Heffect; subst final_depth.
    apply option_nat_isb_true in Hbody.
    eapply IH.
    exact Hbody.
  - intros path body input rest trees Hderive IH
      fuel depth final_depth Heffect.
    destruct fuel as [| fuel]; try discriminate Heffect.
    rewrite relation_neutral_effect_repetition_step in Heffect.
    destruct
      (option_nat_isb
        (relation_neutral_effect_fuel
          phase1_surface_relation_neutral_names
          fuel depth body)
        depth)
      eqn:Hbody; try discriminate Heffect.
    inversion Heffect; subst final_depth.
    apply option_nat_isb_true in Hbody.
    eapply IH.
    exact Hbody.
  - intros path index input fuel depth final_depth Heffect.
    unfold relation_neutral_sequence_effect_fuel in Heffect.
    simpl in Heffect.
    inversion Heffect; subst final_depth.
    exists [].
    split; reflexivity.
  - intros path index item items input middle rest tree trees
      Hitem IHitem Hitems IHitems
      fuel depth final_depth Heffect.
    unfold relation_neutral_sequence_effect_fuel in Heffect.
    simpl in Heffect.
    destruct
      (relation_neutral_effect_fuel
        phase1_surface_relation_neutral_names
        fuel depth item)
      as [middle_depth |] eqn:Hitem_effect.
    + change
        (relation_neutral_sequence_effect_fuel
          phase1_surface_relation_neutral_names
          fuel middle_depth items = Some final_depth)
        in Heffect.
      destruct (IHitem fuel depth middle_depth Hitem_effect)
        as [first [Hfirst_input Hfirst_scan]].
      destruct (IHitems fuel middle_depth final_depth Heffect)
        as [second [Hsecond_input Hsecond_scan]].
      exists (List.app first second).
      split.
      * eapply prefix_compose; eauto.
      * rewrite
          (relation_neutral_scan_app
            depth first second middle_depth Hfirst_scan).
        exact Hsecond_scan.
    + rewrite relation_neutral_sequence_fold_none in Heffect.
      discriminate Heffect.
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
    exists (List.app first second).
    split.
    + eapply prefix_compose; eauto.
    + rewrite
        (relation_neutral_scan_app
          depth first second depth Hfirst_scan).
      exact Hsecond_scan.
Qed.

Corollary phase1_surface_safe_nonterminal_derivation_is_relation_neutral :
  forall path name input rest tree,
    relation_neutral_string_mem
      name phase1_surface_relation_neutral_names = true ->
    Derives phase1_surface_rules path
      (ENonterminal name) input rest tree ->
    exists consumed,
      input = List.app consumed rest /\
      relation_neutral_scan 0 consumed = Some 0.
Proof.
  intros path name input rest tree Hsafe Hderive.
  eapply ((proj1 phase1_surface_relation_neutral_effect_sound)
    path (ENonterminal name) input rest tree Hderive 1 0 0).
  rewrite relation_neutral_effect_nonterminal_zero_step.
  rewrite Hsafe.
  reflexivity.
Qed.

Corollary phase1_surface_additive_expression_derivation_is_relation_neutral :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "additive_expression") input rest tree ->
    exists consumed,
      input = List.app consumed rest /\
      relation_neutral_scan 0 consumed = Some 0.
Proof.
  intros path input rest tree Hderive.
  eapply phase1_surface_safe_nonterminal_derivation_is_relation_neutral.
  - exact phase1_surface_additive_expression_is_relation_neutral_name.
  - exact Hderive.
Qed.

Corollary phase1_surface_claim_application_derivation_is_relation_neutral :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "claim_application") input rest tree ->
    exists consumed,
      input = List.app consumed rest /\
      relation_neutral_scan 0 consumed = Some 0.
Proof.
  intros path input rest tree Hderive.
  eapply phase1_surface_safe_nonterminal_derivation_is_relation_neutral.
  - exact phase1_surface_claim_application_is_relation_neutral_name.
  - exact Hderive.
Qed.
