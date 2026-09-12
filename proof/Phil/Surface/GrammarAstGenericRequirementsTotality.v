From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericRequirementsSpine
  GrammarAstStructuralModeTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the shared generic-requirements correspondence introduced by #946. *)

Definition phase1_surface_generic_requirement_items_for_totality
  : list EbnfExpression :=
  [ ESequence
      [ ELiteral "structural";
        ENonterminal "identifier";
        ELiteral ":";
        ENonterminal "identifier";
        ELiteral ";"
      ];
    ESequence
      [ ELiteral "proposition";
        ENonterminal "proposition";
        ELiteral ";"
      ];
    ESequence
      [ ELiteral "provider";
        ENonterminal "identifier";
        ELiteral ":";
        ENonterminal "type_expression";
        ELiteral ";"
      ];
    ESequence
      [ ELiteral "callable";
        ENonterminal "identifier";
        ELiteral ":";
        ENonterminal "type_expression";
        ELiteral ";"
      ];
    ESequence
      [ ELiteral "boundary";
        ENonterminal "identifier";
        ELiteral ":";
        ENonterminal "type_expression";
        ELiteral ";"
      ];
    ESequence
      [ ELiteral "architecture";
        ENonterminal "identifier";
        ELiteral ":";
        ENonterminal "type_expression";
        ELiteral ";"
      ];
    ESequence
      [ ELiteral "effects";
        ENonterminal "identifier";
        ELiteral "within";
        ENonterminal "effect_set_expression";
        ELiteral ";"
      ];
    ESequence
      [ ELiteral "authority";
        ENonterminal "type_expression";
        ELiteral ";"
      ];
    ESequence
      [ ELiteral "boundary";
        ELiteral "representation";
        ENonterminal "type_expression";
        ELiteral ";"
      ];
    ESequence
      [ ELiteral "representation";
        ENonterminal "proposition";
        ELiteral ";"
      ];
    ESequence
      [ ELiteral "placement";
        ENonterminal "proposition";
        ELiteral ";"
      ];
    ESequence
      [ ELiteral "cost";
        ENonterminal "proposition";
        ELiteral ";"
      ];
    ESequence
      [ ELiteral "environment";
        ENonterminal "proposition";
        ELiteral ";"
      ]
  ].

Lemma phase1_surface_generic_requirement_lookup_for_totality :
  lookupRule "generic_requirement" phase1_surface_rules =
    Some (EAlternative phase1_surface_generic_requirement_items_for_totality).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_generic_requirements_lookup_for_totality :
  lookupRule "generic_requirements" phase1_surface_rules =
    Some
      (ESequence
        [ ELiteral "requires";
          ELiteral "{";
          ERepetition (ENonterminal "generic_requirement");
          ELiteral "}"
        ]).
Proof.
  vm_compute.
  reflexivity.
Qed.

Definition phase1_surface_generic_requirement_expression_for_totality
  (tag : Phase1SurfaceGenericRequirementTag) : EbnfExpression :=
  match tag with
  | Phase1StructuralRequirement =>
      ESequence
        [ ELiteral "structural";
          ENonterminal "identifier";
          ELiteral ":";
          ENonterminal "identifier";
          ELiteral ";"
        ]
  | Phase1PropositionRequirement =>
      ESequence
        [ ELiteral "proposition";
          ENonterminal "proposition";
          ELiteral ";"
        ]
  | Phase1ProviderRequirement =>
      ESequence
        [ ELiteral "provider";
          ENonterminal "identifier";
          ELiteral ":";
          ENonterminal "type_expression";
          ELiteral ";"
        ]
  | Phase1CallableRequirement =>
      ESequence
        [ ELiteral "callable";
          ENonterminal "identifier";
          ELiteral ":";
          ENonterminal "type_expression";
          ELiteral ";"
        ]
  | Phase1BoundaryRequirement =>
      ESequence
        [ ELiteral "boundary";
          ENonterminal "identifier";
          ELiteral ":";
          ENonterminal "type_expression";
          ELiteral ";"
        ]
  | Phase1ArchitectureRequirement =>
      ESequence
        [ ELiteral "architecture";
          ENonterminal "identifier";
          ELiteral ":";
          ENonterminal "type_expression";
          ELiteral ";"
        ]
  | Phase1EffectsRequirement =>
      ESequence
        [ ELiteral "effects";
          ENonterminal "identifier";
          ELiteral "within";
          ENonterminal "effect_set_expression";
          ELiteral ";"
        ]
  | Phase1AuthorityRequirement =>
      ESequence
        [ ELiteral "authority";
          ENonterminal "type_expression";
          ELiteral ";"
        ]
  | Phase1BoundaryRepresentationRequirement =>
      ESequence
        [ ELiteral "boundary";
          ELiteral "representation";
          ENonterminal "type_expression";
          ELiteral ";"
        ]
  | Phase1RepresentationRequirement =>
      ESequence
        [ ELiteral "representation";
          ENonterminal "proposition";
          ELiteral ";"
        ]
  | Phase1PlacementRequirement =>
      ESequence
        [ ELiteral "placement";
          ENonterminal "proposition";
          ELiteral ";"
        ]
  | Phase1CostRequirement =>
      ESequence
        [ ELiteral "cost";
          ENonterminal "proposition";
          ELiteral ";"
        ]
  | Phase1EnvironmentRequirement =>
      ESequence
        [ ELiteral "environment";
          ENonterminal "proposition";
          ELiteral ";"
        ]
  end.

Lemma phase1_surface_generic_requirement_item_matches_tag :
  forall index item,
    nth_error phase1_surface_generic_requirement_items_for_totality index = Some item ->
    exists tag,
      phase1_surface_generic_requirement_tag_of_index index = Some tag /\
      item = phase1_surface_generic_requirement_expression_for_totality tag.
Proof.
  intros index item Hnth.
  destruct index as [|index]; cbn in Hnth.
  - inversion Hnth; subst item.
    exists Phase1StructuralRequirement. split; reflexivity.
  - destruct index as [|index]; cbn in Hnth.
    + inversion Hnth; subst item.
      exists Phase1PropositionRequirement. split; reflexivity.
    + destruct index as [|index]; cbn in Hnth.
      * inversion Hnth; subst item.
        exists Phase1ProviderRequirement. split; reflexivity.
      * destruct index as [|index]; cbn in Hnth.
        -- inversion Hnth; subst item.
           exists Phase1CallableRequirement. split; reflexivity.
        -- destruct index as [|index]; cbn in Hnth.
           ++ inversion Hnth; subst item.
              exists Phase1BoundaryRequirement. split; reflexivity.
           ++ destruct index as [|index]; cbn in Hnth.
              ** inversion Hnth; subst item.
                 exists Phase1ArchitectureRequirement. split; reflexivity.
              ** destruct index as [|index]; cbn in Hnth.
                 --- inversion Hnth; subst item.
                     exists Phase1EffectsRequirement. split; reflexivity.
                 --- destruct index as [|index]; cbn in Hnth.
                     +++ inversion Hnth; subst item.
                         exists Phase1AuthorityRequirement. split; reflexivity.
                     +++ destruct index as [|index]; cbn in Hnth.
                         *** inversion Hnth; subst item.
                             exists Phase1BoundaryRepresentationRequirement.
                             split; reflexivity.
                         *** destruct index as [|index]; cbn in Hnth.
                             ---- inversion Hnth; subst item.
                                  exists Phase1RepresentationRequirement.
                                  split; reflexivity.
                             ---- destruct index as [|index]; cbn in Hnth.
                                  ++++ inversion Hnth; subst item.
                                       exists Phase1PlacementRequirement.
                                       split; reflexivity.
                                  ++++ destruct index as [|index]; cbn in Hnth.
                                       ***** inversion Hnth; subst item.
                                             exists Phase1CostRequirement.
                                             split; reflexivity.
                                       ***** destruct index as [|index]; cbn in Hnth.
                                             ------ inversion Hnth; subst item.
                                                    exists Phase1EnvironmentRequirement.
                                                    split; reflexivity.
                                             ------ discriminate Hnth.
Qed.

Lemma phase1_surface_validate_named_node_total_from_derivation :
  forall name path input rest tree,
    Derives phase1_surface_rules path (ENonterminal name)
      input rest tree ->
    phase1_surface_validate_named_node name tree = Some tt.
Proof.
  intros name path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path name
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite Htree.
  unfold phase1_surface_validate_named_node,
    phase1_surface_expect_nonterminal.
  cbn.
  rewrite String.eqb_refl.
  reflexivity.
Qed.

Lemma phase1_surface_validate_structural_requirement_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ESequence
        [ ELiteral "structural";
          ENonterminal "identifier";
          ELiteral ":";
          ENonterminal "identifier";
          ELiteral ";"
        ])
      input rest tree ->
    phase1_surface_validate_structural_requirement tree = Some tt.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral "structural";
        ENonterminal "identifier";
        ELiteral ":";
        ENonterminal "identifier";
        ELiteral ";"
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hkeyword : Derives phase1_surface_rules _
      (ELiteral "structural") _ _ ?keyword_tree,
    Hname : Derives phase1_surface_rules _
      (ENonterminal "identifier") _ _ ?name_tree,
    Hcolon : Derives phase1_surface_rules _
      (ELiteral ":") _ _ ?colon_tree,
    Hrequired : Derives phase1_surface_rules _
      (ENonterminal "identifier") _ _ ?required_tree,
    Hterminator : Derives phase1_surface_rules _
      (ELiteral ";") _ _ ?terminator_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "structural" _ _ keyword_tree Hkeyword)
        as [keyword_tail [_ [_ Hkeyword_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ ":" _ _ colon_tree Hcolon)
        as [colon_tail [_ [_ Hcolon_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ ";" _ _ terminator_tree Hterminator)
        as [terminator_tail [_ [_ Hterminator_tree]]];
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "identifier" _ _ _ name_tree Hname) as Hname_validate;
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "identifier" _ _ _ required_tree Hrequired) as Hrequired_validate;
      rewrite Htree, Hkeyword_tree, Hcolon_tree, Hterminator_tree;
      unfold phase1_surface_validate_structural_requirement,
        phase1_surface_expect_sequence,
        phase1_surface_exact5,
        phase1_surface_expect_literal;
      cbn;
      rewrite Hname_validate, Hrequired_validate;
      reflexivity
  end.
Qed.

Lemma phase1_surface_validate_proposition_requirement_total_from_derivation :
  forall keyword path input rest tree,
    Derives phase1_surface_rules path
      (ESequence
        [ ELiteral keyword;
          ENonterminal "proposition";
          ELiteral ";"
        ])
      input rest tree ->
    phase1_surface_validate_proposition_requirement keyword tree = Some tt.
Proof.
  intros keyword path input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral keyword;
        ENonterminal "proposition";
        ELiteral ";"
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hkeyword : Derives phase1_surface_rules _
      (ELiteral keyword) _ _ ?keyword_tree,
    Hproposition : Derives phase1_surface_rules _
      (ENonterminal "proposition") _ _ ?proposition_tree,
    Hterminator : Derives phase1_surface_rules _
      (ELiteral ";") _ _ ?terminator_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ keyword _ _ keyword_tree Hkeyword)
        as [keyword_tail [_ [_ Hkeyword_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ ";" _ _ terminator_tree Hterminator)
        as [terminator_tail [_ [_ Hterminator_tree]]];
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "proposition" _ _ _ proposition_tree Hproposition)
        as Hproposition_validate;
      rewrite Htree, Hkeyword_tree, Hterminator_tree;
      unfold phase1_surface_validate_proposition_requirement,
        phase1_surface_expect_sequence,
        phase1_surface_exact3,
        phase1_surface_expect_literal;
      cbn;
      rewrite Hproposition_validate;
      reflexivity
  end.
Qed.

Lemma phase1_surface_validate_named_type_requirement_total_from_derivation :
  forall keyword path input rest tree,
    Derives phase1_surface_rules path
      (ESequence
        [ ELiteral keyword;
          ENonterminal "identifier";
          ELiteral ":";
          ENonterminal "type_expression";
          ELiteral ";"
        ])
      input rest tree ->
    phase1_surface_validate_named_type_requirement keyword tree = Some tt.
Proof.
  intros keyword path input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral keyword;
        ENonterminal "identifier";
        ELiteral ":";
        ENonterminal "type_expression";
        ELiteral ";"
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hkeyword : Derives phase1_surface_rules _
      (ELiteral keyword) _ _ ?keyword_tree,
    Hname : Derives phase1_surface_rules _
      (ENonterminal "identifier") _ _ ?name_tree,
    Hcolon : Derives phase1_surface_rules _
      (ELiteral ":") _ _ ?colon_tree,
    Htype : Derives phase1_surface_rules _
      (ENonterminal "type_expression") _ _ ?type_tree,
    Hterminator : Derives phase1_surface_rules _
      (ELiteral ";") _ _ ?terminator_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ keyword _ _ keyword_tree Hkeyword)
        as [keyword_tail [_ [_ Hkeyword_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ ":" _ _ colon_tree Hcolon)
        as [colon_tail [_ [_ Hcolon_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ ";" _ _ terminator_tree Hterminator)
        as [terminator_tail [_ [_ Hterminator_tree]]];
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "identifier" _ _ _ name_tree Hname) as Hname_validate;
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "type_expression" _ _ _ type_tree Htype) as Htype_validate;
      rewrite Htree, Hkeyword_tree, Hcolon_tree, Hterminator_tree;
      unfold phase1_surface_validate_named_type_requirement,
        phase1_surface_expect_sequence,
        phase1_surface_exact5,
        phase1_surface_expect_literal;
      cbn;
      rewrite Hname_validate, Htype_validate;
      reflexivity
  end.
Qed.

Lemma phase1_surface_validate_effects_requirement_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ESequence
        [ ELiteral "effects";
          ENonterminal "identifier";
          ELiteral "within";
          ENonterminal "effect_set_expression";
          ELiteral ";"
        ])
      input rest tree ->
    phase1_surface_validate_effects_requirement tree = Some tt.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral "effects";
        ENonterminal "identifier";
        ELiteral "within";
        ENonterminal "effect_set_expression";
        ELiteral ";"
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hkeyword : Derives phase1_surface_rules _
      (ELiteral "effects") _ _ ?keyword_tree,
    Hname : Derives phase1_surface_rules _
      (ENonterminal "identifier") _ _ ?name_tree,
    Hwithin : Derives phase1_surface_rules _
      (ELiteral "within") _ _ ?within_tree,
    Heffects : Derives phase1_surface_rules _
      (ENonterminal "effect_set_expression") _ _ ?effects_tree,
    Hterminator : Derives phase1_surface_rules _
      (ELiteral ";") _ _ ?terminator_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "effects" _ _ keyword_tree Hkeyword)
        as [keyword_tail [_ [_ Hkeyword_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "within" _ _ within_tree Hwithin)
        as [within_tail [_ [_ Hwithin_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ ";" _ _ terminator_tree Hterminator)
        as [terminator_tail [_ [_ Hterminator_tree]]];
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "identifier" _ _ _ name_tree Hname) as Hname_validate;
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "effect_set_expression" _ _ _ effects_tree Heffects) as Heffects_validate;
      rewrite Htree, Hkeyword_tree, Hwithin_tree, Hterminator_tree;
      unfold phase1_surface_validate_effects_requirement,
        phase1_surface_expect_sequence,
        phase1_surface_exact5,
        phase1_surface_expect_literal;
      cbn;
      rewrite Hname_validate, Heffects_validate;
      reflexivity
  end.
Qed.

Lemma phase1_surface_validate_type_only_requirement_total_from_derivation :
  forall keyword path input rest tree,
    Derives phase1_surface_rules path
      (ESequence
        [ ELiteral keyword;
          ENonterminal "type_expression";
          ELiteral ";"
        ])
      input rest tree ->
    phase1_surface_validate_type_only_requirement keyword tree = Some tt.
Proof.
  intros keyword path input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral keyword;
        ENonterminal "type_expression";
        ELiteral ";"
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hkeyword : Derives phase1_surface_rules _
      (ELiteral keyword) _ _ ?keyword_tree,
    Htype : Derives phase1_surface_rules _
      (ENonterminal "type_expression") _ _ ?type_tree,
    Hterminator : Derives phase1_surface_rules _
      (ELiteral ";") _ _ ?terminator_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ keyword _ _ keyword_tree Hkeyword)
        as [keyword_tail [_ [_ Hkeyword_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ ";" _ _ terminator_tree Hterminator)
        as [terminator_tail [_ [_ Hterminator_tree]]];
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "type_expression" _ _ _ type_tree Htype) as Htype_validate;
      rewrite Htree, Hkeyword_tree, Hterminator_tree;
      unfold phase1_surface_validate_type_only_requirement,
        phase1_surface_expect_sequence,
        phase1_surface_exact3,
        phase1_surface_expect_literal;
      cbn;
      rewrite Htype_validate;
      reflexivity
  end.
Qed.

Lemma phase1_surface_validate_boundary_representation_requirement_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ESequence
        [ ELiteral "boundary";
          ELiteral "representation";
          ENonterminal "type_expression";
          ELiteral ";"
        ])
      input rest tree ->
    phase1_surface_validate_boundary_representation_requirement tree = Some tt.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral "boundary";
        ELiteral "representation";
        ENonterminal "type_expression";
        ELiteral ";"
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hboundary : Derives phase1_surface_rules _
      (ELiteral "boundary") _ _ ?boundary_tree,
    Hrepresentation : Derives phase1_surface_rules _
      (ELiteral "representation") _ _ ?representation_tree,
    Htype : Derives phase1_surface_rules _
      (ENonterminal "type_expression") _ _ ?type_tree,
    Hterminator : Derives phase1_surface_rules _
      (ELiteral ";") _ _ ?terminator_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "boundary" _ _ boundary_tree Hboundary)
        as [boundary_tail [_ [_ Hboundary_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "representation" _ _ representation_tree Hrepresentation)
        as [representation_tail [_ [_ Hrepresentation_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ ";" _ _ terminator_tree Hterminator)
        as [terminator_tail [_ [_ Hterminator_tree]]];
      pose proof
        (phase1_surface_validate_named_node_total_from_derivation
          "type_expression" _ _ _ type_tree Htype) as Htype_validate;
      rewrite Htree, Hboundary_tree, Hrepresentation_tree, Hterminator_tree;
      unfold phase1_surface_validate_boundary_representation_requirement,
        phase1_surface_expect_sequence,
        phase1_surface_exact4,
        phase1_surface_expect_literal;
      cbn;
      rewrite Htype_validate;
      reflexivity
  end.
Qed.

Lemma phase1_surface_validate_generic_requirement_selected_total_from_derivation :
  forall tag path input rest tree,
    Derives phase1_surface_rules path
      (phase1_surface_generic_requirement_expression_for_totality tag)
      input rest tree ->
    phase1_surface_validate_generic_requirement_selected tag tree = Some tt.
Proof.
  intros tag path input rest tree Hderive.
  destruct tag; cbn in Hderive |- *.
  - eapply phase1_surface_validate_structural_requirement_total_from_derivation.
    exact Hderive.
  - eapply phase1_surface_validate_proposition_requirement_total_from_derivation.
    exact Hderive.
  - eapply phase1_surface_validate_named_type_requirement_total_from_derivation.
    exact Hderive.
  - eapply phase1_surface_validate_named_type_requirement_total_from_derivation.
    exact Hderive.
  - eapply phase1_surface_validate_named_type_requirement_total_from_derivation.
    exact Hderive.
  - eapply phase1_surface_validate_named_type_requirement_total_from_derivation.
    exact Hderive.
  - eapply phase1_surface_validate_effects_requirement_total_from_derivation.
    exact Hderive.
  - eapply phase1_surface_validate_type_only_requirement_total_from_derivation.
    exact Hderive.
  - eapply phase1_surface_validate_boundary_representation_requirement_total_from_derivation.
    exact Hderive.
  - eapply phase1_surface_validate_proposition_requirement_total_from_derivation.
    exact Hderive.
  - eapply phase1_surface_validate_proposition_requirement_total_from_derivation.
    exact Hderive.
  - eapply phase1_surface_validate_proposition_requirement_total_from_derivation.
    exact Hderive.
  - eapply phase1_surface_validate_proposition_requirement_total_from_derivation.
    exact Hderive.
Qed.

Lemma phase1_surface_normalize_generic_requirement_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "generic_requirement")
      input rest tree ->
    exists requirement,
      phase1_surface_normalize_generic_requirement_spine tree = Some requirement /\
      phase1_surface_generic_requirement_spine_tree requirement = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "generic_requirement"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_generic_requirement_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "generic_requirement"))
      phase1_surface_generic_requirement_items_for_totality
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct
    (phase1_surface_generic_requirement_item_matches_tag index item Hnth)
    as [tag [Htag Hitem]].
  subst item.
  pose proof
    (phase1_surface_validate_generic_requirement_selected_total_from_derivation
      tag
      (descend
        (descend path (AtNonterminal "generic_requirement"))
        (AtAlternative index))
      input rest selected Hselected) as Hvalidate.
  let requirement := constr:(
    {| phase1_generic_requirement_spine_tag := tag;
       phase1_generic_requirement_spine_selected_tree := selected |}) in
  assert (Hnormalize :
    phase1_surface_normalize_generic_requirement_spine tree = Some requirement).
  {
    rewrite Htree.
    rewrite Hsubtree.
    unfold phase1_surface_normalize_generic_requirement_spine,
      phase1_surface_expect_nonterminal,
      phase1_surface_expect_alternative.
    cbn.
    rewrite Htag.
    rewrite Hvalidate.
    reflexivity.
  }
  exists requirement.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_generic_requirement_spine_round_trip.
    exact Hnormalize.
Qed.

Lemma phase1_surface_normalize_generic_requirement_spines_total_from_repetition :
  forall path body input rest trees,
    DerivesRepetition phase1_surface_rules path body input rest trees ->
    body = ENonterminal "generic_requirement" ->
    exists requirements,
      phase1_surface_normalize_generic_requirement_spines trees =
        Some requirements.
Proof.
  intros path body input rest trees Hderive.
  induction Hderive as
    [path body input
    |path body input middle rest tree trees
       Hbody Hprogress Hrest IHrest];
    intros Hbody_shape.
  - exists [].
    reflexivity.
  - subst body.
    destruct
      (phase1_surface_normalize_generic_requirement_spine_total_from_derivation
        (descend path AtRepetitionBody)
        input middle tree Hbody)
      as [requirement [Htree Htree_round_trip]].
    destruct (IHrest eq_refl) as [requirements Hrequirements].
    exists (requirement :: requirements).
    cbn.
    rewrite Htree.
    rewrite Hrequirements.
    reflexivity.
Qed.

Lemma phase1_surface_normalize_generic_requirements_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "generic_requirements")
      input rest tree ->
    exists requirements,
      phase1_surface_normalize_generic_requirements_spine tree =
        Some requirements /\
      phase1_surface_generic_requirements_spine_tree requirements = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "generic_requirements"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_generic_requirements_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "generic_requirements"))
      [ ELiteral "requires";
        ELiteral "{";
        ERepetition (ENonterminal "generic_requirement");
        ELiteral "}"
      ]
      input rest subtree Hbody)
    as [trees [Hsubtree Hitems]].
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hrequires : Derives phase1_surface_rules _
      (ELiteral "requires") _ _ ?requires_tree,
    Hopen : Derives phase1_surface_rules _
      (ELiteral "{") _ _ ?open_tree,
    Hentries : Derives phase1_surface_rules _
      (ERepetition (ENonterminal "generic_requirement")) _ _ ?entries_tree,
    Hclose : Derives phase1_surface_rules _
      (ELiteral "}") _ _ ?close_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "requires" _ _ requires_tree Hrequires)
        as [requires_tail [_ [_ Hrequires_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "{" _ _ open_tree Hopen)
        as [open_tail [_ [_ Hopen_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "}" _ _ close_tree Hclose)
        as [close_tail [_ [_ Hclose_tree]]];
      destruct
        (phase1_surface_repetition_derivation_exposes
          _ (ENonterminal "generic_requirement")
          _ _ entries_tree Hentries)
        as [entries [Hentries_tree Hentries_body]];
      destruct
        (phase1_surface_normalize_generic_requirement_spines_total_from_repetition
          _ (ENonterminal "generic_requirement")
          _ _ entries Hentries_body eq_refl)
        as [normalized Hnormalized];
      let requirements := constr:(
        {| phase1_generic_requirements_spine_entries := normalized |}) in
      assert (Hnormalize :
        phase1_surface_normalize_generic_requirements_spine tree =
          Some requirements);
      [ rewrite Htree, Hsubtree, Hrequires_tree, Hopen_tree,
          Hentries_tree, Hclose_tree;
        unfold phase1_surface_normalize_generic_requirements_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_sequence,
          phase1_surface_exact4,
          phase1_surface_expect_literal,
          phase1_surface_expect_repetition;
        cbn;
        rewrite Hnormalized;
        reflexivity
      | exists requirements;
        split;
        [ exact Hnormalize
        | eapply phase1_surface_normalize_generic_requirements_spine_round_trip;
          exact Hnormalize ] ]
  end.
Qed.

Lemma phase1_surface_normalize_optional_generic_requirements_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (EOptional (ENonterminal "generic_requirements"))
      input rest tree ->
    exists requirements,
      phase1_surface_normalize_optional_generic_requirements tree =
        Some requirements /\
      phase1_surface_optional_generic_requirements_tree requirements = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (optional_derivation_exposes_presence
      phase1_surface_rules path
      (ENonterminal "generic_requirements")
      input rest tree Hderive)
    as [[_ Hnone] | [body [Hsome Hbody]]].
  - assert (Hnormalize :
      phase1_surface_normalize_optional_generic_requirements tree = Some None).
    {
      rewrite Hnone.
      reflexivity.
    }
    exists None.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_optional_generic_requirements_round_trip.
      exact Hnormalize.
  - destruct
      (phase1_surface_normalize_generic_requirements_spine_total_from_derivation
        (descend path AtOptionalBody)
        input rest body Hbody)
      as [requirements [Hrequirements Hrequirements_round_trip]].
    assert (Hnormalize :
      phase1_surface_normalize_optional_generic_requirements tree =
        Some (Some requirements)).
    {
      rewrite Hsome.
      unfold phase1_surface_normalize_optional_generic_requirements,
        phase1_surface_expect_optional.
      cbn.
      rewrite Hrequirements.
      reflexivity.
    }
    exists (Some requirements).
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_optional_generic_requirements_round_trip.
      exact Hnormalize.
Qed.

Lemma phase1_surface_record_decl_requirements_lookup_for_totality :
  exists fields_expr,
    lookupRule "record_decl" phase1_surface_rules =
      Some
        (ESequence
          [ ELiteral "record";
            ENonterminal "identifier";
            EOptional (ENonterminal "generic_params");
            EOptional
              (ESequence
                [ ELiteral "mode";
                  ENonterminal "structural_mode"
                ]);
            EOptional (ENonterminal "generic_requirements");
            ELiteral "{";
            fields_expr;
            ELiteral "}"
          ]).
Proof.
  vm_compute.
  eexists.
  reflexivity.
Qed.

Theorem phase1_surface_normalize_record_requirements_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_record_requirements_tree tree = Some refined /\
      phase1_surface_record_requirements_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct phase1_surface_record_decl_requirements_lookup_for_totality
    as [fields_expr Hlookup_exact].
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "record_decl"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite Hlookup_exact in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules
      (descend path (AtNonterminal "record_decl"))
      [ ELiteral "record";
        ENonterminal "identifier";
        EOptional (ENonterminal "generic_params");
        EOptional
          (ESequence
            [ ELiteral "mode";
              ENonterminal "structural_mode"
            ]);
        EOptional (ENonterminal "generic_requirements");
        ELiteral "{";
        fields_expr;
        ELiteral "}"
      ]
      input rest subtree Hbody)
    as [trees [Hsubtree Hitems]].
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hkeyword : Derives phase1_surface_rules _
      (ELiteral "record") _ _ ?keyword_tree,
    Hname : Derives phase1_surface_rules _
      (ENonterminal "identifier") _ _ ?name_tree,
    Hgeneric : Derives phase1_surface_rules _
      (EOptional (ENonterminal "generic_params")) _ _ ?generic_tree,
    Hmode : Derives phase1_surface_rules _
      (EOptional
        (ESequence
          [ ELiteral "mode";
            ENonterminal "structural_mode"
          ])) _ _ ?mode_tree,
    Hrequirements : Derives phase1_surface_rules _
      (EOptional (ENonterminal "generic_requirements")) _ _ ?requirements_tree,
    Hopen : Derives phase1_surface_rules _
      (ELiteral "{") _ _ ?open_tree,
    Hfields : Derives phase1_surface_rules _
      fields_expr _ _ ?fields_tree,
    Hclose : Derives phase1_surface_rules _
      (ELiteral "}") _ _ ?close_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "record" _ _ keyword_tree Hkeyword)
        as [keyword_tail [_ [_ Hkeyword_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "{" _ _ open_tree Hopen)
        as [open_tail [_ [_ Hopen_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "}" _ _ close_tree Hclose)
        as [close_tail [_ [_ Hclose_tree]]];
      destruct
        (phase1_surface_normalize_identifier_total_from_derivation
          _ _ _ name_tree Hname)
        as [name Hname_normalize];
      destruct
        (phase1_surface_normalize_optional_generic_params_total_from_derivation
          _ _ _ generic_tree Hgeneric)
        as [parameters [Hgeneric_normalize Hgeneric_round_trip]];
      destruct
        (phase1_surface_normalize_optional_mode_total_from_derivation
          _ _ _ mode_tree Hmode)
        as [mode [Hmode_normalize Hmode_round_trip]];
      destruct
        (phase1_surface_normalize_optional_generic_requirements_total_from_derivation
          _ _ _ requirements_tree Hrequirements)
        as [requirements [Hrequirements_normalize Hrequirements_round_trip]];
      let refined := constr:(
        {| phase1_record_requirements_spine_name := name;
           phase1_record_requirements_spine_generic_params := parameters;
           phase1_record_requirements_spine_mode := mode;
           phase1_record_requirements_spine_requirements := requirements;
           phase1_record_requirements_spine_fields_tree := fields_tree |}) in
      assert (Hnormalize :
        phase1_surface_normalize_record_requirements_tree tree = Some refined).
      {
        rewrite Htree.
        rewrite Hsubtree.
        rewrite Hkeyword_tree.
        rewrite Hopen_tree.
        rewrite Hclose_tree.
        unfold phase1_surface_normalize_record_requirements_tree,
          phase1_surface_normalize_record_mode_tree,
          phase1_surface_normalize_record_generic_tree,
          phase1_surface_normalize_record_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_sequence,
          phase1_surface_exact8,
          phase1_surface_expect_literal,
          phase1_surface_normalize_record_generic_spine,
          phase1_surface_normalize_record_mode_spine,
          phase1_surface_normalize_record_requirements_spine.
        cbn.
        rewrite Hname_normalize.
        rewrite Hgeneric_normalize.
        rewrite Hmode_normalize.
        rewrite Hrequirements_normalize.
        reflexivity.
      }
      exists refined.
      split.
      + exact Hnormalize.
      + eapply phase1_surface_normalize_record_requirements_tree_round_trip.
        exact Hnormalize
  end.
Qed.
