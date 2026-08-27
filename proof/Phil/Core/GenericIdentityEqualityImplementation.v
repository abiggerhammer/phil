From Stdlib Require Import Bool.Bool.

From Phil.Core Require Import GenericIdentity.

(*
  PHIL-GEN-ID-IMPL-001 — executable equality facts for generic application
  identity and discharge lineage.

  Rich production identities remain outside the normalized proof model.  The
  executable kernel consumes only native equality facts supplied by the
  production representation layer.
*)

Record GenericApplicationEqualityFacts : Type :=
  mkGenericApplicationEqualityFacts {
    applicationDeclarationMatches : bool;
    applicationInterfaceMatches : bool;
    applicationArgumentsMatch : bool
  }.

Definition sameApplicationFactsb
  (facts : GenericApplicationEqualityFacts) : bool :=
  andb
    (applicationDeclarationMatches facts)
    (andb
      (applicationInterfaceMatches facts)
      (applicationArgumentsMatch facts)).

Inductive GenericApplicationEqualityDecision : Type :=
| GenericApplicationEqual
| GenericApplicationDifferent.

Definition decideGenericApplicationEquality
  (facts : GenericApplicationEqualityFacts)
  : GenericApplicationEqualityDecision :=
  if sameApplicationFactsb facts
  then GenericApplicationEqual
  else GenericApplicationDifferent.

Definition sameDischargeLineage
  (left right : GenericDischargeLineage) : Prop :=
  sameApplication (lineageApplication left) (lineageApplication right) /\
  lineageDefinitionRevision left = lineageDefinitionRevision right /\
  lineageEvidenceIdentity left = lineageEvidenceIdentity right.

Record GenericDischargeLineageEqualityFacts : Type :=
  mkGenericDischargeLineageEqualityFacts {
    lineageApplicationMatches : bool;
    lineageDefinitionMatches : bool;
    lineageEvidenceMatches : bool
  }.

Definition sameDischargeLineageFactsb
  (facts : GenericDischargeLineageEqualityFacts) : bool :=
  andb
    (lineageApplicationMatches facts)
    (andb
      (lineageDefinitionMatches facts)
      (lineageEvidenceMatches facts)).

Inductive GenericDischargeLineageEqualityDecision : Type :=
| GenericDischargeLineageEqual
| GenericDischargeLineageDifferent.

Definition decideGenericDischargeLineageEquality
  (facts : GenericDischargeLineageEqualityFacts)
  : GenericDischargeLineageEqualityDecision :=
  if sameDischargeLineageFactsb facts
  then GenericDischargeLineageEqual
  else GenericDischargeLineageDifferent.

Theorem same_application_factsb_true_iff :
  forall
    (left right : GenericApplicationIdentity)
    (declarationMatches interfaceMatches argumentsMatch : bool),
    (declarationMatches = true <->
      applicationDeclarationKey left = applicationDeclarationKey right) ->
    (interfaceMatches = true <->
      applicationInterfaceRevision left = applicationInterfaceRevision right) ->
    (argumentsMatch = true <->
      argumentsEquivalent
        (applicationSemanticArguments left)
        (applicationSemanticArguments right)) ->
    sameApplicationFactsb
      (mkGenericApplicationEqualityFacts
        declarationMatches interfaceMatches argumentsMatch) = true <->
    sameApplication left right.
Proof.
  intros left right declarationMatches interfaceMatches argumentsMatch
    Hdeclaration Hinterface Harguments.
  split.
  - intro Hfacts.
    unfold sameApplicationFactsb in Hfacts.
    apply andb_true_iff in Hfacts.
    destruct Hfacts as [HdeclarationTrue Hrest].
    apply andb_true_iff in Hrest.
    destruct Hrest as [HinterfaceTrue HargumentsTrue].
    unfold sameApplication.
    split.
    + apply (proj1 Hdeclaration).
      exact HdeclarationTrue.
    + split.
      * apply (proj1 Hinterface).
        exact HinterfaceTrue.
      * apply (proj1 Harguments).
        exact HargumentsTrue.
  - intro Hsame.
    unfold sameApplication in Hsame.
    destruct Hsame as [HdeclarationEqual [HinterfaceEqual HargumentsEqual]].
    unfold sameApplicationFactsb.
    apply andb_true_iff.
    split.
    + apply (proj2 Hdeclaration).
      exact HdeclarationEqual.
    + apply andb_true_iff.
      split.
      * apply (proj2 Hinterface).
        exact HinterfaceEqual.
      * apply (proj2 Harguments).
        exact HargumentsEqual.
Qed.

Theorem same_discharge_lineage_factsb_true_iff :
  forall
    (left right : GenericDischargeLineage)
    (applicationMatches definitionMatches evidenceMatches : bool),
    (applicationMatches = true <->
      sameApplication (lineageApplication left) (lineageApplication right)) ->
    (definitionMatches = true <->
      lineageDefinitionRevision left = lineageDefinitionRevision right) ->
    (evidenceMatches = true <->
      lineageEvidenceIdentity left = lineageEvidenceIdentity right) ->
    sameDischargeLineageFactsb
      (mkGenericDischargeLineageEqualityFacts
        applicationMatches definitionMatches evidenceMatches) = true <->
    sameDischargeLineage left right.
Proof.
  intros left right applicationMatches definitionMatches evidenceMatches
    Happlication Hdefinition Hevidence.
  split.
  - intro Hfacts.
    unfold sameDischargeLineageFactsb in Hfacts.
    apply andb_true_iff in Hfacts.
    destruct Hfacts as [HapplicationTrue Hrest].
    apply andb_true_iff in Hrest.
    destruct Hrest as [HdefinitionTrue HevidenceTrue].
    unfold sameDischargeLineage.
    split.
    + apply (proj1 Happlication).
      exact HapplicationTrue.
    + split.
      * apply (proj1 Hdefinition).
        exact HdefinitionTrue.
      * apply (proj1 Hevidence).
        exact HevidenceTrue.
  - intro Hsame.
    unfold sameDischargeLineage in Hsame.
    destruct Hsame as [HapplicationSame [HdefinitionEqual HevidenceEqual]].
    unfold sameDischargeLineageFactsb.
    apply andb_true_iff.
    split.
    + apply (proj2 Happlication).
      exact HapplicationSame.
    + apply andb_true_iff.
      split.
      * apply (proj2 Hdefinition).
        exact HdefinitionEqual.
      * apply (proj2 Hevidence).
        exact HevidenceEqual.
Qed.

Theorem discharge_evidence_difference_rejects_lineage_equality :
  forall applicationMatches definitionMatches,
    sameDischargeLineageFactsb
      (mkGenericDischargeLineageEqualityFacts
        applicationMatches definitionMatches false) = false.
Proof.
  intros applicationMatches definitionMatches.
  destruct applicationMatches; destruct definitionMatches; reflexivity.
Qed.

Theorem definition_difference_rejects_lineage_equality :
  forall applicationMatches evidenceMatches,
    sameDischargeLineageFactsb
      (mkGenericDischargeLineageEqualityFacts
        applicationMatches false evidenceMatches) = false.
Proof.
  intros applicationMatches evidenceMatches.
  destruct applicationMatches; destruct evidenceMatches; reflexivity.
Qed.
