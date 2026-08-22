(*
  PHIL-SYS-SSA-001 — proof-oriented model of Phil.Systems.verifyScalarDataflow.

  The concrete verifier enumerates typed scalar values, operation/terminator uses,
  and definition sites from Data.Map-backed Systems IR.  It then requires:

  - exactly one definition for every TypedScalar value;
  - every use of a TypedScalar value to occur strictly after that definition,
    either earlier in the same block or in a CFG block dominated by the
    definition block.

  This normalized model removes container enumeration and graph-search
  mechanics.  [scalarPrecedes] is the post-computation relation corresponding
  to same-block index order or concrete CFG dominance.  Correspondence from
  Haskell block reachability, operation indexing, and ValueId/Text identities
  remains an implementation boundary.
*)

Definition ValueId := nat.
Definition SiteId := nat.

Record ScalarDataflowModel : Type := mkScalarDataflowModel {
  scalarTyped : ValueId -> Prop;
  scalarDefinitionAt : ValueId -> SiteId -> Prop;
  scalarUseAt : ValueId -> SiteId -> Prop;
  scalarPrecedes : SiteId -> SiteId -> Prop
}.

Definition ExactlyOneScalarDefinition
  (model : ScalarDataflowModel)
  (value : ValueId) : Prop :=
  exists definitionSite,
    scalarDefinitionAt model value definitionSite /\
    forall otherSite,
      scalarDefinitionAt model value otherSite ->
      otherSite = definitionSite.

Definition ScalarDataflowVerificationSuccess
  (model : ScalarDataflowModel) : Prop :=
  (forall value,
    scalarTyped model value ->
    ExactlyOneScalarDefinition model value) /\
  (forall value useSite,
    scalarTyped model value ->
    scalarUseAt model value useSite ->
    exists definitionSite,
      scalarDefinitionAt model value definitionSite /\
      scalarPrecedes model definitionSite useSite).

Theorem verified_typed_scalar_has_exactly_one_definition :
  forall model value,
    ScalarDataflowVerificationSuccess model ->
    scalarTyped model value ->
    ExactlyOneScalarDefinition model value.
Proof.
  intros model value Hverified Htyped.
  destruct Hverified as [Hdefinitions _].
  apply Hdefinitions.
  exact Htyped.
Qed.

Theorem verified_scalar_use_has_unique_preceding_definition :
  forall model value useSite,
    ScalarDataflowVerificationSuccess model ->
    scalarTyped model value ->
    scalarUseAt model value useSite ->
    exists definitionSite,
      scalarDefinitionAt model value definitionSite /\
      scalarPrecedes model definitionSite useSite /\
      forall otherSite,
        scalarDefinitionAt model value otherSite ->
        otherSite = definitionSite.
Proof.
  intros model value useSite Hverified Htyped Huse.
  destruct Hverified as [Hdefinitions Huses].
  destruct (Hdefinitions value Htyped)
    as [uniqueSite [HuniqueDefinition HonlyDefinition]].
  destruct (Huses value useSite Htyped Huse)
    as [definitionSite [Hdefinition Hprecedes]].
  exists definitionSite.
  split.
  - exact Hdefinition.
  - split.
    + exact Hprecedes.
    + intros otherSite HotherDefinition.
      pose proof (HonlyDefinition definitionSite Hdefinition) as HdefinitionEq.
      pose proof (HonlyDefinition otherSite HotherDefinition) as HotherEq.
      rewrite HdefinitionEq.
      exact HotherEq.
Qed.

Theorem missing_scalar_definition_is_rejected :
  forall model value,
    scalarTyped model value ->
    (forall site, ~ scalarDefinitionAt model value site) ->
    ~ ScalarDataflowVerificationSuccess model.
Proof.
  intros model value Htyped Hmissing Hverified.
  pose proof
    (verified_typed_scalar_has_exactly_one_definition
      model value Hverified Htyped) as Hexact.
  destruct Hexact as [site [Hdefinition _]].
  exact (Hmissing site Hdefinition).
Qed.

Theorem multiple_scalar_definitions_are_rejected :
  forall model value leftSite rightSite,
    scalarTyped model value ->
    scalarDefinitionAt model value leftSite ->
    scalarDefinitionAt model value rightSite ->
    leftSite <> rightSite ->
    ~ ScalarDataflowVerificationSuccess model.
Proof.
  intros model value leftSite rightSite Htyped Hleft Hright Hdistinct Hverified.
  pose proof
    (verified_typed_scalar_has_exactly_one_definition
      model value Hverified Htyped) as Hexact.
  destruct Hexact as [uniqueSite [_ Honly]].
  apply Hdistinct.
  transitivity uniqueSite.
  - apply Honly.
    exact Hleft.
  - symmetry.
    apply Honly.
    exact Hright.
Qed.

Theorem non_dominating_scalar_definition_is_rejected :
  forall model value useSite,
    scalarTyped model value ->
    scalarUseAt model value useSite ->
    (forall definitionSite,
      scalarDefinitionAt model value definitionSite ->
      ~ scalarPrecedes model definitionSite useSite) ->
    ~ ScalarDataflowVerificationSuccess model.
Proof.
  intros model value useSite Htyped Huse HnotPreceding Hverified.
  pose proof
    (verified_scalar_use_has_unique_preceding_definition
      model value useSite Hverified Htyped Huse) as Hdefinition.
  destruct Hdefinition as
    [definitionSite [Hdefined [Hprecedes _]]].
  exact (HnotPreceding definitionSite Hdefined Hprecedes).
Qed.

Theorem scalar_use_before_same_site_definition_is_rejected :
  forall model value useSite definitionSite,
    scalarTyped model value ->
    scalarUseAt model value useSite ->
    scalarDefinitionAt model value definitionSite ->
    (forall site,
      scalarDefinitionAt model value site ->
      site = definitionSite) ->
    ~ scalarPrecedes model definitionSite useSite ->
    ~ ScalarDataflowVerificationSuccess model.
Proof.
  intros model value useSite definitionSite Htyped Huse Hdefinition Honly
    HnotPrecedes Hverified.
  pose proof
    (verified_scalar_use_has_unique_preceding_definition
      model value useSite Hverified Htyped Huse) as HverifiedUse.
  destruct HverifiedUse as [actualSite [Hactual [Hprecedes _]]].
  pose proof (Honly actualSite Hactual) as Heq.
  subst actualSite.
  contradiction.
Qed.
