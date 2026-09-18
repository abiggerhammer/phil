From Stdlib Require Import Bool.Bool Arith.PeanoNat.

(*
  PHIL-SURFACE-ELAB-001 — semantic routing and authority preservation for the
  Phase 1 Grammar-v1 source front end.

  This normalized model starts after a Grammar-v1 construct exists. It does not
  claim parser/grammar correspondence. It certifies only the elaboration
  authority boundary:

  - accepted constructs preserve the exact intended semantic category;
  - rejected constructs reach the declared competent semantic layer;
  - competence routing is exact rather than category-collapsing;
  - stable lineage identities are consumed when required, not recomputed from
    source position;
  - elaboration never invents evidence, authority, qualification, assumptions,
    or realization choices; and
  - the semantic attribute namespace is closed.

  Concrete GrammarV1 AST/Text/Map representation, parser correctness, binder
  scope, category-specific checker truth, and Haskell implementation details
  remain explicit predecessor/correspondence boundaries.
*)

Definition SemanticCategory := nat.
Definition CompetenceTarget := nat.
Definition StableIdentity := nat.

Inductive ElaborationOutcome : Type :=
| Elaborated : SemanticCategory -> ElaborationOutcome
| CompetentlyRejected : CompetenceTarget -> ElaborationOutcome.

Record ElaborationIdentityFacts : Type := mkElaborationIdentityFacts {
  identityRequired : bool;
  identityInput : StableIdentity;
  identityOutput : StableIdentity;
  identityRecomputedFromSourcePosition : bool
}.

Definition ElaborationIdentityValid
  (facts : ElaborationIdentityFacts) : Prop :=
  match identityRequired facts with
  | false => identityRecomputedFromSourcePosition facts = false
  | true =>
      identityInput facts <> 0 /\
      identityOutput facts = identityInput facts /\
      identityRecomputedFromSourcePosition facts = false
  end.

Record SurfaceElaborationFacts : Type := mkSurfaceElaborationFacts {
  expectedSemanticCategory : SemanticCategory;
  expectedCompetenceTarget : CompetenceTarget;
  elaborationOutcome : ElaborationOutcome;
  elaborationIdentityFacts : ElaborationIdentityFacts;
  inventedEvidence : bool;
  inventedAuthority : bool;
  inventedQualification : bool;
  inventedAssumption : bool;
  inventedRealizationChoice : bool;
  semanticAttributeNamespaceClosed : bool
}.

Definition ElaborationOutcomeValid
  (facts : SurfaceElaborationFacts) : Prop :=
  match elaborationOutcome facts with
  | Elaborated observedCategory =>
      observedCategory = expectedSemanticCategory facts
  | CompetentlyRejected observedTarget =>
      observedTarget = expectedCompetenceTarget facts
  end.

Definition SurfaceElaborationValid
  (facts : SurfaceElaborationFacts) : Prop :=
  ElaborationOutcomeValid facts /\
  ElaborationIdentityValid (elaborationIdentityFacts facts) /\
  inventedEvidence facts = false /\
  inventedAuthority facts = false /\
  inventedQualification facts = false /\
  inventedAssumption facts = false /\
  inventedRealizationChoice facts = false /\
  semanticAttributeNamespaceClosed facts = true.

Theorem accepted_elaboration_preserves_exact_semantic_category :
  forall facts observed,
    SurfaceElaborationValid facts ->
    elaborationOutcome facts = Elaborated observed ->
    observed = expectedSemanticCategory facts.
Proof.
  intros facts observed Hvalid Houtcome.
  destruct Hvalid as [HoutcomeValid _].
  unfold ElaborationOutcomeValid in HoutcomeValid.
  rewrite Houtcome in HoutcomeValid.
  exact HoutcomeValid.
Qed.

Theorem rejected_elaboration_reaches_exact_competent_target :
  forall facts observed,
    SurfaceElaborationValid facts ->
    elaborationOutcome facts = CompetentlyRejected observed ->
    observed = expectedCompetenceTarget facts.
Proof.
  intros facts observed Hvalid Houtcome.
  destruct Hvalid as [HoutcomeValid _].
  unfold ElaborationOutcomeValid in HoutcomeValid.
  rewrite Houtcome in HoutcomeValid.
  exact HoutcomeValid.
Qed.

Theorem accepted_identity_bearing_elaboration_consumes_exact_input :
  forall facts,
    SurfaceElaborationValid facts ->
    identityRequired (elaborationIdentityFacts facts) = true ->
    identityOutput (elaborationIdentityFacts facts) =
      identityInput (elaborationIdentityFacts facts).
Proof.
  intros facts Hvalid Hrequired.
  destruct Hvalid as [_ [Hidentity _]].
  unfold ElaborationIdentityValid in Hidentity.
  rewrite Hrequired in Hidentity.
  destruct Hidentity as [_ [Hexact _]].
  exact Hexact.
Qed.

Theorem identity_bearing_elaboration_does_not_recompute_from_source_position :
  forall facts,
    SurfaceElaborationValid facts ->
    identityRecomputedFromSourcePosition
      (elaborationIdentityFacts facts) = false.
Proof.
  intros facts Hvalid.
  destruct Hvalid as [_ [Hidentity _]].
  unfold ElaborationIdentityValid in Hidentity.
  destruct (identityRequired (elaborationIdentityFacts facts)) eqn:Hrequired.
  - destruct Hidentity as [_ [_ HnotRecomputed]].
    exact HnotRecomputed.
  - exact Hidentity.
Qed.

Theorem accepted_elaboration_invents_no_evidence :
  forall facts,
    SurfaceElaborationValid facts ->
    inventedEvidence facts = false.
Proof.
  intros facts Hvalid.
  destruct Hvalid as [_ [_ [Hevidence _]]].
  exact Hevidence.
Qed.

Theorem accepted_elaboration_invents_no_authority :
  forall facts,
    SurfaceElaborationValid facts ->
    inventedAuthority facts = false.
Proof.
  intros facts Hvalid.
  destruct Hvalid as [_ [_ [_ [Hauthority _]]]].
  exact Hauthority.
Qed.

Theorem accepted_elaboration_invents_no_qualification :
  forall facts,
    SurfaceElaborationValid facts ->
    inventedQualification facts = false.
Proof.
  intros facts Hvalid.
  destruct Hvalid as [_ [_ [_ [_ [Hqualification _]]]]].
  exact Hqualification.
Qed.

Theorem accepted_elaboration_invents_no_assumption :
  forall facts,
    SurfaceElaborationValid facts ->
    inventedAssumption facts = false.
Proof.
  intros facts Hvalid.
  destruct Hvalid as [_ [_ [_ [_ [_ [Hassumption _]]]]]].
  exact Hassumption.
Qed.

Theorem accepted_elaboration_invents_no_realization_choice :
  forall facts,
    SurfaceElaborationValid facts ->
    inventedRealizationChoice facts = false.
Proof.
  intros facts Hvalid.
  destruct Hvalid as [_ [_ [_ [_ [_ [_ [Hrealization _]]]]]]].
  exact Hrealization.
Qed.

Theorem semantic_attribute_namespace_is_closed :
  forall facts,
    SurfaceElaborationValid facts ->
    semanticAttributeNamespaceClosed facts = true.
Proof.
  intros facts Hvalid.
  destruct Hvalid as [_ [_ [_ [_ [_ [_ [_ Hclosed]]]]]]].
  exact Hclosed.
Qed.

Theorem category_substitution_cannot_be_accepted :
  forall facts observed,
    elaborationOutcome facts = Elaborated observed ->
    observed <> expectedSemanticCategory facts ->
    ~ SurfaceElaborationValid facts.
Proof.
  intros facts observed Houtcome Hneq Hvalid.
  apply Hneq.
  eapply accepted_elaboration_preserves_exact_semantic_category; eauto.
Qed.

Theorem wrong_competence_target_cannot_be_a_valid_rejection :
  forall facts observed,
    elaborationOutcome facts = CompetentlyRejected observed ->
    observed <> expectedCompetenceTarget facts ->
    ~ SurfaceElaborationValid facts.
Proof.
  intros facts observed Houtcome Hneq Hvalid.
  apply Hneq.
  eapply rejected_elaboration_reaches_exact_competent_target; eauto.
Qed.
