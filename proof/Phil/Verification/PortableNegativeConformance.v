From Stdlib Require Import Bool.Bool Arith.PeanoNat.

(*
  PHIL-P1-CONFORMANCE-001 — portable negative conformance closure.

  The normalized theorem starts after a portable fixture manifest and
  environment profile have been decoded.  It owns the meta-level conformance
  contract only:

  - each fixture has one stable identity;
  - its declared rejection class is exact;
  - its declared competent layer is exact;
  - its governing semantic authority resolves exactly;
  - its portable environment materializes successfully;
  - execution rejects rather than succeeds; and
  - the observed rejection class/layer are exactly the declared ones.

  Concrete TSV/Text/path parsing, Haskell environment reconstruction,
  individual checker semantics, proof-artifact existence, and the complete
  81-fixture corpus are implementation/correspondence evidence rather than
  re-proved here.
*)

Definition FixtureIdentity := nat.
Definition RejectionClassIdentity := nat.
Definition CompetentLayerIdentity := nat.
Definition AuthorityIdentity := nat.
Definition EnvironmentIdentity := nat.

Record PortableNegativeFixture : Type := mkPortableNegativeFixture {
  fixtureIdentity : FixtureIdentity;
  fixtureExpectedClass : RejectionClassIdentity;
  fixtureExpectedLayer : CompetentLayerIdentity;
  fixtureAuthority : AuthorityIdentity;
  fixtureEnvironment : EnvironmentIdentity
}.

Record PortableNegativeObservation : Type := mkPortableNegativeObservation {
  observationFixtureIdentity : FixtureIdentity;
  observationRejected : bool;
  observationClass : RejectionClassIdentity;
  observationLayer : CompetentLayerIdentity;
  observationAuthorityResolved : bool;
  observationEnvironmentMaterialized : bool
}.

Definition PortableNegativeConforms
  (fixture : PortableNegativeFixture)
  (observation : PortableNegativeObservation) : Prop :=
  fixtureIdentity fixture <> 0 /\
  fixtureAuthority fixture <> 0 /\
  fixtureEnvironment fixture <> 0 /\
  observationFixtureIdentity observation = fixtureIdentity fixture /\
  observationAuthorityResolved observation = true /\
  observationEnvironmentMaterialized observation = true /\
  observationRejected observation = true /\
  observationClass observation = fixtureExpectedClass fixture /\
  observationLayer observation = fixtureExpectedLayer fixture.

Theorem conforming_fixture_has_stable_identity :
  forall fixture observation,
    PortableNegativeConforms fixture observation ->
    fixtureIdentity fixture <> 0.
Proof.
  intros fixture observation H.
  exact (proj1 H).
Qed.

Theorem conforming_fixture_uses_exact_governing_authority :
  forall fixture observation,
    PortableNegativeConforms fixture observation ->
    fixtureAuthority fixture <> 0 /\
    observationAuthorityResolved observation = true.
Proof.
  intros fixture observation H.
  destruct H as [_ [Hauthority [_ [_ [Hresolved _]]]]].
  split; assumption.
Qed.

Theorem conforming_fixture_requires_materialized_portable_environment :
  forall fixture observation,
    PortableNegativeConforms fixture observation ->
    fixtureEnvironment fixture <> 0 /\
    observationEnvironmentMaterialized observation = true.
Proof.
  intros fixture observation H.
  destruct H as [_ [_ [Henvironment [_ [_ [Hmaterialized _]]]]]].
  split; assumption.
Qed.

Theorem conforming_fixture_rejects :
  forall fixture observation,
    PortableNegativeConforms fixture observation ->
    observationRejected observation = true.
Proof.
  intros fixture observation H.
  destruct H as [_ [_ [_ [_ [_ [_ [Hrejected _]]]]]]].
  exact Hrejected.
Qed.

Theorem conforming_fixture_rejects_at_declared_class :
  forall fixture observation,
    PortableNegativeConforms fixture observation ->
    observationClass observation = fixtureExpectedClass fixture.
Proof.
  intros fixture observation H.
  destruct H as [_ [_ [_ [_ [_ [_ [_ [Hclass _]]]]]]]].
  exact Hclass.
Qed.

Theorem conforming_fixture_rejects_at_declared_competent_layer :
  forall fixture observation,
    PortableNegativeConforms fixture observation ->
    observationLayer observation = fixtureExpectedLayer fixture.
Proof.
  intros fixture observation H.
  destruct H as [_ [_ [_ [_ [_ [_ [_ [_ Hlayer]]]]]]]].
  exact Hlayer.
Qed.

Theorem wrong_rejection_class_cannot_conform :
  forall fixture observation,
    observationClass observation <> fixtureExpectedClass fixture ->
    ~ PortableNegativeConforms fixture observation.
Proof.
  intros fixture observation Hneq Hconforms.
  apply Hneq.
  eapply conforming_fixture_rejects_at_declared_class.
  exact Hconforms.
Qed.

Theorem wrong_competent_layer_cannot_conform :
  forall fixture observation,
    observationLayer observation <> fixtureExpectedLayer fixture ->
    ~ PortableNegativeConforms fixture observation.
Proof.
  intros fixture observation Hneq Hconforms.
  apply Hneq.
  eapply conforming_fixture_rejects_at_declared_competent_layer.
  exact Hconforms.
Qed.

Theorem successful_execution_cannot_satisfy_negative_conformance :
  forall fixture observation,
    observationRejected observation = false ->
    ~ PortableNegativeConforms fixture observation.
Proof.
  intros fixture observation Hsuccess Hconforms.
  pose proof (conforming_fixture_rejects fixture observation Hconforms) as Hreject.
  rewrite Hsuccess in Hreject.
  discriminate.
Qed.

Theorem unresolved_authority_cannot_satisfy_conformance :
  forall fixture observation,
    observationAuthorityResolved observation = false ->
    ~ PortableNegativeConforms fixture observation.
Proof.
  intros fixture observation Hunresolved Hconforms.
  destruct (conforming_fixture_uses_exact_governing_authority
    fixture observation Hconforms) as [_ Hresolved].
  rewrite Hunresolved in Hresolved.
  discriminate.
Qed.

Theorem unmaterialized_environment_cannot_satisfy_conformance :
  forall fixture observation,
    observationEnvironmentMaterialized observation = false ->
    ~ PortableNegativeConforms fixture observation.
Proof.
  intros fixture observation Hmissing Hconforms.
  destruct (conforming_fixture_requires_materialized_portable_environment
    fixture observation Hconforms) as [_ Hmaterialized].
  rewrite Hmissing in Hmaterialized.
  discriminate.
Qed.

Definition FixtureFamily := nat.

Record PortableConformanceCorpus : Type := mkPortableConformanceCorpus {
  corpusFixtureCount : nat;
  corpusFamilyCount : nat;
  corpusManifestUnique : bool;
  corpusAuthorityRegistryExact : bool;
  corpusEnvironmentRegistryExact : bool;
  corpusAllFixturesConform : bool
}.

Definition PortableConformanceCorpusClosed
  (corpus : PortableConformanceCorpus) : Prop :=
  corpusFixtureCount corpus = 81 /\
  corpusFamilyCount corpus = 9 /\
  corpusManifestUnique corpus = true /\
  corpusAuthorityRegistryExact corpus = true /\
  corpusEnvironmentRegistryExact corpus = true /\
  corpusAllFixturesConform corpus = true.

Theorem closed_phase1_negative_corpus_has_81_fixtures :
  forall corpus,
    PortableConformanceCorpusClosed corpus ->
    corpusFixtureCount corpus = 81.
Proof.
  intros corpus H.
  exact (proj1 H).
Qed.

Theorem closed_phase1_negative_corpus_has_nine_replay_families :
  forall corpus,
    PortableConformanceCorpusClosed corpus ->
    corpusFamilyCount corpus = 9.
Proof.
  intros corpus H.
  exact (proj1 (proj2 H)).
Qed.

Theorem closed_phase1_negative_corpus_requires_exact_registries :
  forall corpus,
    PortableConformanceCorpusClosed corpus ->
    corpusManifestUnique corpus = true /\
    corpusAuthorityRegistryExact corpus = true /\
    corpusEnvironmentRegistryExact corpus = true.
Proof.
  intros corpus H.
  destruct H as [_ [_ [Hmanifest [Hauthority [Henvironment _]]]]].
  repeat split; assumption.
Qed.

Theorem closed_phase1_negative_corpus_requires_every_fixture_to_conform :
  forall corpus,
    PortableConformanceCorpusClosed corpus ->
    corpusAllFixturesConform corpus = true.
Proof.
  intros corpus H.
  destruct H as [_ [_ [_ [_ [_ Hall]]]]].
  exact Hall.
Qed.
