(*
  PHIL-SYS-SUBJECT-AUTH-001

  Normalized semantic model for the cumulative SYS-004--006
  Systems/StageContract subject, provider-call, authority, and effect
  preservation chain.

  This model intentionally begins after concrete Haskell Map/Set/list and
  identifier normalization.  Those representation bridges remain explicit
  correspondence assumptions rather than being silently folded into the
  theorem.
*)

Inductive SubjectCorrespondenceBasis : Type :=
| CheckedSubjectRelation
| RuntimeRepresentationCoincidence.

Definition subject_basis_admitted (basis : SubjectCorrespondenceBasis) : Prop :=
  match basis with
  | CheckedSubjectRelation => True
  | RuntimeRepresentationCoincidence => False
  end.

Record SubjectStageFacts : Type := {
  subject_basis : SubjectCorrespondenceBasis;
  subject_systems_set_nonempty : Prop;
  subject_systems_values_exist : Prop;
  subject_systems_value_exclusive : Prop;
  subject_validity_scope_exact : Prop
}.

Definition subject_stage_ok (facts : SubjectStageFacts) : Prop :=
  subject_basis_admitted (subject_basis facts) /\
  subject_systems_set_nonempty facts /\
  subject_systems_values_exist facts /\
  subject_systems_value_exclusive facts /\
  subject_validity_scope_exact facts.

Theorem runtime_representation_coincidence_rejected :
  ~ subject_basis_admitted RuntimeRepresentationCoincidence.
Proof.
  simpl.
  intros H.
  exact H.
Qed.

Theorem checked_subject_relation_admitted :
  subject_basis_admitted CheckedSubjectRelation.
Proof.
  simpl.
  exact I.
Qed.

Theorem accepted_subject_stage_has_exclusive_systems_values :
  forall facts,
    subject_stage_ok facts ->
    subject_systems_value_exclusive facts.
Proof.
  intros facts H.
  destruct H as [_ [_ [_ [Hexclusive _]]]].
  exact Hexclusive.
Qed.

Inductive ProviderCallBindingBasis : Type :=
| ExactProviderCallBinding
| RuntimeSymbolOnlyProviderCall.

Definition provider_binding_admitted (basis : ProviderCallBindingBasis) : Prop :=
  match basis with
  | ExactProviderCallBinding => True
  | RuntimeSymbolOnlyProviderCall => False
  end.

Record ProviderCallStageFacts : Type := {
  provider_subject_stage : SubjectStageFacts;
  provider_binding_basis : ProviderCallBindingBasis;
  provider_selected_admission_exact : Prop;
  provider_interface_exact : Prop;
  provider_operation_exact : Prop;
  provider_implementation_entry_exact : Prop;
  provider_call_site_domain_exact : Prop
}.

Definition provider_call_stage_ok (facts : ProviderCallStageFacts) : Prop :=
  subject_stage_ok (provider_subject_stage facts) /\
  provider_binding_admitted (provider_binding_basis facts) /\
  provider_selected_admission_exact facts /\
  provider_interface_exact facts /\
  provider_operation_exact facts /\
  provider_implementation_entry_exact facts /\
  provider_call_site_domain_exact facts.

Theorem runtime_symbol_only_provider_call_rejected :
  ~ provider_binding_admitted RuntimeSymbolOnlyProviderCall.
Proof.
  simpl.
  intros H.
  exact H.
Qed.

Theorem accepted_provider_call_preserves_subject_stage :
  forall facts,
    provider_call_stage_ok facts ->
    subject_stage_ok (provider_subject_stage facts).
Proof.
  intros facts H.
  destruct H as [Hsubject _].
  exact Hsubject.
Qed.

Theorem accepted_provider_call_has_exact_operation_and_entry :
  forall facts,
    provider_call_stage_ok facts ->
    provider_operation_exact facts /\
    provider_implementation_entry_exact facts.
Proof.
  intros facts H.
  destruct H as [_ [_ [_ [_ [Hoperation [Hentry _]]]]]].
  split.
  - exact Hoperation.
  - exact Hentry.
Qed.

Inductive EffectVisibility : Type :=
| SourceObservableEffect
| InternalRealizationEffect.

Definition effect_use_admitted
  (already_in_source_bound has_realization_refinement : Prop)
  (visibility : EffectVisibility) : Prop :=
  already_in_source_bound \/
  match visibility with
  | SourceObservableEffect => False
  | InternalRealizationEffect => has_realization_refinement
  end.

Theorem source_observable_effect_widening_rejected :
  ~ effect_use_admitted False False SourceObservableEffect.
Proof.
  intros H.
  destruct H as [H | H].
  - exact H.
  - exact H.
Qed.

Theorem internal_effect_requires_refinement_when_not_in_source_bound :
  forall refinement,
    effect_use_admitted False refinement InternalRealizationEffect ->
    refinement.
Proof.
  intros refinement H.
  destruct H as [Hfalse | Hrefinement].
  - exact Hfalse.
  - exact Hrefinement.
Qed.

Inductive AuthorityVisibility : Type :=
| PublicAuthority
| QualifiedInternalAuthority.

Definition authority_exercise_admitted
  (declared_public qualified_internal disposition_matches : Prop)
  (visibility : AuthorityVisibility) : Prop :=
  match visibility with
  | PublicAuthority => declared_public
  | QualifiedInternalAuthority => qualified_internal /\ disposition_matches
  end.

Theorem undeclared_public_authority_rejected :
  ~ authority_exercise_admitted False False False PublicAuthority.
Proof.
  simpl.
  intros H.
  exact H.
Qed.

Theorem internal_authority_requires_qualification_and_disposition :
  forall qualified disposition,
    authority_exercise_admitted False qualified disposition QualifiedInternalAuthority ->
    qualified /\ disposition.
Proof.
  intros qualified disposition H.
  exact H.
Qed.

Record AuthorityEffectStageFacts : Type := {
  authority_provider_stage : ProviderCallStageFacts;
  authority_surface_domain_exact : Prop;
  authority_use_domain_exact : Prop;
  authority_public_surface_no_escape : Prop;
  authority_public_surface_complete : Prop;
  authority_internal_assignments_qualified : Prop;
  authority_all_effect_uses_admitted : Prop;
  authority_all_authority_exercises_admitted : Prop
}.

Definition authority_effect_stage_ok (facts : AuthorityEffectStageFacts) : Prop :=
  provider_call_stage_ok (authority_provider_stage facts) /\
  authority_surface_domain_exact facts /\
  authority_use_domain_exact facts /\
  authority_public_surface_no_escape facts /\
  authority_public_surface_complete facts /\
  authority_internal_assignments_qualified facts /\
  authority_all_effect_uses_admitted facts /\
  authority_all_authority_exercises_admitted facts.

Theorem accepted_authority_effect_stage_preserves_provider_chain :
  forall facts,
    authority_effect_stage_ok facts ->
    provider_call_stage_ok (authority_provider_stage facts).
Proof.
  intros facts H.
  destruct H as [Hprovider _].
  exact Hprovider.
Qed.

Theorem accepted_authority_effect_stage_preserves_nonwidening :
  forall facts,
    authority_effect_stage_ok facts ->
    authority_public_surface_no_escape facts /\
    authority_public_surface_complete facts /\
    authority_internal_assignments_qualified facts /\
    authority_all_effect_uses_admitted facts /\
    authority_all_authority_exercises_admitted facts.
Proof.
  intros facts H.
  destruct H as [_ [_ [_ [Hescape [Hcomplete [Hinternal [Heffects Hauthority]]]]]]].
  repeat split; assumption.
Qed.

Theorem successful_systems_subject_authority_chain_preserves_subject_identity :
  forall facts,
    authority_effect_stage_ok facts ->
    subject_stage_ok
      (provider_subject_stage (authority_provider_stage facts)).
Proof.
  intros facts H.
  apply accepted_provider_call_preserves_subject_stage.
  apply accepted_authority_effect_stage_preserves_provider_chain.
  exact H.
Qed.

Theorem successful_systems_subject_authority_chain_uses_checked_subject_relation :
  forall facts,
    authority_effect_stage_ok facts ->
    subject_basis
      (provider_subject_stage (authority_provider_stage facts)) <>
      RuntimeRepresentationCoincidence.
Proof.
  intros facts Hstage Heq.
  pose proof
    (successful_systems_subject_authority_chain_preserves_subject_identity
      facts Hstage) as Hsubject.
  destruct Hsubject as [Hbasis _].
  rewrite Heq in Hbasis.
  simpl in Hbasis.
  exact Hbasis.
Qed.

Theorem successful_systems_subject_authority_chain_uses_exact_provider_binding :
  forall facts,
    authority_effect_stage_ok facts ->
    provider_binding_basis (authority_provider_stage facts) <>
      RuntimeSymbolOnlyProviderCall.
Proof.
  intros facts Hstage Heq.
  pose proof
    (accepted_authority_effect_stage_preserves_provider_chain facts Hstage)
    as Hprovider.
  destruct Hprovider as [_ [Hbinding _]].
  rewrite Heq in Hbinding.
  simpl in Hbinding.
  exact Hbinding.
Qed.
