From Phil.Core Require Import SystemsSubjectAuthority.

Definition subjectBasisAdmittedBool (basis : SubjectCorrespondenceBasis) : bool :=
  match basis with
  | CheckedSubjectRelation => true
  | RuntimeRepresentationCoincidence => false
  end.

Inductive SubjectStageDecision : Type :=
| SubjectStageAcceptedDecision
| SubjectStageBasisDecision
| SubjectStageSystemsSetDecision
| SubjectStageSystemsValuesDecision
| SubjectStageExclusivityDecision
| SubjectStageValidityScopeDecision.

Definition decideSubjectStageByFacts
  (basis : SubjectCorrespondenceBasis)
  (systemsSetNonempty systemsValuesExist systemsValueExclusive validityScopeExact : bool)
  : SubjectStageDecision :=
  if subjectBasisAdmittedBool basis then
    if systemsSetNonempty then
      if systemsValuesExist then
        if systemsValueExclusive then
          if validityScopeExact
          then SubjectStageAcceptedDecision
          else SubjectStageValidityScopeDecision
        else SubjectStageExclusivityDecision
      else SubjectStageSystemsValuesDecision
    else SubjectStageSystemsSetDecision
  else SubjectStageBasisDecision.

Definition reflectedSubjectStageFacts
  (basis : SubjectCorrespondenceBasis)
  (systemsSetNonempty systemsValuesExist systemsValueExclusive validityScopeExact : bool)
  : SubjectStageFacts :=
  {| subject_basis := basis;
     subject_systems_set_nonempty := systemsSetNonempty = true;
     subject_systems_values_exist := systemsValuesExist = true;
     subject_systems_value_exclusive := systemsValueExclusive = true;
     subject_validity_scope_exact := validityScopeExact = true |}.

Theorem reflected_subject_stage_decision_exact :
  forall basis systemsSetNonempty systemsValuesExist systemsValueExclusive validityScopeExact,
    decideSubjectStageByFacts
      basis systemsSetNonempty systemsValuesExist systemsValueExclusive validityScopeExact =
      SubjectStageAcceptedDecision <->
    subject_stage_ok
      (reflectedSubjectStageFacts
        basis systemsSetNonempty systemsValuesExist systemsValueExclusive validityScopeExact).
Proof.
  intros basis systemsSetNonempty systemsValuesExist systemsValueExclusive validityScopeExact.
  unfold decideSubjectStageByFacts, subjectBasisAdmittedBool,
    subject_stage_ok, reflectedSubjectStageFacts, subject_basis_admitted.
  destruct basis;
  destruct systemsSetNonempty;
  destruct systemsValuesExist;
  destruct systemsValueExclusive;
  destruct validityScopeExact;
  simpl; intuition discriminate.
Qed.

Definition providerBindingAdmittedBool (basis : ProviderCallBindingBasis) : bool :=
  match basis with
  | ExactProviderCallBinding => true
  | RuntimeSymbolOnlyProviderCall => false
  end.

Inductive ProviderCallStageDecision : Type :=
| ProviderCallStageAcceptedDecision
| ProviderCallSubjectStageDecision
| ProviderCallBindingDecision
| ProviderCallAdmissionDecision
| ProviderCallInterfaceDecision
| ProviderCallOperationDecision
| ProviderCallImplementationEntryDecision
| ProviderCallSiteDomainDecision.

Definition decideProviderCallStageByFacts
  (subjectStageAccepted : bool)
  (basis : ProviderCallBindingBasis)
  (selectedAdmissionExact interfaceExact operationExact implementationEntryExact callSiteDomainExact : bool)
  : ProviderCallStageDecision :=
  if subjectStageAccepted then
    if providerBindingAdmittedBool basis then
      if selectedAdmissionExact then
        if interfaceExact then
          if operationExact then
            if implementationEntryExact then
              if callSiteDomainExact
              then ProviderCallStageAcceptedDecision
              else ProviderCallSiteDomainDecision
            else ProviderCallImplementationEntryDecision
          else ProviderCallOperationDecision
        else ProviderCallInterfaceDecision
      else ProviderCallAdmissionDecision
    else ProviderCallBindingDecision
  else ProviderCallSubjectStageDecision.

Definition reflectedProviderCallStageFacts
  (subjectFacts : SubjectStageFacts)
  (basis : ProviderCallBindingBasis)
  (selectedAdmissionExact interfaceExact operationExact implementationEntryExact callSiteDomainExact : bool)
  : ProviderCallStageFacts :=
  {| provider_subject_stage := subjectFacts;
     provider_binding_basis := basis;
     provider_selected_admission_exact := selectedAdmissionExact = true;
     provider_interface_exact := interfaceExact = true;
     provider_operation_exact := operationExact = true;
     provider_implementation_entry_exact := implementationEntryExact = true;
     provider_call_site_domain_exact := callSiteDomainExact = true |}.

Theorem reflected_provider_call_stage_decision_exact :
  forall subjectFacts subjectStageAccepted basis
         selectedAdmissionExact interfaceExact operationExact implementationEntryExact callSiteDomainExact,
    (subjectStageAccepted = true <-> subject_stage_ok subjectFacts) ->
    decideProviderCallStageByFacts
      subjectStageAccepted basis selectedAdmissionExact interfaceExact operationExact
      implementationEntryExact callSiteDomainExact = ProviderCallStageAcceptedDecision <->
    provider_call_stage_ok
      (reflectedProviderCallStageFacts
        subjectFacts basis selectedAdmissionExact interfaceExact operationExact
        implementationEntryExact callSiteDomainExact).
Proof.
  intros subjectFacts subjectStageAccepted basis
    selectedAdmissionExact interfaceExact operationExact implementationEntryExact callSiteDomainExact
    Hsubject.
  unfold decideProviderCallStageByFacts, providerBindingAdmittedBool,
    provider_call_stage_ok, reflectedProviderCallStageFacts, provider_binding_admitted.
  destruct subjectStageAccepted;
  destruct basis;
  destruct selectedAdmissionExact;
  destruct interfaceExact;
  destruct operationExact;
  destruct implementationEntryExact;
  destruct callSiteDomainExact;
  simpl in *; intuition discriminate.
Qed.

Inductive EffectUseDecision : Type :=
| EffectUseAcceptedDecision
| EffectUseObservableWideningDecision
| EffectUseMissingRefinementDecision.

Definition decideEffectUseByFacts
  (alreadyInSourceBound hasRealizationRefinement : bool)
  (visibility : EffectVisibility) : EffectUseDecision :=
  if alreadyInSourceBound then EffectUseAcceptedDecision else
  match visibility with
  | SourceObservableEffect => EffectUseObservableWideningDecision
  | InternalRealizationEffect =>
      if hasRealizationRefinement
      then EffectUseAcceptedDecision
      else EffectUseMissingRefinementDecision
  end.

Theorem effect_use_decision_accepted_iff :
  forall alreadyInSourceBound hasRealizationRefinement visibility,
    decideEffectUseByFacts alreadyInSourceBound hasRealizationRefinement visibility =
      EffectUseAcceptedDecision <->
    effect_use_admitted
      (alreadyInSourceBound = true)
      (hasRealizationRefinement = true)
      visibility.
Proof.
  intros alreadyInSourceBound hasRealizationRefinement visibility.
  unfold decideEffectUseByFacts, effect_use_admitted.
  destruct alreadyInSourceBound;
  destruct hasRealizationRefinement;
  destruct visibility;
  simpl; intuition discriminate.
Qed.

Inductive AuthorityExerciseDecision : Type :=
| AuthorityExerciseAcceptedDecision
| AuthorityExerciseHiddenPublicDecision
| AuthorityExerciseHiddenInternalDecision
| AuthorityExerciseDispositionDecision.

Definition decideAuthorityExerciseByFacts
  (declaredPublic qualifiedInternal dispositionMatches : bool)
  (visibility : AuthorityVisibility) : AuthorityExerciseDecision :=
  match visibility with
  | PublicAuthority =>
      if declaredPublic
      then AuthorityExerciseAcceptedDecision
      else AuthorityExerciseHiddenPublicDecision
  | QualifiedInternalAuthority =>
      if qualifiedInternal then
        if dispositionMatches
        then AuthorityExerciseAcceptedDecision
        else AuthorityExerciseDispositionDecision
      else AuthorityExerciseHiddenInternalDecision
  end.

Theorem authority_exercise_decision_accepted_iff :
  forall declaredPublic qualifiedInternal dispositionMatches visibility,
    decideAuthorityExerciseByFacts
      declaredPublic qualifiedInternal dispositionMatches visibility =
      AuthorityExerciseAcceptedDecision <->
    authority_exercise_admitted
      (declaredPublic = true)
      (qualifiedInternal = true)
      (dispositionMatches = true)
      visibility.
Proof.
  intros declaredPublic qualifiedInternal dispositionMatches visibility.
  unfold decideAuthorityExerciseByFacts, authority_exercise_admitted.
  destruct declaredPublic;
  destruct qualifiedInternal;
  destruct dispositionMatches;
  destruct visibility;
  simpl; intuition discriminate.
Qed.

Inductive AuthorityEffectStageDecision : Type :=
| AuthorityEffectStageAcceptedDecision
| AuthorityEffectProviderStageDecision
| AuthorityEffectSurfaceDomainDecision
| AuthorityEffectUseDomainDecision
| AuthorityEffectPublicEscapeDecision
| AuthorityEffectPublicCompletenessDecision
| AuthorityEffectInternalAssignmentsDecision
| AuthorityEffectUsesDecision
| AuthorityEffectExercisesDecision.

Definition decideAuthorityEffectStageByFacts
  (providerStageAccepted surfaceDomainExact useDomainExact publicSurfaceNoEscape
   publicSurfaceComplete internalAssignmentsQualified allEffectUsesAdmitted
   allAuthorityExercisesAdmitted : bool) : AuthorityEffectStageDecision :=
  if providerStageAccepted then
    if surfaceDomainExact then
      if useDomainExact then
        if publicSurfaceNoEscape then
          if publicSurfaceComplete then
            if internalAssignmentsQualified then
              if allEffectUsesAdmitted then
                if allAuthorityExercisesAdmitted
                then AuthorityEffectStageAcceptedDecision
                else AuthorityEffectExercisesDecision
              else AuthorityEffectUsesDecision
            else AuthorityEffectInternalAssignmentsDecision
          else AuthorityEffectPublicCompletenessDecision
        else AuthorityEffectPublicEscapeDecision
      else AuthorityEffectUseDomainDecision
    else AuthorityEffectSurfaceDomainDecision
  else AuthorityEffectProviderStageDecision.

Definition reflectedAuthorityEffectStageFacts
  (providerFacts : ProviderCallStageFacts)
  (surfaceDomainExact useDomainExact publicSurfaceNoEscape publicSurfaceComplete
   internalAssignmentsQualified allEffectUsesAdmitted allAuthorityExercisesAdmitted : bool)
  : AuthorityEffectStageFacts :=
  {| authority_provider_stage := providerFacts;
     authority_surface_domain_exact := surfaceDomainExact = true;
     authority_use_domain_exact := useDomainExact = true;
     authority_public_surface_no_escape := publicSurfaceNoEscape = true;
     authority_public_surface_complete := publicSurfaceComplete = true;
     authority_internal_assignments_qualified := internalAssignmentsQualified = true;
     authority_all_effect_uses_admitted := allEffectUsesAdmitted = true;
     authority_all_authority_exercises_admitted := allAuthorityExercisesAdmitted = true |}.

Theorem reflected_authority_effect_stage_decision_exact :
  forall providerFacts providerStageAccepted surfaceDomainExact useDomainExact
         publicSurfaceNoEscape publicSurfaceComplete internalAssignmentsQualified
         allEffectUsesAdmitted allAuthorityExercisesAdmitted,
    (providerStageAccepted = true <-> provider_call_stage_ok providerFacts) ->
    decideAuthorityEffectStageByFacts
      providerStageAccepted surfaceDomainExact useDomainExact publicSurfaceNoEscape
      publicSurfaceComplete internalAssignmentsQualified allEffectUsesAdmitted
      allAuthorityExercisesAdmitted = AuthorityEffectStageAcceptedDecision <->
    authority_effect_stage_ok
      (reflectedAuthorityEffectStageFacts
        providerFacts surfaceDomainExact useDomainExact publicSurfaceNoEscape
        publicSurfaceComplete internalAssignmentsQualified allEffectUsesAdmitted
        allAuthorityExercisesAdmitted).
Proof.
  intros providerFacts providerStageAccepted surfaceDomainExact useDomainExact
    publicSurfaceNoEscape publicSurfaceComplete internalAssignmentsQualified
    allEffectUsesAdmitted allAuthorityExercisesAdmitted Hprovider.
  unfold decideAuthorityEffectStageByFacts, authority_effect_stage_ok,
    reflectedAuthorityEffectStageFacts.
  destruct providerStageAccepted;
  destruct surfaceDomainExact;
  destruct useDomainExact;
  destruct publicSurfaceNoEscape;
  destruct publicSurfaceComplete;
  destruct internalAssignmentsQualified;
  destruct allEffectUsesAdmitted;
  destruct allAuthorityExercisesAdmitted;
  simpl in *; intuition discriminate.
Qed.
