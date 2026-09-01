module Main (main) where

import SystemsSubjectAuthorityKernel

assert :: String -> Bool -> IO ()
assert label ok =
  if ok then putStrLn ("PASS: " ++ label)
  else error ("systems subject authority correspondence failed: " ++ label)

isSubject :: SubjectStageDecision -> SubjectStageDecision -> Bool
isSubject expected actual = case (expected, actual) of
  (SubjectStageAcceptedDecision, SubjectStageAcceptedDecision) -> True
  (SubjectStageBasisDecision, SubjectStageBasisDecision) -> True
  (SubjectStageSystemsSetDecision, SubjectStageSystemsSetDecision) -> True
  (SubjectStageSystemsValuesDecision, SubjectStageSystemsValuesDecision) -> True
  (SubjectStageExclusivityDecision, SubjectStageExclusivityDecision) -> True
  (SubjectStageValidityScopeDecision, SubjectStageValidityScopeDecision) -> True
  _ -> False

isProvider :: ProviderCallStageDecision -> ProviderCallStageDecision -> Bool
isProvider expected actual = case (expected, actual) of
  (ProviderCallStageAcceptedDecision, ProviderCallStageAcceptedDecision) -> True
  (ProviderCallSubjectStageDecision, ProviderCallSubjectStageDecision) -> True
  (ProviderCallBindingDecision, ProviderCallBindingDecision) -> True
  (ProviderCallAdmissionDecision, ProviderCallAdmissionDecision) -> True
  (ProviderCallInterfaceDecision, ProviderCallInterfaceDecision) -> True
  (ProviderCallOperationDecision, ProviderCallOperationDecision) -> True
  (ProviderCallImplementationEntryDecision, ProviderCallImplementationEntryDecision) -> True
  (ProviderCallSiteDomainDecision, ProviderCallSiteDomainDecision) -> True
  _ -> False

isEffect :: EffectUseDecision -> EffectUseDecision -> Bool
isEffect expected actual = case (expected, actual) of
  (EffectUseAcceptedDecision, EffectUseAcceptedDecision) -> True
  (EffectUseObservableWideningDecision, EffectUseObservableWideningDecision) -> True
  (EffectUseMissingRefinementDecision, EffectUseMissingRefinementDecision) -> True
  _ -> False

isAuthority :: AuthorityExerciseDecision -> AuthorityExerciseDecision -> Bool
isAuthority expected actual = case (expected, actual) of
  (AuthorityExerciseAcceptedDecision, AuthorityExerciseAcceptedDecision) -> True
  (AuthorityExerciseHiddenPublicDecision, AuthorityExerciseHiddenPublicDecision) -> True
  (AuthorityExerciseHiddenInternalDecision, AuthorityExerciseHiddenInternalDecision) -> True
  (AuthorityExerciseDispositionDecision, AuthorityExerciseDispositionDecision) -> True
  _ -> False

isAuthorityStage :: AuthorityEffectStageDecision -> AuthorityEffectStageDecision -> Bool
isAuthorityStage expected actual = case (expected, actual) of
  (AuthorityEffectStageAcceptedDecision, AuthorityEffectStageAcceptedDecision) -> True
  (AuthorityEffectProviderStageDecision, AuthorityEffectProviderStageDecision) -> True
  (AuthorityEffectSurfaceDomainDecision, AuthorityEffectSurfaceDomainDecision) -> True
  (AuthorityEffectUseDomainDecision, AuthorityEffectUseDomainDecision) -> True
  (AuthorityEffectPublicEscapeDecision, AuthorityEffectPublicEscapeDecision) -> True
  (AuthorityEffectPublicCompletenessDecision, AuthorityEffectPublicCompletenessDecision) -> True
  (AuthorityEffectInternalAssignmentsDecision, AuthorityEffectInternalAssignmentsDecision) -> True
  (AuthorityEffectUsesDecision, AuthorityEffectUsesDecision) -> True
  (AuthorityEffectExercisesDecision, AuthorityEffectExercisesDecision) -> True
  _ -> False

main :: IO ()
main = do
  assert "SYS-004 checked subject stage accepts" $
    isSubject SubjectStageAcceptedDecision
      (decideSubjectStageByFacts CheckedSubjectRelation True True True True)
  assert "SYS-004 runtime representation coincidence rejects" $
    isSubject SubjectStageBasisDecision
      (decideSubjectStageByFacts RuntimeRepresentationCoincidence True True True True)
  assert "SYS-004 nonempty Systems set required" $
    isSubject SubjectStageSystemsSetDecision
      (decideSubjectStageByFacts CheckedSubjectRelation False True True True)
  assert "SYS-004 referenced Systems values must exist" $
    isSubject SubjectStageSystemsValuesDecision
      (decideSubjectStageByFacts CheckedSubjectRelation True False True True)
  assert "SYS-004 Systems values are exclusive to one subject" $
    isSubject SubjectStageExclusivityDecision
      (decideSubjectStageByFacts CheckedSubjectRelation True True False True)
  assert "SYS-004 validity scope is exact" $
    isSubject SubjectStageValidityScopeDecision
      (decideSubjectStageByFacts CheckedSubjectRelation True True True False)

  assert "SYS-005 exact provider call stage accepts" $
    isProvider ProviderCallStageAcceptedDecision
      (decideProviderCallStageByFacts True ExactProviderCallBinding True True True True True)
  assert "SYS-005 predecessor subject stage is required" $
    isProvider ProviderCallSubjectStageDecision
      (decideProviderCallStageByFacts False ExactProviderCallBinding True True True True True)
  assert "SYS-005 runtime-symbol-only binding rejects" $
    isProvider ProviderCallBindingDecision
      (decideProviderCallStageByFacts True RuntimeSymbolOnlyProviderCall True True True True True)
  assert "SYS-005 selected admission must match" $
    isProvider ProviderCallAdmissionDecision
      (decideProviderCallStageByFacts True ExactProviderCallBinding False True True True True)
  assert "SYS-005 interface must match" $
    isProvider ProviderCallInterfaceDecision
      (decideProviderCallStageByFacts True ExactProviderCallBinding True False True True True)
  assert "SYS-005 operation must match" $
    isProvider ProviderCallOperationDecision
      (decideProviderCallStageByFacts True ExactProviderCallBinding True True False True True)
  assert "SYS-005 implementation entry must match" $
    isProvider ProviderCallImplementationEntryDecision
      (decideProviderCallStageByFacts True ExactProviderCallBinding True True True False True)
  assert "SYS-005 call-site domain must match" $
    isProvider ProviderCallSiteDomainDecision
      (decideProviderCallStageByFacts True ExactProviderCallBinding True True True True False)

  assert "SYS-006 already-bound source-observable effect accepts" $
    isEffect EffectUseAcceptedDecision
      (decideEffectUseByFacts True False SourceObservableEffect)
  assert "SYS-006 source-observable widening rejects" $
    isEffect EffectUseObservableWideningDecision
      (decideEffectUseByFacts False True SourceObservableEffect)
  assert "SYS-006 internal target effect with refinement accepts" $
    isEffect EffectUseAcceptedDecision
      (decideEffectUseByFacts False True InternalRealizationEffect)
  assert "SYS-006 internal target effect without refinement rejects" $
    isEffect EffectUseMissingRefinementDecision
      (decideEffectUseByFacts False False InternalRealizationEffect)

  assert "SYS-006 declared public authority accepts" $
    isAuthority AuthorityExerciseAcceptedDecision
      (decideAuthorityExerciseByFacts True False False PublicAuthority)
  assert "SYS-006 undeclared public authority rejects" $
    isAuthority AuthorityExerciseHiddenPublicDecision
      (decideAuthorityExerciseByFacts False True True PublicAuthority)
  assert "SYS-006 qualified internal authority with exact disposition accepts" $
    isAuthority AuthorityExerciseAcceptedDecision
      (decideAuthorityExerciseByFacts False True True QualifiedInternalAuthority)
  assert "SYS-006 unqualified internal authority rejects" $
    isAuthority AuthorityExerciseHiddenInternalDecision
      (decideAuthorityExerciseByFacts False False True QualifiedInternalAuthority)
  assert "SYS-006 internal disposition mismatch rejects" $
    isAuthority AuthorityExerciseDispositionDecision
      (decideAuthorityExerciseByFacts False True False QualifiedInternalAuthority)

  assert "SYS-006 aggregate authority/effect stage accepts" $
    isAuthorityStage AuthorityEffectStageAcceptedDecision
      (decideAuthorityEffectStageByFacts True True True True True True True True)
  assert "SYS-006 predecessor provider stage is required" $
    isAuthorityStage AuthorityEffectProviderStageDecision
      (decideAuthorityEffectStageByFacts False True True True True True True True)
  assert "SYS-006 surface domain must match" $
    isAuthorityStage AuthorityEffectSurfaceDomainDecision
      (decideAuthorityEffectStageByFacts True False True True True True True True)
  assert "SYS-006 use domain must match" $
    isAuthorityStage AuthorityEffectUseDomainDecision
      (decideAuthorityEffectStageByFacts True True False True True True True True)
  assert "SYS-006 public authority may not escape" $
    isAuthorityStage AuthorityEffectPublicEscapeDecision
      (decideAuthorityEffectStageByFacts True True True False True True True True)
  assert "SYS-006 public authority surface must be complete" $
    isAuthorityStage AuthorityEffectPublicCompletenessDecision
      (decideAuthorityEffectStageByFacts True True True True False True True True)
  assert "SYS-006 internal assignments must be qualified" $
    isAuthorityStage AuthorityEffectInternalAssignmentsDecision
      (decideAuthorityEffectStageByFacts True True True True True False True True)
  assert "SYS-006 all effect uses must be admitted" $
    isAuthorityStage AuthorityEffectUsesDecision
      (decideAuthorityEffectStageByFacts True True True True True True False True)
  assert "SYS-006 all authority exercises must be admitted" $
    isAuthorityStage AuthorityEffectExercisesDecision
      (decideAuthorityEffectStageByFacts True True True True True True True False)
