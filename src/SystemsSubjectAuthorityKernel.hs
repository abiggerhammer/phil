module SystemsSubjectAuthorityKernel where

import qualified Prelude

data SubjectCorrespondenceBasis =
   CheckedSubjectRelation
 | RuntimeRepresentationCoincidence

data ProviderCallBindingBasis =
   ExactProviderCallBinding
 | RuntimeSymbolOnlyProviderCall

data EffectVisibility =
   SourceObservableEffect
 | InternalRealizationEffect

data AuthorityVisibility =
   PublicAuthority
 | QualifiedInternalAuthority

subjectBasisAdmittedBool :: SubjectCorrespondenceBasis -> Prelude.Bool
subjectBasisAdmittedBool basis =
  case basis of {
   CheckedSubjectRelation -> Prelude.True;
   RuntimeRepresentationCoincidence -> Prelude.False}

data SubjectStageDecision =
   SubjectStageAcceptedDecision
 | SubjectStageBasisDecision
 | SubjectStageSystemsSetDecision
 | SubjectStageSystemsValuesDecision
 | SubjectStageExclusivityDecision
 | SubjectStageValidityScopeDecision

decideSubjectStageByFacts :: SubjectCorrespondenceBasis -> Prelude.Bool ->
                             Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
                             SubjectStageDecision
decideSubjectStageByFacts basis systemsSetNonempty systemsValuesExist systemsValueExclusive validityScopeExact =
  case subjectBasisAdmittedBool basis of {
   Prelude.True ->
    case systemsSetNonempty of {
     Prelude.True ->
      case systemsValuesExist of {
       Prelude.True ->
        case systemsValueExclusive of {
         Prelude.True ->
          case validityScopeExact of {
           Prelude.True -> SubjectStageAcceptedDecision;
           Prelude.False -> SubjectStageValidityScopeDecision};
         Prelude.False -> SubjectStageExclusivityDecision};
       Prelude.False -> SubjectStageSystemsValuesDecision};
     Prelude.False -> SubjectStageSystemsSetDecision};
   Prelude.False -> SubjectStageBasisDecision}

providerBindingAdmittedBool :: ProviderCallBindingBasis -> Prelude.Bool
providerBindingAdmittedBool basis =
  case basis of {
   ExactProviderCallBinding -> Prelude.True;
   RuntimeSymbolOnlyProviderCall -> Prelude.False}

data ProviderCallStageDecision =
   ProviderCallStageAcceptedDecision
 | ProviderCallSubjectStageDecision
 | ProviderCallBindingDecision
 | ProviderCallAdmissionDecision
 | ProviderCallInterfaceDecision
 | ProviderCallOperationDecision
 | ProviderCallImplementationEntryDecision
 | ProviderCallSiteDomainDecision

decideProviderCallStageByFacts :: Prelude.Bool -> ProviderCallBindingBasis ->
                                  Prelude.Bool -> Prelude.Bool ->
                                  Prelude.Bool -> Prelude.Bool ->
                                  Prelude.Bool -> ProviderCallStageDecision
decideProviderCallStageByFacts subjectStageAccepted basis selectedAdmissionExact interfaceExact operationExact implementationEntryExact callSiteDomainExact =
  case subjectStageAccepted of {
   Prelude.True ->
    case providerBindingAdmittedBool basis of {
     Prelude.True ->
      case selectedAdmissionExact of {
       Prelude.True ->
        case interfaceExact of {
         Prelude.True ->
          case operationExact of {
           Prelude.True ->
            case implementationEntryExact of {
             Prelude.True ->
              case callSiteDomainExact of {
               Prelude.True -> ProviderCallStageAcceptedDecision;
               Prelude.False -> ProviderCallSiteDomainDecision};
             Prelude.False -> ProviderCallImplementationEntryDecision};
           Prelude.False -> ProviderCallOperationDecision};
         Prelude.False -> ProviderCallInterfaceDecision};
       Prelude.False -> ProviderCallAdmissionDecision};
     Prelude.False -> ProviderCallBindingDecision};
   Prelude.False -> ProviderCallSubjectStageDecision}

data EffectUseDecision =
   EffectUseAcceptedDecision
 | EffectUseObservableWideningDecision
 | EffectUseMissingRefinementDecision

decideEffectUseByFacts :: Prelude.Bool -> Prelude.Bool -> EffectVisibility ->
                          EffectUseDecision
decideEffectUseByFacts alreadyInSourceBound hasRealizationRefinement visibility =
  case alreadyInSourceBound of {
   Prelude.True -> EffectUseAcceptedDecision;
   Prelude.False ->
    case visibility of {
     SourceObservableEffect -> EffectUseObservableWideningDecision;
     InternalRealizationEffect ->
      case hasRealizationRefinement of {
       Prelude.True -> EffectUseAcceptedDecision;
       Prelude.False -> EffectUseMissingRefinementDecision}}}

data AuthorityExerciseDecision =
   AuthorityExerciseAcceptedDecision
 | AuthorityExerciseHiddenPublicDecision
 | AuthorityExerciseHiddenInternalDecision
 | AuthorityExerciseDispositionDecision

decideAuthorityExerciseByFacts :: Prelude.Bool -> Prelude.Bool ->
                                  Prelude.Bool -> AuthorityVisibility ->
                                  AuthorityExerciseDecision
decideAuthorityExerciseByFacts declaredPublic qualifiedInternal dispositionMatches visibility =
  case visibility of {
   PublicAuthority ->
    case declaredPublic of {
     Prelude.True -> AuthorityExerciseAcceptedDecision;
     Prelude.False -> AuthorityExerciseHiddenPublicDecision};
   QualifiedInternalAuthority ->
    case qualifiedInternal of {
     Prelude.True ->
      case dispositionMatches of {
       Prelude.True -> AuthorityExerciseAcceptedDecision;
       Prelude.False -> AuthorityExerciseDispositionDecision};
     Prelude.False -> AuthorityExerciseHiddenInternalDecision}}

data AuthorityEffectStageDecision =
   AuthorityEffectStageAcceptedDecision
 | AuthorityEffectProviderStageDecision
 | AuthorityEffectSurfaceDomainDecision
 | AuthorityEffectUseDomainDecision
 | AuthorityEffectPublicEscapeDecision
 | AuthorityEffectPublicCompletenessDecision
 | AuthorityEffectInternalAssignmentsDecision
 | AuthorityEffectUsesDecision
 | AuthorityEffectExercisesDecision

decideAuthorityEffectStageByFacts :: Prelude.Bool -> Prelude.Bool ->
                                     Prelude.Bool -> Prelude.Bool ->
                                     Prelude.Bool -> Prelude.Bool ->
                                     Prelude.Bool -> Prelude.Bool ->
                                     AuthorityEffectStageDecision
decideAuthorityEffectStageByFacts providerStageAccepted surfaceDomainExact useDomainExact publicSurfaceNoEscape publicSurfaceComplete internalAssignmentsQualified allEffectUsesAdmitted allAuthorityExercisesAdmitted =
  case providerStageAccepted of {
   Prelude.True ->
    case surfaceDomainExact of {
     Prelude.True ->
      case useDomainExact of {
       Prelude.True ->
        case publicSurfaceNoEscape of {
         Prelude.True ->
          case publicSurfaceComplete of {
           Prelude.True ->
            case internalAssignmentsQualified of {
             Prelude.True ->
              case allEffectUsesAdmitted of {
               Prelude.True ->
                case allAuthorityExercisesAdmitted of {
                 Prelude.True -> AuthorityEffectStageAcceptedDecision;
                 Prelude.False -> AuthorityEffectExercisesDecision};
               Prelude.False -> AuthorityEffectUsesDecision};
             Prelude.False -> AuthorityEffectInternalAssignmentsDecision};
           Prelude.False -> AuthorityEffectPublicCompletenessDecision};
         Prelude.False -> AuthorityEffectPublicEscapeDecision};
       Prelude.False -> AuthorityEffectUseDomainDecision};
     Prelude.False -> AuthorityEffectSurfaceDomainDecision};
   Prelude.False -> AuthorityEffectProviderStageDecision}

