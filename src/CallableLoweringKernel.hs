module CallableLoweringKernel where

import qualified Prelude

data CallableLoweringProjection =
   MkCallableLoweringProjection Prelude.Bool Prelude.Bool Prelude.Bool 
 Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool 
 Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool 
 Prelude.Bool

projectionContractRevisionEqual :: CallableLoweringProjection -> Prelude.Bool
projectionContractRevisionEqual c =
  case c of {
   MkCallableLoweringProjection projectionContractRevisionEqual0 _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ -> projectionContractRevisionEqual0}

projectionMachineShapeEqual :: CallableLoweringProjection -> Prelude.Bool
projectionMachineShapeEqual c =
  case c of {
   MkCallableLoweringProjection _ projectionMachineShapeEqual0 _ _ _ _ _ _ _
    _ _ _ _ _ _ _ -> projectionMachineShapeEqual0}

projectionOccurrenceEqual :: CallableLoweringProjection -> Prelude.Bool
projectionOccurrenceEqual c =
  case c of {
   MkCallableLoweringProjection _ _ projectionOccurrenceEqual0 _ _ _ _ _ _ _
    _ _ _ _ _ _ -> projectionOccurrenceEqual0}

projectionStructuralModeEqual :: CallableLoweringProjection -> Prelude.Bool
projectionStructuralModeEqual c =
  case c of {
   MkCallableLoweringProjection _ _ _ projectionStructuralModeEqual0 _ _ _ _
    _ _ _ _ _ _ _ _ -> projectionStructuralModeEqual0}

projectionCapturesEqual :: CallableLoweringProjection -> Prelude.Bool
projectionCapturesEqual c =
  case c of {
   MkCallableLoweringProjection _ _ _ _ projectionCapturesEqual0 _ _ _ _ _ _
    _ _ _ _ _ -> projectionCapturesEqual0}

projectionCalleeTransitionEqual :: CallableLoweringProjection -> Prelude.Bool
projectionCalleeTransitionEqual c =
  case c of {
   MkCallableLoweringProjection _ _ _ _ _ projectionCalleeTransitionEqual0 _
    _ _ _ _ _ _ _ _ _ -> projectionCalleeTransitionEqual0}

projectionCallerAuthorityEqual :: CallableLoweringProjection -> Prelude.Bool
projectionCallerAuthorityEqual c =
  case c of {
   MkCallableLoweringProjection _ _ _ _ _ _ projectionCallerAuthorityEqual0 _
    _ _ _ _ _ _ _ _ -> projectionCallerAuthorityEqual0}

projectionInternalAuthorityEqual :: CallableLoweringProjection ->
                                    Prelude.Bool
projectionInternalAuthorityEqual c =
  case c of {
   MkCallableLoweringProjection _ _ _ _ _ _ _
    projectionInternalAuthorityEqual0 _ _ _ _ _ _ _ _ ->
    projectionInternalAuthorityEqual0}

projectionEffectBoundEqual :: CallableLoweringProjection -> Prelude.Bool
projectionEffectBoundEqual c =
  case c of {
   MkCallableLoweringProjection _ _ _ _ _ _ _ _ projectionEffectBoundEqual0 _
    _ _ _ _ _ _ -> projectionEffectBoundEqual0}

projectionFailuresEqual :: CallableLoweringProjection -> Prelude.Bool
projectionFailuresEqual c =
  case c of {
   MkCallableLoweringProjection _ _ _ _ _ _ _ _ _ projectionFailuresEqual0 _
    _ _ _ _ _ -> projectionFailuresEqual0}

projectionLoanScopesEqual :: CallableLoweringProjection -> Prelude.Bool
projectionLoanScopesEqual c =
  case c of {
   MkCallableLoweringProjection _ _ _ _ _ _ _ _ _ _
    projectionLoanScopesEqual0 _ _ _ _ _ -> projectionLoanScopesEqual0}

projectionEffectAccountingEqual :: CallableLoweringProjection -> Prelude.Bool
projectionEffectAccountingEqual c =
  case c of {
   MkCallableLoweringProjection _ _ _ _ _ _ _ _ _ _ _
    projectionEffectAccountingEqual0 _ _ _ _ ->
    projectionEffectAccountingEqual0}

projectionFailureAccountingEqual :: CallableLoweringProjection ->
                                    Prelude.Bool
projectionFailureAccountingEqual c =
  case c of {
   MkCallableLoweringProjection _ _ _ _ _ _ _ _ _ _ _ _
    projectionFailureAccountingEqual0 _ _ _ ->
    projectionFailureAccountingEqual0}

projectionAssumptionAccountingEqual :: CallableLoweringProjection ->
                                       Prelude.Bool
projectionAssumptionAccountingEqual c =
  case c of {
   MkCallableLoweringProjection _ _ _ _ _ _ _ _ _ _ _ _ _
    projectionAssumptionAccountingEqual0 _ _ ->
    projectionAssumptionAccountingEqual0}

projectionCarrierAccountingEqual :: CallableLoweringProjection ->
                                    Prelude.Bool
projectionCarrierAccountingEqual c =
  case c of {
   MkCallableLoweringProjection _ _ _ _ _ _ _ _ _ _ _ _ _ _
    projectionCarrierAccountingEqual0 _ -> projectionCarrierAccountingEqual0}

projectionCostAccountingEqual :: CallableLoweringProjection -> Prelude.Bool
projectionCostAccountingEqual c =
  case c of {
   MkCallableLoweringProjection _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    projectionCostAccountingEqual0 -> projectionCostAccountingEqual0}

data CallableLoweringDecision =
   CallableLoweringAccepted
 | CallableLoweringContractRevisionMismatch
 | CallableLoweringMachineShapeMismatch
 | CallableLoweringOccurrenceMismatch
 | CallableLoweringStructuralModeMismatch
 | CallableLoweringCaptureMismatch
 | CallableLoweringCalleeTransitionMismatch
 | CallableLoweringCallerAuthorityMismatch
 | CallableLoweringInternalAuthorityMismatch
 | CallableLoweringEffectBoundMismatch
 | CallableLoweringFailureMismatch
 | CallableLoweringLoanScopeMismatch
 | CallableLoweringEffectAccountingMismatch
 | CallableLoweringFailureAccountingMismatch
 | CallableLoweringAssumptionAccountingMismatch
 | CallableLoweringCarrierAccountingMismatch
 | CallableLoweringCostAccountingMismatch

decideCallableLowering :: CallableLoweringProjection ->
                          CallableLoweringDecision
decideCallableLowering projection =
  case projectionContractRevisionEqual projection of {
   Prelude.True ->
    case projectionMachineShapeEqual projection of {
     Prelude.True ->
      case projectionOccurrenceEqual projection of {
       Prelude.True ->
        case projectionStructuralModeEqual projection of {
         Prelude.True ->
          case projectionCapturesEqual projection of {
           Prelude.True ->
            case projectionCalleeTransitionEqual projection of {
             Prelude.True ->
              case projectionCallerAuthorityEqual projection of {
               Prelude.True ->
                case projectionInternalAuthorityEqual projection of {
                 Prelude.True ->
                  case projectionEffectBoundEqual projection of {
                   Prelude.True ->
                    case projectionFailuresEqual projection of {
                     Prelude.True ->
                      case projectionLoanScopesEqual projection of {
                       Prelude.True ->
                        case projectionEffectAccountingEqual projection of {
                         Prelude.True ->
                          case projectionFailureAccountingEqual projection of {
                           Prelude.True ->
                            case projectionAssumptionAccountingEqual
                                   projection of {
                             Prelude.True ->
                              case projectionCarrierAccountingEqual
                                     projection of {
                               Prelude.True ->
                                case projectionCostAccountingEqual projection of {
                                 Prelude.True -> CallableLoweringAccepted;
                                 Prelude.False ->
                                  CallableLoweringCostAccountingMismatch};
                               Prelude.False ->
                                CallableLoweringCarrierAccountingMismatch};
                             Prelude.False ->
                              CallableLoweringAssumptionAccountingMismatch};
                           Prelude.False ->
                            CallableLoweringFailureAccountingMismatch};
                         Prelude.False ->
                          CallableLoweringEffectAccountingMismatch};
                       Prelude.False -> CallableLoweringLoanScopeMismatch};
                     Prelude.False -> CallableLoweringFailureMismatch};
                   Prelude.False -> CallableLoweringEffectBoundMismatch};
                 Prelude.False -> CallableLoweringInternalAuthorityMismatch};
               Prelude.False -> CallableLoweringCallerAuthorityMismatch};
             Prelude.False -> CallableLoweringCalleeTransitionMismatch};
           Prelude.False -> CallableLoweringCaptureMismatch};
         Prelude.False -> CallableLoweringStructuralModeMismatch};
       Prelude.False -> CallableLoweringOccurrenceMismatch};
     Prelude.False -> CallableLoweringMachineShapeMismatch};
   Prelude.False -> CallableLoweringContractRevisionMismatch}

