module AuthorityPossessionKernel where

import qualified Prelude

data Mode =
   Unrestricted
 | Affine
 | Linear

data StructuralPermission =
   WeakeningPermission
 | ContractionPermission

modeAllowsStructuralPermission :: Mode -> StructuralPermission ->
                                  Prelude.Bool
modeAllowsStructuralPermission mode permission =
  case mode of {
   Unrestricted -> Prelude.True;
   Affine ->
    case permission of {
     WeakeningPermission -> Prelude.True;
     ContractionPermission -> Prelude.False};
   Linear -> Prelude.False}

capabilityCopyAllowed :: Mode -> Prelude.Bool
capabilityCopyAllowed mode =
  modeAllowsStructuralPermission mode ContractionPermission

capabilityDropAllowed :: Mode -> Prelude.Bool
capabilityDropAllowed mode =
  modeAllowsStructuralPermission mode WeakeningPermission

data AuthorityExerciseDecision =
   AuthorityExerciseSourceRejected
 | AuthorityExerciseContractRejected
 | AuthorityExerciseSubjectRejected
 | AuthorityExerciseOperationRejected
 | AuthorityExerciseAccepted

decideAuthorityExerciseFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
                                -> Prelude.Bool -> AuthorityExerciseDecision
decideAuthorityExerciseFacts sourcePossessed contractMatches subjectMatches operationPermitted =
  case sourcePossessed of {
   Prelude.True ->
    case contractMatches of {
     Prelude.True ->
      case subjectMatches of {
       Prelude.True ->
        case operationPermitted of {
         Prelude.True -> AuthorityExerciseAccepted;
         Prelude.False -> AuthorityExerciseOperationRejected};
       Prelude.False -> AuthorityExerciseSubjectRejected};
     Prelude.False -> AuthorityExerciseContractRejected};
   Prelude.False -> AuthorityExerciseSourceRejected}

data AuthorityCopyDecision =
   AuthorityCopyRejected
 | AuthorityCopyAccepted

decideAuthorityCopy :: Mode -> AuthorityCopyDecision
decideAuthorityCopy mode =
  case capabilityCopyAllowed mode of {
   Prelude.True -> AuthorityCopyAccepted;
   Prelude.False -> AuthorityCopyRejected}

data AuthorityDropDecision =
   AuthorityDropRejected
 | AuthorityDropAccepted

decideAuthorityDrop :: Mode -> AuthorityDropDecision
decideAuthorityDrop mode =
  case capabilityDropAllowed mode of {
   Prelude.True -> AuthorityDropAccepted;
   Prelude.False -> AuthorityDropRejected}

