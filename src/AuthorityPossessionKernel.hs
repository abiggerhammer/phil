module AuthorityPossessionKernel where

import qualified Prelude

data Bool =
   True
 | False

data Mode =
   Unrestricted
 | Affine
 | Linear

data StructuralPermission =
   WeakeningPermission
 | ContractionPermission

modeAllowsStructuralPermission :: Mode -> StructuralPermission -> Bool
modeAllowsStructuralPermission mode permission =
  case mode of {
   Unrestricted -> True;
   Affine ->
    case permission of {
     WeakeningPermission -> True;
     ContractionPermission -> False};
   Linear -> False}

capabilityCopyAllowed :: Mode -> Bool
capabilityCopyAllowed mode =
  modeAllowsStructuralPermission mode ContractionPermission

capabilityDropAllowed :: Mode -> Bool
capabilityDropAllowed mode =
  modeAllowsStructuralPermission mode WeakeningPermission

data AuthorityExerciseDecision =
   AuthorityExerciseSourceRejected
 | AuthorityExerciseContractRejected
 | AuthorityExerciseSubjectRejected
 | AuthorityExerciseOperationRejected
 | AuthorityExerciseAccepted

decideAuthorityExerciseFacts :: Bool -> Bool -> Bool -> Bool ->
                                AuthorityExerciseDecision
decideAuthorityExerciseFacts sourcePossessed contractMatches subjectMatches operationPermitted =
  case sourcePossessed of {
   True ->
    case contractMatches of {
     True ->
      case subjectMatches of {
       True ->
        case operationPermitted of {
         True -> AuthorityExerciseAccepted;
         False -> AuthorityExerciseOperationRejected};
       False -> AuthorityExerciseSubjectRejected};
     False -> AuthorityExerciseContractRejected};
   False -> AuthorityExerciseSourceRejected}

data AuthorityCopyDecision =
   AuthorityCopyRejected
 | AuthorityCopyAccepted

decideAuthorityCopy :: Mode -> AuthorityCopyDecision
decideAuthorityCopy mode =
  case capabilityCopyAllowed mode of {
   True -> AuthorityCopyAccepted;
   False -> AuthorityCopyRejected}

data AuthorityDropDecision =
   AuthorityDropRejected
 | AuthorityDropAccepted

decideAuthorityDrop :: Mode -> AuthorityDropDecision
decideAuthorityDrop mode =
  case capabilityDropAllowed mode of {
   True -> AuthorityDropAccepted;
   False -> AuthorityDropRejected}
