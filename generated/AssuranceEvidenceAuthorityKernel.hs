module AssuranceEvidenceAuthorityKernel where

import qualified Prelude

data GateResult =
   GateRejected
 | GateAccepted

data ArtifactAuthority =
   MkArtifactAuthority Prelude.Bool Prelude.Bool Prelude.Bool

artifactDeclared :: ArtifactAuthority -> Prelude.Bool
artifactDeclared a =
  case a of {
   MkArtifactAuthority artifactDeclared0 _ _ -> artifactDeclared0}

artifactIdentityMatches :: ArtifactAuthority -> Prelude.Bool
artifactIdentityMatches a =
  case a of {
   MkArtifactAuthority _ artifactIdentityMatches0 _ ->
    artifactIdentityMatches0}

artifactDigestMatchesTrustedAvailability :: ArtifactAuthority -> Prelude.Bool
artifactDigestMatchesTrustedAvailability a =
  case a of {
   MkArtifactAuthority _ _ artifactDigestMatchesTrustedAvailability0 ->
    artifactDigestMatchesTrustedAvailability0}

verifyArtifactAuthority :: ArtifactAuthority -> GateResult
verifyArtifactAuthority artifact =
  case artifactDeclared artifact of {
   Prelude.True ->
    case artifactIdentityMatches artifact of {
     Prelude.True ->
      case artifactDigestMatchesTrustedAvailability artifact of {
       Prelude.True -> GateAccepted;
       Prelude.False -> GateRejected};
     Prelude.False -> GateRejected};
   Prelude.False -> GateRejected}

data RuntimeAuthority =
   MkRuntimeAuthority Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool 
 Prelude.Bool

runtimeMechanismPresent :: RuntimeAuthority -> Prelude.Bool
runtimeMechanismPresent r =
  case r of {
   MkRuntimeAuthority runtimeMechanismPresent0 _ _ _ _ ->
    runtimeMechanismPresent0}

runtimeMechanismComplete :: RuntimeAuthority -> Prelude.Bool
runtimeMechanismComplete r =
  case r of {
   MkRuntimeAuthority _ runtimeMechanismComplete0 _ _ _ ->
    runtimeMechanismComplete0}

runtimeResiduePresent :: RuntimeAuthority -> Prelude.Bool
runtimeResiduePresent r =
  case r of {
   MkRuntimeAuthority _ _ runtimeResiduePresent0 _ _ ->
    runtimeResiduePresent0}

runtimeCostReferencePresent :: RuntimeAuthority -> Prelude.Bool
runtimeCostReferencePresent r =
  case r of {
   MkRuntimeAuthority _ _ _ runtimeCostReferencePresent0 _ ->
    runtimeCostReferencePresent0}

runtimeCostReferenceKnown :: RuntimeAuthority -> Prelude.Bool
runtimeCostReferenceKnown r =
  case r of {
   MkRuntimeAuthority _ _ _ _ runtimeCostReferenceKnown0 ->
    runtimeCostReferenceKnown0}

verifyRuntimeAuthority :: RuntimeAuthority -> GateResult
verifyRuntimeAuthority runtime =
  case runtimeMechanismPresent runtime of {
   Prelude.True ->
    case runtimeMechanismComplete runtime of {
     Prelude.True ->
      case runtimeResiduePresent runtime of {
       Prelude.True ->
        case runtimeCostReferencePresent runtime of {
         Prelude.True ->
          case runtimeCostReferenceKnown runtime of {
           Prelude.True -> GateAccepted;
           Prelude.False -> GateRejected};
         Prelude.False -> GateRejected};
       Prelude.False -> GateRejected};
     Prelude.False -> GateRejected};
   Prelude.False -> GateRejected}

decideArtifactAuthorityByFacts :: Prelude.Bool -> Prelude.Bool ->
                                  Prelude.Bool -> GateResult
decideArtifactAuthorityByFacts declared identityMatches digestMatches =
  verifyArtifactAuthority (MkArtifactAuthority declared identityMatches
    digestMatches)

decideRuntimeAuthorityByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
                                 -> Prelude.Bool -> Prelude.Bool ->
                                 GateResult
decideRuntimeAuthorityByFacts mechanismPresent mechanismComplete residuePresent costReferencePresent costReferenceKnown =
  verifyRuntimeAuthority (MkRuntimeAuthority mechanismPresent
    mechanismComplete residuePresent costReferencePresent costReferenceKnown)

