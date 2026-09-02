module SystemsIdentityKernel where

import qualified Prelude

data ArtifactIdentityDecision =
   ArtifactIdentityAcceptedDecision
 | ArtifactIdentitySourceDecision
 | ArtifactIdentityTargetDecision
 | ArtifactIdentityImplementationDecision
 | ArtifactIdentityDeclaredRootDecision
 | ArtifactIdentityManifestRootDecision

decideArtifactIdentityByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
                                 -> Prelude.Bool -> Prelude.Bool ->
                                 ArtifactIdentityDecision
decideArtifactIdentityByFacts sourceMatches targetMatches implementationMatches declaredRootMatches manifestRootMatches =
  case sourceMatches of {
   Prelude.True ->
    case targetMatches of {
     Prelude.True ->
      case implementationMatches of {
       Prelude.True ->
        case declaredRootMatches of {
         Prelude.True ->
          case manifestRootMatches of {
           Prelude.True -> ArtifactIdentityAcceptedDecision;
           Prelude.False -> ArtifactIdentityManifestRootDecision};
         Prelude.False -> ArtifactIdentityDeclaredRootDecision};
       Prelude.False -> ArtifactIdentityImplementationDecision};
     Prelude.False -> ArtifactIdentityTargetDecision};
   Prelude.False -> ArtifactIdentitySourceDecision}

data DecisionBindingDecision =
   DecisionBindingAcceptedDecision
 | DecisionBindingNonemptyDecision
 | DecisionBindingMapKeyDecision
 | DecisionBindingDigestDecision
 | DecisionBindingSourceDecision
 | DecisionBindingTargetDecision

decideDecisionBindingByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
                                -> Prelude.Bool -> Prelude.Bool ->
                                DecisionBindingDecision
decideDecisionBindingByFacts nonemptyStableId mapKeyMatches digestMatches sourceMatches targetMatches =
  case nonemptyStableId of {
   Prelude.True ->
    case mapKeyMatches of {
     Prelude.True ->
      case digestMatches of {
       Prelude.True ->
        case sourceMatches of {
         Prelude.True ->
          case targetMatches of {
           Prelude.True -> DecisionBindingAcceptedDecision;
           Prelude.False -> DecisionBindingTargetDecision};
         Prelude.False -> DecisionBindingSourceDecision};
       Prelude.False -> DecisionBindingDigestDecision};
     Prelude.False -> DecisionBindingMapKeyDecision};
   Prelude.False -> DecisionBindingNonemptyDecision}

