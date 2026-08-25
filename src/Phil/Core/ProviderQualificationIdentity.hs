{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.ProviderQualificationIdentity
  ( QualificationClaimRevision (..)
  , QualificationEvidenceRevision (..)
  , QualificationAdmissionRevision (..)
  , ProviderQualificationLayer (..)
  , ProviderQualificationSubject (..)
  , ProviderQualificationClaimIdentityInput (..)
  , ProviderQualificationEvidenceIdentityInput (..)
  , ProviderQualificationAdmissionDecision (..)
  , ProviderQualificationAdmissionIdentityInput (..)
  , CheckedProviderQualificationEvidenceIdentity (..)
  , CheckedProviderQualificationAdmissionIdentity (..)
  , ProviderQualificationIdentityError (..)
  , deriveQualificationClaimRevision
  , deriveQualificationEvidenceRevision
  , deriveQualificationAdmissionRevision
  , checkQualificationEvidenceIdentity
  , checkQualificationAdmissionIdentity
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Static
  ( DefinitionRevision (..)
  , InterfaceRevision (..)
  , SemanticForm (..)
  , canonicalSemanticForm
  )

newtype QualificationClaimRevision = QualificationClaimRevision
  { unQualificationClaimRevision :: Text }
  deriving (Eq, Ord, Show)

newtype QualificationEvidenceRevision = QualificationEvidenceRevision
  { unQualificationEvidenceRevision :: Text }
  deriving (Eq, Ord, Show)

newtype QualificationAdmissionRevision = QualificationAdmissionRevision
  { unQualificationAdmissionRevision :: Text }
  deriving (Eq, Ord, Show)

data ProviderQualificationLayer
  = SemanticImplementationQualification
  | ConcreteRealizationQualification
  | CollapsedOpaqueQualification
  deriving (Eq, Ord, Show)

data ProviderQualificationSubject
  = SemanticProviderImplementation DefinitionRevision
  | ConcreteProviderRealization DefinitionRevision Text
  | OpaqueProviderBoundary Text
  deriving (Eq, Ord, Show)

-- | Identity-bearing semantic statement for one conditional provider
-- qualification. Evidence bytes, proof artifacts, current build policy, and one
-- build's admission decision are deliberately absent.
data ProviderQualificationClaimIdentityInput = ProviderQualificationClaimIdentityInput
  { qualificationClaimRequiredInterface :: InterfaceRevision
  , qualificationClaimSubject :: ProviderQualificationSubject
  , qualificationClaimLayer :: ProviderQualificationLayer
  , qualificationClaimSemanticRelations :: Map.Map Text SemanticForm
  , qualificationClaimConditions :: Set.Set Text
  , qualificationClaimValidityScope :: SemanticForm
  }
  deriving (Eq, Ord, Show)

-- | Evidence/disposition bundle for one exact semantic claim. Different bundles
-- may justify the same claim and therefore get distinct evidence revisions while
-- retaining the same claim revision.
data ProviderQualificationEvidenceIdentityInput = ProviderQualificationEvidenceIdentityInput
  { qualificationEvidenceClaimRevision :: QualificationClaimRevision
  , qualificationEvidenceObligationDispositions :: Map.Map Text SemanticForm
  , qualificationEvidenceRefs :: Set.Set Text
  , qualificationEvidenceProofRefs :: Set.Set Text
  , qualificationEvidenceTranslationValidationRefs :: Set.Set Text
  , qualificationEvidenceRuntimeEnforcementRefs :: Set.Set Text
  , qualificationEvidenceAssumptionRefs :: Set.Set Text
  , qualificationEvidenceValidityDependencies :: Set.Set Text
  }
  deriving (Eq, Ord, Show)

data ProviderQualificationAdmissionDecision
  = QualificationAdmitted
  | QualificationRejected (Set.Set Text)
  deriving (Eq, Ord, Show)

-- | One contextual build-admission decision. This is intentionally downstream
-- of both semantic claim identity and evidence identity.
data ProviderQualificationAdmissionIdentityInput = ProviderQualificationAdmissionIdentityInput
  { qualificationAdmissionClaimRevision :: QualificationClaimRevision
  , qualificationAdmissionEvidenceRevision :: QualificationEvidenceRevision
  , qualificationAdmissionProviderOccurrence :: Text
  , qualificationAdmissionRequiredInterface :: InterfaceRevision
  , qualificationAdmissionRealizationContextRevision :: Text
  , qualificationAdmissionAssurancePolicyRevision :: Text
  , qualificationAdmissionConditionDispositions :: Map.Map Text SemanticForm
  , qualificationAdmissionDependencyAdmissions :: Set.Set Text
  , qualificationAdmissionSelectedArtifactRuntimeAbi :: Maybe Text
  , qualificationAdmissionExportedRuntimeObligations :: Set.Set Text
  , qualificationAdmissionExportedDeploymentRequirements :: Set.Set Text
  , qualificationAdmissionDecision :: ProviderQualificationAdmissionDecision
  }
  deriving (Eq, Ord, Show)

data CheckedProviderQualificationEvidenceIdentity = CheckedProviderQualificationEvidenceIdentity
  { checkedQualificationEvidenceClaimRevision :: QualificationClaimRevision
  , checkedQualificationEvidenceRevision :: QualificationEvidenceRevision
  }
  deriving (Eq, Ord, Show)

data CheckedProviderQualificationAdmissionIdentity = CheckedProviderQualificationAdmissionIdentity
  { checkedQualificationAdmissionClaimRevision :: QualificationClaimRevision
  , checkedQualificationAdmissionEvidenceRevision :: QualificationEvidenceRevision
  , checkedQualificationAdmissionRevision :: QualificationAdmissionRevision
  , checkedQualificationAdmissionDecision :: ProviderQualificationAdmissionDecision
  }
  deriving (Eq, Ord, Show)

data ProviderQualificationIdentityError
  = QualificationEvidenceClaimRevisionMismatch
      QualificationClaimRevision QualificationClaimRevision
  | QualificationAdmissionClaimRevisionMismatch
      QualificationClaimRevision QualificationClaimRevision
  | QualificationAdmissionEvidenceRevisionMismatch
      QualificationEvidenceRevision QualificationEvidenceRevision
  | QualificationAdmissionInterfaceMismatch InterfaceRevision InterfaceRevision
  deriving (Eq, Ord, Show)

deriveQualificationClaimRevision
  :: ProviderQualificationClaimIdentityInput
  -> QualificationClaimRevision
deriveQualificationClaimRevision input = QualificationClaimRevision
  ("phil.provider-qualification.claim.canonical.v1:"
    <> canonicalSemanticForm (SemanticRecord (Map.fromList
      [ ("required_interface", SemanticAtom
          (unInterfaceRevision (qualificationClaimRequiredInterface input)))
      , ("subject", subjectSemantic (qualificationClaimSubject input))
      , ("layer", SemanticAtom (layerText (qualificationClaimLayer input)))
      , ("semantic_relations", SemanticRecord
          (qualificationClaimSemanticRelations input))
      , ("conditions", SemanticUnordered
          (Set.map SemanticAtom (qualificationClaimConditions input)))
      , ("validity_scope", qualificationClaimValidityScope input)
      ])))

deriveQualificationEvidenceRevision
  :: ProviderQualificationEvidenceIdentityInput
  -> QualificationEvidenceRevision
deriveQualificationEvidenceRevision input = QualificationEvidenceRevision
  ("phil.provider-qualification.evidence.canonical.v1:"
    <> canonicalSemanticForm (SemanticRecord (Map.fromList
      [ ("claim_revision", SemanticAtom
          (unQualificationClaimRevision (qualificationEvidenceClaimRevision input)))
      , ("obligation_dispositions", SemanticRecord
          (qualificationEvidenceObligationDispositions input))
      , ("evidence_refs", textSetSemantic (qualificationEvidenceRefs input))
      , ("proof_refs", textSetSemantic (qualificationEvidenceProofRefs input))
      , ("translation_validation_refs", textSetSemantic
          (qualificationEvidenceTranslationValidationRefs input))
      , ("runtime_enforcement_refs", textSetSemantic
          (qualificationEvidenceRuntimeEnforcementRefs input))
      , ("assumption_refs", textSetSemantic
          (qualificationEvidenceAssumptionRefs input))
      , ("validity_dependencies", textSetSemantic
          (qualificationEvidenceValidityDependencies input))
      ])))

deriveQualificationAdmissionRevision
  :: ProviderQualificationAdmissionIdentityInput
  -> QualificationAdmissionRevision
deriveQualificationAdmissionRevision input = QualificationAdmissionRevision
  ("phil.provider-qualification.admission.canonical.v1:"
    <> canonicalSemanticForm (SemanticRecord (Map.fromList
      [ ("claim_revision", SemanticAtom
          (unQualificationClaimRevision (qualificationAdmissionClaimRevision input)))
      , ("evidence_revision", SemanticAtom
          (unQualificationEvidenceRevision (qualificationAdmissionEvidenceRevision input)))
      , ("provider_occurrence", SemanticAtom
          (qualificationAdmissionProviderOccurrence input))
      , ("required_interface", SemanticAtom
          (unInterfaceRevision (qualificationAdmissionRequiredInterface input)))
      , ("realization_context_revision", SemanticAtom
          (qualificationAdmissionRealizationContextRevision input))
      , ("assurance_policy_revision", SemanticAtom
          (qualificationAdmissionAssurancePolicyRevision input))
      , ("condition_dispositions", SemanticRecord
          (qualificationAdmissionConditionDispositions input))
      , ("dependency_admissions", textSetSemantic
          (qualificationAdmissionDependencyAdmissions input))
      , ("selected_artifact_runtime_abi", maybeSemantic
          (qualificationAdmissionSelectedArtifactRuntimeAbi input))
      , ("exported_runtime_obligations", textSetSemantic
          (qualificationAdmissionExportedRuntimeObligations input))
      , ("exported_deployment_requirements", textSetSemantic
          (qualificationAdmissionExportedDeploymentRequirements input))
      , ("decision", decisionSemantic (qualificationAdmissionDecision input))
      ])))

checkQualificationEvidenceIdentity
  :: ProviderQualificationClaimIdentityInput
  -> ProviderQualificationEvidenceIdentityInput
  -> Either ProviderQualificationIdentityError CheckedProviderQualificationEvidenceIdentity
checkQualificationEvidenceIdentity claim evidence
  | qualificationEvidenceClaimRevision evidence /= expectedClaim =
      Left (QualificationEvidenceClaimRevisionMismatch
        expectedClaim (qualificationEvidenceClaimRevision evidence))
  | otherwise = Right CheckedProviderQualificationEvidenceIdentity
      { checkedQualificationEvidenceClaimRevision = expectedClaim
      , checkedQualificationEvidenceRevision = deriveQualificationEvidenceRevision evidence
      }
  where
    expectedClaim = deriveQualificationClaimRevision claim

checkQualificationAdmissionIdentity
  :: ProviderQualificationClaimIdentityInput
  -> ProviderQualificationEvidenceIdentityInput
  -> ProviderQualificationAdmissionIdentityInput
  -> Either ProviderQualificationIdentityError CheckedProviderQualificationAdmissionIdentity
checkQualificationAdmissionIdentity claim evidence admission = do
  checkedEvidence <- checkQualificationEvidenceIdentity claim evidence
  let expectedClaim = checkedQualificationEvidenceClaimRevision checkedEvidence
      expectedEvidence = checkedQualificationEvidenceRevision checkedEvidence
      expectedInterface = qualificationClaimRequiredInterface claim
  if qualificationAdmissionClaimRevision admission /= expectedClaim
    then Left (QualificationAdmissionClaimRevisionMismatch
      expectedClaim (qualificationAdmissionClaimRevision admission))
    else if qualificationAdmissionEvidenceRevision admission /= expectedEvidence
      then Left (QualificationAdmissionEvidenceRevisionMismatch
        expectedEvidence (qualificationAdmissionEvidenceRevision admission))
      else if qualificationAdmissionRequiredInterface admission /= expectedInterface
        then Left (QualificationAdmissionInterfaceMismatch
          expectedInterface (qualificationAdmissionRequiredInterface admission))
        else Right CheckedProviderQualificationAdmissionIdentity
          { checkedQualificationAdmissionClaimRevision = expectedClaim
          , checkedQualificationAdmissionEvidenceRevision = expectedEvidence
          , checkedQualificationAdmissionRevision = deriveQualificationAdmissionRevision admission
          , checkedQualificationAdmissionDecision = qualificationAdmissionDecision admission
          }

subjectSemantic :: ProviderQualificationSubject -> SemanticForm
subjectSemantic subject = case subject of
  SemanticProviderImplementation revision -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "semantic-implementation")
    , ("definition_revision", SemanticAtom (unDefinitionRevision revision))
    ])
  ConcreteProviderRealization revision artifact -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "concrete-realization")
    , ("definition_revision", SemanticAtom (unDefinitionRevision revision))
    , ("artifact", SemanticAtom artifact)
    ])
  OpaqueProviderBoundary boundary -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "opaque-boundary")
    , ("boundary", SemanticAtom boundary)
    ])

layerText :: ProviderQualificationLayer -> Text
layerText layer = case layer of
  SemanticImplementationQualification -> "semantic-implementation"
  ConcreteRealizationQualification -> "concrete-realization"
  CollapsedOpaqueQualification -> "collapsed-opaque"

textSetSemantic :: Set.Set Text -> SemanticForm
textSetSemantic = SemanticUnordered . Set.map SemanticAtom

maybeSemantic :: Maybe Text -> SemanticForm
maybeSemantic value = case value of
  Nothing -> SemanticRecord (Map.singleton "none" (SemanticAtom ""))
  Just text -> SemanticRecord (Map.singleton "some" (SemanticAtom text))

decisionSemantic :: ProviderQualificationAdmissionDecision -> SemanticForm
decisionSemantic decision = case decision of
  QualificationAdmitted -> SemanticRecord
    (Map.singleton "admitted" (SemanticAtom ""))
  QualificationRejected reasons -> SemanticRecord
    (Map.singleton "rejected" (textSetSemantic reasons))
