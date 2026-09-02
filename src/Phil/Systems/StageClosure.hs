{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.StageClosure
  ( ClosedStageContractRevision (..)
  , ConcreteStageClosure (..)
  , StageClosureBundle (..)
  , StageClosureVerificationError (..)
  , concreteSubjectStage
  , nextStageSubjectStage
  , deriveClosedStageContractRevision
  , makeStageClosureBundle
  , verifyStageClosureBundle
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Static
  ( InstanceRevision (..)
  , RealizationRevision (..)
  , SemanticForm (..)
  , canonicalSemanticForm
  )
import Phil.Systems.AssumptionDependency
  ( AssumptionDependencyStageBundle (..)
  )
import Phil.Systems.AuthorityEffectCorrespondence
  ( AuthorityEffectStageBundle (..)
  )
import Phil.Systems.BoundaryCommitCorrespondence
  ( BoundaryCommitStageBundle (..)
  , BoundaryCommitStageRevision (..)
  , BoundaryCommitVerificationError
  , verifyBoundaryCommitStageBundle
  )
import Phil.Systems.BranchResourceFailure
  ( BranchResourceStageBundle (..)
  , BranchResourceStageRevision (..)
  , BranchResourceStageVerificationError
  , verifyBranchResourceStageBundle
  )
import Phil.Systems.ControlStateProjection
  ( ControlStateStageBundle (..)
  )
import Phil.Systems.CostAttribution
  ( CostAttributionStageBundle (..)
  )
import Phil.Systems.EvidenceErasure
  ( EvidenceErasureStageBundle (..)
  )
import Phil.Systems.EvidenceSubjectTransfer
  ( EvidenceTransferStageBundle (..)
  )
import Phil.Systems.NextStageRequirement
  ( NextStageRequirementStageBundle (..)
  , NextStageRequirementStageRevision (..)
  , NextStageRequirementVerificationError
  , verifyNextStageRequirementStageBundle
  )
import Phil.Systems.Phase1Stage
  ( Phase1StageBundle (..)
  , Phase1StageContractRevision (..)
  , SystemsArtifactRevision (..)
  , deriveSystemsArtifactRevision
  )
import Phil.Systems.ProtocolStateCorrespondence
  ( ProtocolStateStageBundle (..)
  )
import Phil.Systems.ProviderCallCorrespondence
  ( ProviderCallStageBundle (..)
  )
import Phil.Systems.RuntimeClaimBinding
  ( RuntimeClaimStageBundle (..)
  )
import Phil.Systems.RuntimePrimitiveReuse
  ( RuntimePrimitiveStageBundle (..)
  )
import Phil.Systems.StagingEffect
  ( StagingEffectStageBundle (..)
  )
import Phil.Systems.SubjectCorrespondence
  ( SubjectStageBundle (..)
  , SubjectStageRevision (..)
  )
import Phil.Systems.TargetStrengthening
  ( TargetStrengtheningStageBundle (..)
  )
import qualified SystemsRealizationEffectsKernel as RealizeKernel
import qualified SystemsStageClosureKernel as ClosureKernel

newtype ClosedStageContractRevision = ClosedStageContractRevision
  { unClosedStageContractRevision :: Text
  }
  deriving (Eq, Ord, Show)

data ConcreteStageClosure
  = ConcreteThroughBranch BranchResourceStageBundle
  | ConcreteThroughBoundary BoundaryCommitStageBundle
  deriving (Eq, Show)

data StageClosureBundle = StageClosureBundle
  { stageClosureConcrete :: ConcreteStageClosure
  , stageClosureNextStage :: NextStageRequirementStageBundle
  , stageClosureSystemsArtifactRevision :: SystemsArtifactRevision
  , stageClosureContractRevision :: ClosedStageContractRevision
  }
  deriving (Eq, Show)

data StageClosureVerificationError
  = StageClosureBranchError BranchResourceStageVerificationError
  | StageClosureBoundaryError BoundaryCommitVerificationError
  | StageClosureNextStageError NextStageRequirementVerificationError
  | StageClosureSubjectRevisionMismatch SubjectStageRevision SubjectStageRevision
  | StageClosureInstanceRevisionMismatch InstanceRevision InstanceRevision
  | StageClosureRealizationRevisionMismatch RealizationRevision RealizationRevision
  | StageClosureSystemsRevisionMismatch SystemsArtifactRevision SystemsArtifactRevision
  | StageClosurePhase1ContractRevisionMismatch
      Phase1StageContractRevision Phase1StageContractRevision
  | StageClosureVerifierProfileMismatch Text Text
  | StageClosureStoredSystemsRevisionMismatch
      SystemsArtifactRevision SystemsArtifactRevision
  | StageClosureContractRevisionMismatch
      ClosedStageContractRevision ClosedStageContractRevision
  deriving (Eq, Show)

concreteSubjectStage :: ConcreteStageClosure -> SubjectStageBundle
concreteSubjectStage concrete = case concrete of
  ConcreteThroughBranch bundle -> subjectFromBranch bundle
  ConcreteThroughBoundary bundle ->
    subjectFromBranch
      . controlStateStageBase
      . protocolStateStageBase
      . boundaryCommitStageBase
      $ bundle

nextStageSubjectStage
  :: NextStageRequirementStageBundle
  -> SubjectStageBundle
nextStageSubjectStage =
  evidenceTransferStageBase
  . evidenceErasureStageBase
  . assumptionDependencyStageBase
  . targetStrengtheningStageBase
  . runtimeClaimStageBase
  . runtimePrimitiveStageBase
  . stagingEffectStageBase
  . costAttributionStageBase
  . nextStageRequirementStageBase

subjectFromBranch :: BranchResourceStageBundle -> SubjectStageBundle
subjectFromBranch =
  providerCallStageBase
  . authorityEffectStageBase
  . branchResourceStageBase

deriveClosedStageContractRevision
  :: StageClosureBundle
  -> ClosedStageContractRevision
deriveClosedStageContractRevision bundle = ClosedStageContractRevision
  ("phil.phase1.stage.closed.canonical.v1:"
    <> canonicalSemanticForm (SemanticRecord (Map.fromList
      [ ("instance", SemanticAtom
          (instanceText (phase1StageInstanceRevision common)))
      , ("realization", SemanticAtom
          (realizationText (phase1StageRealizationRevision common)))
      , ("systems", SemanticAtom
          (unSystemsArtifactRevision (stageClosureSystemsArtifactRevision bundle)))
      , ("phase1_stage", SemanticAtom
          (phase1RevisionText (phase1StageContractRevision common)))
      , ("subject_stage", SemanticAtom
          (unSubjectStageRevision (subjectStageRevision subject)))
      , ("concrete_kind", SemanticAtom (concreteKind concrete))
      , ("concrete_stage", SemanticAtom (concreteRevision concrete))
      , ("next_stage", SemanticAtom
          (unNextStageRequirementStageRevision
            (nextStageRequirementStageRevision (stageClosureNextStage bundle))))
      ])))
  where
    concrete = stageClosureConcrete bundle
    subject = concreteSubjectStage concrete
    common = subjectStageBase subject

makeStageClosureBundle
  :: ConcreteStageClosure
  -> NextStageRequirementStageBundle
  -> StageClosureBundle
makeStageClosureBundle concrete nextStage = provisional
  { stageClosureContractRevision =
      deriveClosedStageContractRevision provisional
  }
  where
    common = subjectStageBase (concreteSubjectStage concrete)
    systemsRevision = deriveSystemsArtifactRevision
      (phase1StageSystemsArtifact common)
    provisional = StageClosureBundle
      { stageClosureConcrete = concrete
      , stageClosureNextStage = nextStage
      , stageClosureSystemsArtifactRevision = systemsRevision
      , stageClosureContractRevision = ClosedStageContractRevision "pending"
      }

verifyStageClosureBundle
  :: StageClosureBundle
  -> Either StageClosureVerificationError ()
verifyStageClosureBundle bundle = do
  verifyConcrete (stageClosureConcrete bundle)
  mapLeft StageClosureNextStageError $
    verifyNextStageRequirementStageBundle (stageClosureNextStage bundle)
  verifyRealizationKernel

  let concreteSubject = concreteSubjectStage (stageClosureConcrete bundle)
      nextSubject = nextStageSubjectStage (stageClosureNextStage bundle)
      concreteCommon = subjectStageBase concreteSubject
      nextCommon = subjectStageBase nextSubject
      sourceDecision = ClosureKernel.decideSourceClosureByFacts
        (phase1StageSourceFacts concreteCommon
          == Map.keysSet (phase1StageFactDispositions concreteCommon))
        True
        True
      targetDecision = ClosureKernel.decideTargetClosureByFacts
        (phase1StageSystemsMechanisms concreteCommon
          == Map.keysSet (phase1StageSystemsJustifications concreteCommon))
        True
        True

  case sourceDecision of
    ClosureKernel.SourceClosureAcceptedDecision -> Right ()
    _ -> kernelInvariant "source-closure-after-native-verification"
  case targetDecision of
    ClosureKernel.TargetClosureAcceptedDecision -> Right ()
    _ -> kernelInvariant "target-closure-after-native-verification"

  let concreteSubjectRevision = subjectStageRevision concreteSubject
      nextSubjectRevision = subjectStageRevision nextSubject
      concreteInstanceRevision = phase1StageInstanceRevision concreteCommon
      nextInstanceRevision = phase1StageInstanceRevision nextCommon
      concreteRealizationRevision = phase1StageRealizationRevision concreteCommon
      nextRealizationRevision = phase1StageRealizationRevision nextCommon
      concreteSystemsRevision = phase1StageSystemsArtifactRevision concreteCommon
      nextSystemsRevision = phase1StageSystemsArtifactRevision nextCommon
      concreteContractRevision = phase1StageContractRevision concreteCommon
      nextContractRevision = phase1StageContractRevision nextCommon
      concreteProfile = phase1StageVerifierProfileRevision concreteCommon
      nextProfile = phase1StageVerifierProfileRevision nextCommon
      expectedSystems = deriveSystemsArtifactRevision
        (phase1StageSystemsArtifact concreteCommon)
      storedSystems = stageClosureSystemsArtifactRevision bundle
      expectedFinal = deriveClosedStageContractRevision bundle
      storedFinal = stageClosureContractRevision bundle
      identityDecision = ClosureKernel.decideStageIdentityByFacts
        (concreteSubjectRevision == nextSubjectRevision)
        (concreteInstanceRevision == nextInstanceRevision)
        (concreteRealizationRevision == nextRealizationRevision)
        (concreteSystemsRevision == nextSystemsRevision)
        (concreteContractRevision == nextContractRevision)
        (concreteProfile == nextProfile)
        (expectedSystems == storedSystems)
        (expectedFinal == storedFinal)
        (not (Text.null (unSystemsArtifactRevision storedSystems)))
        (not (Text.null (unClosedStageContractRevision storedFinal)))

  case identityDecision of
    ClosureKernel.StageIdentityAcceptedDecision -> Right ()
    ClosureKernel.StageIdentitySubjectDecision ->
      Left (StageClosureSubjectRevisionMismatch
        concreteSubjectRevision nextSubjectRevision)
    ClosureKernel.StageIdentityInstanceDecision ->
      Left (StageClosureInstanceRevisionMismatch
        concreteInstanceRevision nextInstanceRevision)
    ClosureKernel.StageIdentityRealizationDecision ->
      Left (StageClosureRealizationRevisionMismatch
        concreteRealizationRevision nextRealizationRevision)
    ClosureKernel.StageIdentitySystemsDecision ->
      Left (StageClosureSystemsRevisionMismatch
        concreteSystemsRevision nextSystemsRevision)
    ClosureKernel.StageIdentityContractDecision ->
      Left (StageClosurePhase1ContractRevisionMismatch
        concreteContractRevision nextContractRevision)
    ClosureKernel.StageIdentityProfileDecision ->
      Left (StageClosureVerifierProfileMismatch concreteProfile nextProfile)
    ClosureKernel.StageIdentityRecomputedSystemsDecision ->
      Left (StageClosureStoredSystemsRevisionMismatch expectedSystems storedSystems)
    ClosureKernel.StageIdentityRecomputedFinalDecision ->
      Left (StageClosureContractRevisionMismatch expectedFinal storedFinal)
    ClosureKernel.StageIdentityStoredSystemsDecision ->
      kernelInvariant "stored-systems-presence"
    ClosureKernel.StageIdentityStoredFinalDecision ->
      kernelInvariant "stored-final-presence"

  case ClosureKernel.decideSystemsStageClosureByFacts
      True True
      (sourceAccepted sourceDecision)
      (targetAccepted targetDecision)
      True
      (identityAccepted identityDecision) of
    ClosureKernel.SystemsStageClosureAcceptedDecision -> Right ()
    _ -> kernelInvariant "cumulative-stage-closure"

verifyRealizationKernel :: Either StageClosureVerificationError ()
verifyRealizationKernel =
  case RealizeKernel.decideTargetStrengtheningByFacts
      True True True True True True True True True of
    RealizeKernel.TargetStrengtheningAcceptedDecision ->
      case RealizeKernel.decideStagingEffectByFacts
          True True True True True True True True True of
        RealizeKernel.StagingEffectAcceptedDecision ->
          case RealizeKernel.decideNextStageExportByFacts
              True True True True True True True of
            RealizeKernel.NextStageExportAcceptedDecision ->
              case RealizeKernel.decideSystemsRealizationEffectsByFacts
                  True True True True of
                RealizeKernel.SystemsRealizationEffectsAcceptedDecision -> Right ()
                _ -> kernelInvariant "realization-effects-cumulative"
            _ -> kernelInvariant "realization-effects-next-stage"
        _ -> kernelInvariant "realization-effects-staging"
    _ -> kernelInvariant "realization-effects-strengthening"

verifyConcrete
  :: ConcreteStageClosure
  -> Either StageClosureVerificationError ()
verifyConcrete concrete = case concrete of
  ConcreteThroughBranch bundle ->
    mapLeft StageClosureBranchError (verifyBranchResourceStageBundle bundle)
  ConcreteThroughBoundary bundle ->
    mapLeft StageClosureBoundaryError (verifyBoundaryCommitStageBundle bundle)

sourceAccepted :: ClosureKernel.SourceClosureDecision -> Bool
sourceAccepted decision = case decision of
  ClosureKernel.SourceClosureAcceptedDecision -> True
  _ -> False

targetAccepted :: ClosureKernel.TargetClosureDecision -> Bool
targetAccepted decision = case decision of
  ClosureKernel.TargetClosureAcceptedDecision -> True
  _ -> False

identityAccepted :: ClosureKernel.StageIdentityDecision -> Bool
identityAccepted decision = case decision of
  ClosureKernel.StageIdentityAcceptedDecision -> True
  _ -> False

concreteKind :: ConcreteStageClosure -> Text
concreteKind concrete = case concrete of
  ConcreteThroughBranch _ -> "through-branch-resource"
  ConcreteThroughBoundary _ -> "through-boundary-commit"

concreteRevision :: ConcreteStageClosure -> Text
concreteRevision concrete = case concrete of
  ConcreteThroughBranch bundle ->
    unBranchResourceStageRevision (branchResourceStageRevision bundle)
  ConcreteThroughBoundary bundle ->
    unBoundaryCommitStageRevision (boundaryCommitStageRevision bundle)

instanceText :: InstanceRevision -> Text
instanceText (InstanceRevision value) = value

realizationText :: RealizationRevision -> Text
realizationText (RealizationRevision value) = value

phase1RevisionText :: Phase1StageContractRevision -> Text
phase1RevisionText (Phase1StageContractRevision value) = value

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right

kernelInvariant :: String -> a
kernelInvariant label =
  error ("certified Systems kernel mismatch: " <> label)
