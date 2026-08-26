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

newtype ClosedStageContractRevision = ClosedStageContractRevision
  { unClosedStageContractRevision :: Text
  }
  deriving (Eq, Ord, Show)

-- | The relation-specific SYS-004..010 trunk has different applicable terminal
-- layers for the two current witnesses.  Upload reaches boundary correspondence;
-- Steve currently stops at branch/resource correspondence because protocol and
-- boundary relations are not applicable to its provider-local CAS operations.
data ConcreteStageClosure
  = ConcreteThroughBranch BranchResourceStageBundle
  | ConcreteThroughBoundary BoundaryCommitStageBundle
  deriving (Eq, Show)

-- | SYS-020 joins the two StageContract trunks that have grown from the common
-- SubjectStage: the concrete source/target correspondence trunk and the
-- evidence/realization/runtime/cost/next-stage trunk.  The stored revisions are
-- recomputable consequences, not generative IDs.
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

  let concreteSubject = concreteSubjectStage (stageClosureConcrete bundle)
      nextSubject = nextStageSubjectStage (stageClosureNextStage bundle)
      concreteCommon = subjectStageBase concreteSubject
      nextCommon = subjectStageBase nextSubject

  requireEqual StageClosureSubjectRevisionMismatch
    (subjectStageRevision concreteSubject)
    (subjectStageRevision nextSubject)
  requireEqual StageClosureInstanceRevisionMismatch
    (phase1StageInstanceRevision concreteCommon)
    (phase1StageInstanceRevision nextCommon)
  requireEqual StageClosureRealizationRevisionMismatch
    (phase1StageRealizationRevision concreteCommon)
    (phase1StageRealizationRevision nextCommon)
  requireEqual StageClosureSystemsRevisionMismatch
    (phase1StageSystemsArtifactRevision concreteCommon)
    (phase1StageSystemsArtifactRevision nextCommon)
  requireEqual StageClosurePhase1ContractRevisionMismatch
    (phase1StageContractRevision concreteCommon)
    (phase1StageContractRevision nextCommon)
  requireEqual StageClosureVerifierProfileMismatch
    (phase1StageVerifierProfileRevision concreteCommon)
    (phase1StageVerifierProfileRevision nextCommon)

  let expectedSystems = deriveSystemsArtifactRevision
        (phase1StageSystemsArtifact concreteCommon)
  requireEqual StageClosureStoredSystemsRevisionMismatch
    expectedSystems (stageClosureSystemsArtifactRevision bundle)
  requireEqual StageClosureContractRevisionMismatch
    (deriveClosedStageContractRevision bundle)
    (stageClosureContractRevision bundle)

verifyConcrete
  :: ConcreteStageClosure
  -> Either StageClosureVerificationError ()
verifyConcrete concrete = case concrete of
  ConcreteThroughBranch bundle ->
    mapLeft StageClosureBranchError (verifyBranchResourceStageBundle bundle)
  ConcreteThroughBoundary bundle ->
    mapLeft StageClosureBoundaryError (verifyBoundaryCommitStageBundle bundle)

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

requireEqual :: Eq a => (a -> a -> e) -> a -> a -> Either e ()
requireEqual mkError expected actual
  | expected == actual = Right ()
  | otherwise = Left (mkError expected actual)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
