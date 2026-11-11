-- | P6: construct the selected whole StageClosure from one opaque,
-- independently rechecked ordinary-source/Core Systems production event.
-- The structural template is extension configuration, not source authority;
-- every cumulative stage is reminted from the produced base.
module Phil.Verification.VerifiedStageClosureProduction
  ( VerifiedStageClosureProduction
  , VerifiedStageClosureProductionError (..)
  , produceVerifiedStageClosure
  , verifiedStageClosureSourceProduction
  , verifiedStageClosureSelected
  ) where

import qualified Phil.Compiler.SourceSystems as Source
import qualified Phil.Systems.AssumptionDependency as Assumption
import qualified Phil.Systems.AuthorityEffectCorrespondence as Authority
import qualified Phil.Systems.BoundaryCommitCorrespondence as Boundary
import qualified Phil.Systems.BranchResourceFailure as Branch
import qualified Phil.Systems.ControlStateProjection as Control
import qualified Phil.Systems.CostAttribution as Cost
import qualified Phil.Systems.EvidenceErasure as Erasure
import qualified Phil.Systems.EvidenceSubjectTransfer as Transfer
import qualified Phil.Systems.NextStageRequirement as Next
import qualified Phil.Systems.ProtocolStateCorrespondence as Protocol
import qualified Phil.Systems.ProviderCallCorrespondence as Provider
import qualified Phil.Systems.RuntimeClaimBinding as Claim
import qualified Phil.Systems.RuntimePrimitiveReuse as Primitive
import qualified Phil.Systems.StageClosure as Closure
import qualified Phil.Systems.StagingEffect as Staging
import qualified Phil.Systems.SubjectCorrespondence as Subject
import qualified Phil.Systems.TargetStrengthening as Target

-- Private constructor: callers cannot substitute independently assembled
-- StageClosure or arbitrary K/I records for source-owned production.
data VerifiedStageClosureProduction = VerifiedStageClosureProduction
  Source.VerifiedSourceSystemsProduction
  Closure.StageClosureBundle
  deriving (Eq, Show)

data VerifiedStageClosureProductionError
  = VerifiedStageTemplateRejected Closure.StageClosureVerificationError
  | VerifiedStageProviderRejected Authority.AuthorityEffectStageVerificationError
  | VerifiedStageCostRejected String
  | VerifiedStageNextRejected String
  | VerifiedStageResultRejected Closure.StageClosureVerificationError
  | VerifiedStageProducedBaseDrift
  deriving (Eq, Show)

-- | Old template's base, revisions and opaque provider authority are NEVER
-- reused. Rebuild and verify the whole selected closure from the sealed
-- ordinary-source lowering stage, including BOTH concrete and next-stage arms.
-- Independent provider expectations are checked before re-minting authority.
-- A separately accepted final release is NOT bound here (P7).
produceVerifiedStageClosure
  :: Source.VerifiedSourceSystemsProduction
  -> Provider.ProviderCallExpectationMap
  -> Closure.StageClosureBundle
  -> Either VerifiedStageClosureProductionError VerifiedStageClosureProduction
produceVerifiedStageClosure production expectations template = do
  mapLeft VerifiedStageTemplateRejected
    (Closure.verifyStageClosureBundle template)

  let originalConcrete = Closure.stageClosureConcrete template
      originalSubject = Closure.concreteSubjectStage originalConcrete
      sourceStage = Source.verifiedSourceSystemsStage production
      subject = Subject.makeSubjectStageBundle sourceStage
        (Subject.subjectStageCorrespondences originalSubject)

      originalBranch = case originalConcrete of
        Closure.ConcreteThroughBranch branch -> branch
        Closure.ConcreteThroughBoundary boundary ->
          Control.controlStateStageBase
            (Protocol.protocolStateStageBase
              (Boundary.boundaryCommitStageBase boundary))
      originalAuthority = Branch.branchResourceStageBase originalBranch
      originalProvider = Authority.authorityEffectStageBase originalAuthority
      provider = Provider.makeProviderCallStageBundle subject
        (Provider.providerCallStageSelections originalProvider)
        (Provider.providerCallStageCallSites originalProvider)
        (Provider.providerCallStageLinks originalProvider)
      authority = Authority.makeAuthorityEffectStageBundle provider
        (Authority.authorityEffectStageSurfaces originalAuthority)
        (Authority.authorityEffectStageUses originalAuthority)

  providerAuthority <- mapLeft VerifiedStageProviderRejected
    (Branch.certifyProviderCallClosureAuthority expectations authority)
  let branch = Branch.makeBranchResourceStageBundle
        providerAuthority authority (Branch.branchResourceStageSites originalBranch)
      concrete = case originalConcrete of
        Closure.ConcreteThroughBranch _ -> Closure.ConcreteThroughBranch branch
        Closure.ConcreteThroughBoundary originalBoundary ->
          let oldProtocol = Boundary.boundaryCommitStageBase originalBoundary
              oldControl = Protocol.protocolStateStageBase oldProtocol
              control = Control.makeControlStateStageBundle branch
                (Control.controlStateStageBoundaries oldControl)
                (Control.controlStateStageProjections oldControl)
                (Control.controlStateStageClosureCaptures oldControl)
              protocol = Protocol.makeProtocolStateStageBundle control
                (Protocol.protocolStateStageEndpoints oldProtocol)
                (Protocol.protocolStateStageTransitions oldProtocol)
          in Closure.ConcreteThroughBoundary
               (Boundary.makeBoundaryCommitStageBundle protocol
                 (Boundary.boundaryCommitStageTransfers originalBoundary))

      oldNext = Closure.stageClosureNextStage template
      oldCost = Next.nextStageRequirementStageBase oldNext
      oldStaging = Cost.costAttributionStageBase oldCost
      oldPrimitive = Staging.stagingEffectStageBase oldStaging
      oldClaim = Primitive.runtimePrimitiveStageBase oldPrimitive
      oldTarget = Claim.runtimeClaimStageBase oldClaim
      oldAssumption = Target.targetStrengtheningStageBase oldTarget
      oldErasure = Assumption.assumptionDependencyStageBase oldAssumption
      oldTransfer = Erasure.evidenceErasureStageBase oldErasure

      transfer = Transfer.makeEvidenceTransferStageBundle subject
        (Transfer.evidenceTransferStageRelations oldTransfer)
        (Transfer.evidenceTransferStageRebindings oldTransfer)
      erasure = Erasure.makeEvidenceErasureStageBundle transfer
        (Erasure.evidenceErasureStageJustifications oldErasure)
        (Erasure.evidenceErasureStageLaterConsumers oldErasure)
      assumption = Assumption.makeAssumptionDependencyStageBundle erasure
        (Assumption.assumptionDependencyStageAssumptions oldAssumption)
        (Assumption.assumptionDependencyStageForward oldAssumption)
        (Assumption.assumptionDependencyStageReverse oldAssumption)
      target = Target.makeTargetStrengtheningStageBundle assumption
        (Target.targetStrengtheningStageFacts oldTarget)
        (Target.targetStrengtheningStageDerivedObligations oldTarget)
      claims = Claim.completeRuntimeClaimStageBundle target
        (Claim.runtimeClaimStageClaims oldClaim)
        (Claim.runtimeClaimStageBindings oldClaim)
      primitive = Primitive.completeRuntimePrimitiveStageBundle claims
      staging = Staging.makeStagingEffectStageBundle primitive
        (Staging.stagingEffectStageRequirements oldStaging)
        (Staging.stagingEffectStageEvents oldStaging)

  cost <- mapLeft VerifiedStageCostRejected
    (Cost.completeCostAttributionStageBundle staging
      (Cost.costAttributionStageRuntimeBases oldCost))
  next <- mapLeft VerifiedStageNextRejected
    (Next.completeNextStageRequirementStageBundle cost)
  let selected = Closure.makeStageClosureBundle concrete next
      concreteSource =
        Subject.subjectStageBase (Closure.concreteSubjectStage concrete)
      nextSource =
        Subject.subjectStageBase (Closure.nextStageSubjectStage next)
  -- Complete base equality, not a revision or K/I comparison.
  if concreteSource == sourceStage && nextSource == sourceStage
    then Right ()
    else Left VerifiedStageProducedBaseDrift
  mapLeft VerifiedStageResultRejected
    (Closure.verifyStageClosureBundle selected)
  Right (VerifiedStageClosureProduction production selected)

verifiedStageClosureSourceProduction
  :: VerifiedStageClosureProduction -> Source.VerifiedSourceSystemsProduction
verifiedStageClosureSourceProduction (VerifiedStageClosureProduction source _) = source

verifiedStageClosureSelected
  :: VerifiedStageClosureProduction -> Closure.StageClosureBundle
verifiedStageClosureSelected (VerifiedStageClosureProduction _ selected) = selected

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
