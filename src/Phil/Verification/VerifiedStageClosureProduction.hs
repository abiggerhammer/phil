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
  , verifiedStageClosureSourceCheckEventGraph
  , AcceptedCheckedStaticUse
  , CheckedStaticUseAcceptanceError (..)
  , acceptSelectedCheckedStaticUse
  ) where

import qualified Phil.Compiler.SourceSystems as Source
import Phil.Compiler.SourceBundle (CheckedSourceEvidenceOccurrence (..))
import Phil.Core.Static (ArchitectureInstanceIdentity)
import Phil.Core.Focusing (FocusedRequirement (..), FocusMechanism (..))
import Phil.Assurance.Types
  ( AssuranceLedger (..), AssuranceManifest (..), AssuranceUse (..)
  , AssuranceUseId, StaticCheckedSourceFact (..), StaticCheckedUseKind (..)
  , VerificationContext )
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import qualified Phil.Surface.Check.Types as Checker
import qualified Phil.Verification.SourceManifestBinding as Binding
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
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

-- | The exact same private P2 source event graph retained through both P6
-- StageClosure arms (whose full source bases are checked for equality).
-- Neither arm claims P7 final evidence use on the strength of this projection.
verifiedStageClosureSourceCheckEventGraph
  :: VerifiedStageClosureProduction -> Source.VerifiedSourceCheckEventGraph
verifiedStageClosureSourceCheckEventGraph
  (VerifiedStageClosureProduction production _) =
    Source.verifiedSourceSystemsCheckEventGraph production

verifiedStageClosureSelected
  :: VerifiedStageClosureProduction -> Closure.StageClosureBundle
verifiedStageClosureSelected (VerifiedStageClosureProduction _ selected) = selected

-- | Opaque checked-source and independently selected immutable use contract.
-- In particular this is NOT P7 final-use authority, nor proof that a dynamic
-- runtime alternative executed; those remain separate non-bypassable gates.
data AcceptedCheckedStaticUse = AcceptedCheckedStaticUse
  VerifiedStageClosureProduction
  Binding.CertifiedSourceManifestBinding
  AssuranceUseId
  StaticCheckedSourceFact
  deriving (Eq, Show)

data CheckedStaticUseAcceptanceError
  = StaticUseSourceInstanceMismatch
  | StaticUseSelectedManifestRejected ManifestError
  | StaticUseNotSelected AssuranceUseId
  | StaticUseNotInLedger AssuranceUseId
  | StaticUseIncorrectKind AssuranceUseId
  | StaticUseNotObservedByOriginalChecker AssuranceUseId
  deriving (Eq, Show)

acceptSelectedCheckedStaticUse
  :: VerifiedStageClosureProduction
  -> Binding.CertifiedSourceManifestBinding
  -> VerificationContext
  -> AssuranceLedger
  -> AssuranceUseId
  -> Either CheckedStaticUseAcceptanceError AcceptedCheckedStaticUse
acceptSelectedCheckedStaticUse stage binding context ledger useId = do
  let production = verifiedStageClosureSourceProduction stage
      descriptor = Source.verifiedSourceSystemsArchitectureDescriptor production
      graph = verifiedStageClosureSourceCheckEventGraph stage
      manifest = Binding.sourceManifestBindingManifest binding
  if Binding.sourceManifestBindingArchitectureDescriptor binding == Just descriptor
    then Right ()
    else Left StaticUseSourceInstanceMismatch
  mapLeft StaticUseSelectedManifestRejected (verifyManifest context ledger manifest)
  if Set.member useId (manifestAssuranceUses manifest)
    then Right ()
    else Left (StaticUseNotSelected useId)
  selected <- maybe (Left (StaticUseNotInLedger useId)) Right
    (Map.lookup useId (ledgerUses ledger))
  fact <- case selected of
    CheckedStaticUse _ _ _ _ actual -> Right actual
    _ -> Left (StaticUseIncorrectKind useId)
  let checkedFacts =
        [ actual
        | occurrence <- Source.verifiedSourceCheckEventOccurrences graph
        , Just actual <- [checkerStaticFact
            (Source.verifiedSourceCheckEventArchitectureIdentity graph)
            occurrence]
        ]
  if fact `elem` checkedFacts
    then Right (AcceptedCheckedStaticUse stage binding useId fact)
    else Left (StaticUseNotObservedByOriginalChecker useId)

-- | A fact is produced only by a named proof or requirement *actually checked*
-- at its original site. A definition proof (including 'prove true'), an
-- uncertified decision, and provider outcomes cannot mint a static use.
checkerStaticFact
  :: ArchitectureInstanceIdentity
  -> CheckedSourceEvidenceOccurrence
  -> Maybe StaticCheckedSourceFact
checkerStaticFact architecture occurrence =
  case Checker.sourceEvidenceUse event of
    Checker.SourceRequirementEvidence proposition (Just binder) Nothing ->
      Just (makeFact proposition proposition
        (StaticRequirementByBinding binder))
    Checker.SourceProveEvidence requirement False ->
      case focusedMechanism requirement of
        FocusByEvidence binder ->
          Just (makeFact (focusedOriginal requirement)
            (focusedCanonical requirement) (StaticProofByBinding binder))
        _ -> Nothing
    _ -> Nothing
  where
    event = checkedEvidenceEvent occurrence
    makeFact original canonical kind = StaticCheckedSourceFact
      { staticUseSourceUnit = checkedEvidenceUnitId occurrence
      , staticUseDeclarationSite = checkedEvidenceDeclarationSite occurrence
      , staticUseDeclarationKey = checkedEvidenceDeclarationKey occurrence
      , staticUseArchitecture = architecture
      , staticUseSite = Checker.sourceEvidenceSite event
      , staticUseBranches = Checker.sourceEvidenceBranchRoute event
      , staticUseOrdinal = Checker.sourceEvidenceOrdinal event
      , staticUseOriginalProposition = original
      , staticUseCanonicalProposition = canonical
      , staticUseKind = kind
      }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
