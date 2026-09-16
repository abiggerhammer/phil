{-# LANGUAGE OverloadedStrings #-}

module Phil.Compiler.RuntimeChoiceSystems
  ( RuntimeChoiceSystemsError (..)
  , bindRuntimeChoicePayloadPlan
  ) where

import Control.Monad (foldM)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance.Types (Digest (..))
import Phil.Compiler.RuntimeChoicePayload
import Phil.Systems.GenericLowering (CoreSystemsProgram)
import Phil.Systems.IR
import Phil.Systems.Phase1Stage

-- | Fail-closed errors while carrying a certified checked-Core runtime-choice
-- payload plan into the Phase-1 Systems representation.
data RuntimeChoiceSystemsError
  = RuntimeChoiceSystemsBaseStageRejected Phase1StageVerificationError
  | RuntimeChoiceSystemsPlanRejected RuntimeChoicePayloadError
  | RuntimeChoiceSystemsPlanCoreMismatch
  | RuntimeChoiceSystemsFunctionMissing RuntimeChoiceSite
  | RuntimeChoiceSystemsBlockMissing RuntimeChoiceSite
  | RuntimeChoiceSystemsNotRuntimeChoice RuntimeChoiceSite
  | RuntimeChoiceSystemsArmDomainMismatch RuntimeChoiceSite (Set.Set Text) (Set.Set Text)
  | RuntimeChoiceSystemsTargetMismatch RuntimeChoiceSite Text BlockId BlockId
  | RuntimeChoiceSystemsPayloadValueMissing RuntimeChoiceSite Text ValueId
  | RuntimeChoiceSystemsExistingPayloadMismatch RuntimeChoiceSite Text (Maybe ValueId) (Maybe ValueId)
  | RuntimeChoiceSystemsDecisionCollision DecisionId
  | RuntimeChoiceSystemsFinalStageRejected Phase1StageVerificationError
  deriving (Eq, Show)

-- | Bind a previously certified runtime-choice payload plan into an already
-- verified Phase-1 stage. The plan is re-certified against the exact checked
-- Core program, then every affected Systems arm is checked for exact domain and
-- successor agreement before its payload identity is installed.
--
-- The resulting Systems artifact is fully resealed: target digest, every
-- lowering-decision target digest, lowering-ledger root, Systems revision, and
-- Phase-1 stage revision are all recomputed. Existing fact dispositions and
-- mechanism justifications are retained because payload binding changes the
-- data carried by a runtime-choice edge, not the mechanism domain itself.
bindRuntimeChoicePayloadPlan
  :: CoreSystemsProgram
  -> RuntimeChoicePayloadPlan
  -> Phase1StageBundle
  -> Either RuntimeChoiceSystemsError Phase1StageBundle
bindRuntimeChoicePayloadPlan core plan base = do
  mapLeft RuntimeChoiceSystemsBaseStageRejected (verifyPhase1StageBundle base)
  recertified <- mapLeft RuntimeChoiceSystemsPlanRejected $
    certifyRuntimeChoicePayloadPlan core
      (Map.elems (runtimeChoicePayloadPlanSpecs plan))
  if recertified == plan
    then Right ()
    else Left RuntimeChoiceSystemsPlanCoreMismatch
  program <- foldM bindSpec
    (systemsArtifactProgram baseArtifact)
    (Map.elems (runtimeChoicePayloadPlanSpecs plan))
  let targetDigest = systemsProgramDigest program
      baseContract = systemsArtifactStageContract baseArtifact
      contract = baseContract { stageTargetArtifactDigest = targetDigest }
      rebound = Map.map (rebindDecision targetDigest)
        (loweringLedgerDecisions (systemsArtifactLoweringLedger baseArtifact))
      decision = payloadDecision plan sourceDigest targetDigest
      decisionId = loweringDecisionId decision
  if Map.member decisionId rebound
    then Left (RuntimeChoiceSystemsDecisionCollision decisionId)
    else Right ()
  let decisions = Map.insert decisionId decision rebound
      loweringRoot = deriveLoweringLedgerRoot decisions
      artifact = SystemsArtifact
        { systemsArtifactProgram = program
        , systemsArtifactStageContract = contract
        , systemsArtifactLoweringLedger = LoweringLedger decisions loweringRoot
        }
      bundle = makePhase1StageBundle
        (phase1StageInstanceRevision base)
        (phase1StageRealizationRevision base)
        (phase1StageVerifierProfileRevision base)
        artifact
        (phase1StageFactDispositions base)
        (phase1StageSystemsJustifications base)
  mapLeft RuntimeChoiceSystemsFinalStageRejected (verifyPhase1StageBundle bundle)
  pure bundle
  where
    baseArtifact = phase1StageSystemsArtifact base
    sourceDigest = stageSourceArtifactDigest (systemsArtifactStageContract baseArtifact)

bindSpec
  :: SystemsProgram
  -> RuntimeChoicePayloadSpec
  -> Either RuntimeChoiceSystemsError SystemsProgram
bindSpec program spec = do
  function <- maybe
    (Left (RuntimeChoiceSystemsFunctionMissing site))
    Right
    (Map.lookup functionName (systemsProgramFunctions program))
  blockValue <- maybe
    (Left (RuntimeChoiceSystemsBlockMissing site))
    Right
    (Map.lookup blockId (systemsFunctionBlocks function))
  arms <- case systemsBlockTerminator blockValue of
    TermRuntimeChoice name inputs runtimeSite existingArms -> do
      boundArms <- bindArms function existingArms spec
      pure (TermRuntimeChoice name inputs runtimeSite boundArms)
    _ -> Left (RuntimeChoiceSystemsNotRuntimeChoice site)
  let blockValue' = blockValue { systemsBlockTerminator = arms }
      function' = function
        { systemsFunctionBlocks = Map.insert blockId blockValue'
            (systemsFunctionBlocks function)
        }
  pure program
    { systemsProgramFunctions = Map.insert functionName function'
        (systemsProgramFunctions program)
    }
  where
    site = runtimeChoicePayloadSite spec
    functionName = runtimeChoiceSiteFunction site
    blockId = BlockId (runtimeChoiceSiteBlock site)

bindArms
  :: SystemsFunction
  -> Map.Map Text SystemsRuntimeChoiceArm
  -> RuntimeChoicePayloadSpec
  -> Either RuntimeChoiceSystemsError (Map.Map Text SystemsRuntimeChoiceArm)
bindArms function existingArms spec = do
  let site = runtimeChoicePayloadSite spec
      plannedArms = runtimeChoicePayloadArms spec
      expectedDomain = Map.keysSet existingArms
      actualDomain = Map.keysSet plannedArms
  if expectedDomain == actualDomain
    then Right ()
    else Left (RuntimeChoiceSystemsArmDomainMismatch site expectedDomain actualDomain)
  Map.traverseWithKey (bindArm site) plannedArms
  where
    bindArm site label planned = do
      let existing = existingArms Map.! label
          expectedTarget = runtimeChoiceArmTarget existing
          actualTarget = BlockId (runtimeChoicePayloadTarget planned)
          plannedPayload = ValueId <$> runtimeChoicePayloadValue planned
          existingPayload = runtimeChoiceArmPayloadBinding existing
      if expectedTarget == actualTarget
        then Right ()
        else Left (RuntimeChoiceSystemsTargetMismatch
          site label expectedTarget actualTarget)
      case plannedPayload of
        Nothing -> Right ()
        Just valueId
          | Map.member valueId (systemsFunctionValues function) -> Right ()
          | otherwise -> Left (RuntimeChoiceSystemsPayloadValueMissing site label valueId)
      case existingPayload of
        Nothing -> Right ()
        Just _
          | existingPayload == plannedPayload -> Right ()
          | otherwise -> Left (RuntimeChoiceSystemsExistingPayloadMismatch
              site label existingPayload plannedPayload)
      pure SystemsRuntimeChoiceArm
        { runtimeChoiceArmPayloadBinding = plannedPayload
        , runtimeChoiceArmTarget = actualTarget
        }

rebindDecision :: Digest -> LoweringDecision -> LoweringDecision
rebindDecision targetDigest decision =
  let rebound = decision { loweringTargetArtifactDigest = targetDigest }
  in rebound { loweringDecisionDigest = deriveLoweringDecisionDigest rebound }

payloadDecision :: RuntimeChoicePayloadPlan -> Digest -> Digest -> LoweringDecision
payloadDecision plan sourceDigest targetDigest =
  provisional { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
  where
    planDigest = runtimeChoicePayloadPlanDigest plan
    decisionId = DecisionId ("lower.runtime-choice.payload-bindings:" <> unDigest planDigest)
    sites =
      [ runtimeChoiceSiteFunction site <> ":" <> runtimeChoiceSiteBlock site
      | site <- Map.keys (runtimeChoicePayloadPlanSpecs plan)
      ]
    provisional = LoweringDecision
      { loweringDecisionId = decisionId
      , loweringDecisionDigest = Digest ""
      , loweringSourceArtifactDigest = sourceDigest
      , loweringTargetArtifactDigest = targetDigest
      , loweringSourceRepresentation = "certified checked-Core runtime-choice payload plan"
      , loweringTargetRepresentation = "SystemsRuntimeChoiceArm payload bindings"
      , loweringSemanticEntities = sites
      , loweringObligationRevisions = []
      , loweringAssuranceEntries = []
      , loweringAssuranceUses = []
      , loweringAction = Retain
      , loweringRepresentationBefore = "runtime-choice arm and successor identity without retained payload"
      , loweringRepresentationAfter = "runtime-choice arm, successor, and exact retained payload value identity"
      , loweringInvariantsPreserved =
          [ "runtime-choice arm domain unchanged"
          , "runtime-choice successor targets unchanged"
          , "payload values are declared in the owning Systems function"
          ]
      , loweringInvariantsTransferred = []
      , loweringRuntimeResidue = ["runtime-choice payload transfer"]
      , loweringCostClass = Just SemanticRequired
      , loweringCostShape = emptyCostShape
          { costFrequency = Just "per payload-bearing runtime-choice result" }
      , loweringTargetPreconditions = []
      , loweringAssumptions = []
      , loweringDerivedObligations = []
      , loweringInspectionPlan =
          [ "compare checked-Core payload-plan arm domain with Systems arm domain"
          , "compare exact successor targets"
          , "check retained payload identities against Systems value domain"
          ]
      }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
