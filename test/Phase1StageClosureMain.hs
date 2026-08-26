{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Examples.Phase1.StageClosureWitnesses
import Phil.Systems.BranchResourceFailure
  ( BranchResourceStageBundle (..)
  , BranchResourceStageRevision (..)
  )
import Phil.Systems.IR
import Phil.Systems.NextStageRequirement
import Phil.Systems.Phase1Stage
import Phil.Systems.StageClosure
import Phil.Systems.SubjectCorrespondence
  ( SubjectStageBundle (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ t "SYS-020 upload final StageContract closure is accepted" uploadAccepted
    , t "SYS-020 Steve final StageContract closure is accepted" steveAccepted
    , t "SYS-020 upload concrete and next-stage trunks share one subject stage" uploadTrunksAgree
    , t "SYS-020 Steve concrete and next-stage trunks share one subject stage" steveTrunksAgree
    , t "SYS-020 final Systems revision is recomputed from the common artifact" uploadSystemsRecomputed
    , t "SYS-020 semantically unordered StageContract lists do not change Systems revision" unorderedStageListsStable
    , t "SYS-020 lowering enumeration order does not change Systems revision" loweringListOrderStable
    , t "SYS-020 lowering inspection prose does not change Systems revision" inspectionPlanStable
    , t "SYS-020 diagnostic names do not change Systems revision" diagnosticSystemsStable
    , t "SYS-020 diagnostic names do not change coarse StageContract revision" diagnosticStageStable
    , t "SYS-020 semantic trace changes do change Systems revision" semanticTraceChangesSystems
    , t "SYS-020 semantic trace changes do change coarse StageContract revision" semanticTraceChangesStage
    , t "SYS-020 next-stage map reconstruction preserves final closure revision" nextStageEnumerationStable
    , t "SYS-020 identity-bearing next-stage requirement changes final closure revision" nextStageSemanticChangeRevises
    , t "SYS-020 identity-bearing concrete-stage revision changes final closure revision" concreteSemanticChangeRevises
    , t "SYS-020 stale stored Systems revision rejects" $ reject staleSystemsRevision
    , t "SYS-020 stale stored StageContract revision rejects" $ reject staleContractRevision
    , t "SYS-020 upload concrete trunk cannot close against Steve next-stage trunk" crossUploadConcreteSteveNextRejects
    , t "SYS-020 Steve concrete trunk cannot close against upload next-stage trunk" crossSteveConcreteUploadNextRejects
    , t "SYS-020 closed revision is deterministic on reconstruction" reconstructionStable
    ]
  if and results then pure () else exitFailure

t :: String -> Either String () -> IO Bool
t label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left e -> putStrLn ("FAIL: " <> label <> " -- " <> e) >> pure False

uploadAccepted, steveAccepted :: Either String ()
uploadAccepted = uploadStageClosureBundle >>=
  mapLeft show . verifyStageClosureBundle
steveAccepted = steveStageClosureBundle >>=
  mapLeft show . verifyStageClosureBundle

uploadTrunksAgree, steveTrunksAgree :: Either String ()
uploadTrunksAgree = uploadStageClosureBundle >>= trunksAgree
steveTrunksAgree = steveStageClosureBundle >>= trunksAgree

trunksAgree :: StageClosureBundle -> Either String ()
trunksAgree bundle =
  assert
    (subjectStageRevision (concreteSubjectStage (stageClosureConcrete bundle))
      == subjectStageRevision (nextStageSubjectStage (stageClosureNextStage bundle)))
    "concrete and next-stage trunks do not share the exact SubjectStage revision"

uploadSystemsRecomputed :: Either String ()
uploadSystemsRecomputed = do
  bundle <- uploadStageClosureBundle
  let common = subjectStageBase (concreteSubjectStage (stageClosureConcrete bundle))
      expected = deriveSystemsArtifactRevision (phase1StageSystemsArtifact common)
  assert (stageClosureSystemsArtifactRevision bundle == expected)
    "stored final Systems revision is not the recomputed common-artifact revision"

unorderedStageListsStable :: Either String ()
unorderedStageListsStable = do
  artifact <- uploadArtifact
  let contract = systemsArtifactStageContract artifact
      changed = artifact
        { systemsArtifactStageContract = contract
            { stageFacts = reverse (stageFacts contract)
            , stageRequiredEdges = reverse (stageRequiredEdges contract)
            , stageDerivedObligations = reverse (stageDerivedObligations contract)
            , stageAssumptions = reverse (stageAssumptions contract)
            , stageTraceRelation = reverse (stageTraceRelation contract)
            , stageResourceFailureRelation = reverse (stageResourceFailureRelation contract)
            }
        }
  assert (deriveSystemsArtifactRevision artifact == deriveSystemsArtifactRevision changed)
    "semantically unordered StageContract list order changed SystemsArtifactRevision"

loweringListOrderStable :: Either String ()
loweringListOrderStable = do
  artifact <- uploadArtifact
  let ledger = systemsArtifactLoweringLedger artifact
      reverseDecision d = d
        { loweringSemanticEntities = reverse (loweringSemanticEntities d)
        , loweringObligationRevisions = reverse (loweringObligationRevisions d)
        , loweringAssuranceEntries = reverse (loweringAssuranceEntries d)
        , loweringAssuranceUses = reverse (loweringAssuranceUses d)
        , loweringInvariantsPreserved = reverse (loweringInvariantsPreserved d)
        , loweringInvariantsTransferred = reverse (loweringInvariantsTransferred d)
        , loweringRuntimeResidue = reverse (loweringRuntimeResidue d)
        , loweringTargetPreconditions = reverse (loweringTargetPreconditions d)
        , loweringAssumptions = reverse (loweringAssumptions d)
        , loweringDerivedObligations = reverse (loweringDerivedObligations d)
        }
      changed = artifact
        { systemsArtifactLoweringLedger = ledger
            { loweringLedgerDecisions = Map.map reverseDecision
                (loweringLedgerDecisions ledger)
            }
        }
  assert (deriveSystemsArtifactRevision artifact == deriveSystemsArtifactRevision changed)
    "set-like lowering list order changed SystemsArtifactRevision"

inspectionPlanStable :: Either String ()
inspectionPlanStable = do
  artifact <- uploadArtifact
  let ledger = systemsArtifactLoweringLedger artifact
      changed = artifact
        { systemsArtifactLoweringLedger = ledger
            { loweringLedgerDecisions = Map.map
                (\d -> d { loweringInspectionPlan =
                    ["temporary path /tmp/sys020", "different diagnostic inspection prose"] })
                (loweringLedgerDecisions ledger)
            }
        }
  assert (deriveSystemsArtifactRevision artifact == deriveSystemsArtifactRevision changed)
    "inspection-only prose changed SystemsArtifactRevision"

diagnosticSystemsStable :: Either String ()
diagnosticSystemsStable = do
  artifact <- uploadArtifact
  let a = insertDiagnostic "diagnostic-name-a" artifact
      b = insertDiagnostic "diagnostic-name-b" artifact
  assert (deriveSystemsArtifactRevision a == deriveSystemsArtifactRevision b)
    "diagnostic display name changed SystemsArtifactRevision"

diagnosticStageStable :: Either String ()
diagnosticStageStable = do
  template <- uploadCommonStage
  let artifact = phase1StageSystemsArtifact template
      a = syntheticStage template (insertDiagnostic "diagnostic-name-a" artifact)
      b = syntheticStage template (insertDiagnostic "diagnostic-name-b" artifact)
  assert (phase1StageContractRevision a == phase1StageContractRevision b)
    "diagnostic display name changed Phase1 StageContractRevision"

semanticTraceChangesSystems :: Either String ()
semanticTraceChangesSystems = do
  artifact <- uploadArtifact
  let a = insertTrace "sys020.semantic-a" artifact
      b = insertTrace "sys020.semantic-b" artifact
  assert (deriveSystemsArtifactRevision a /= deriveSystemsArtifactRevision b)
    "identity-bearing trace change failed to revise SystemsArtifactRevision"

semanticTraceChangesStage :: Either String ()
semanticTraceChangesStage = do
  template <- uploadCommonStage
  let artifact = phase1StageSystemsArtifact template
      a = syntheticStage template (insertTrace "sys020.semantic-a" artifact)
      b = syntheticStage template (insertTrace "sys020.semantic-b" artifact)
  assert (phase1StageContractRevision a /= phase1StageContractRevision b)
    "identity-bearing trace change failed to revise Phase1 StageContractRevision"

nextStageEnumerationStable :: Either String ()
nextStageEnumerationStable = do
  bundle <- uploadStageClosureBundle
  let next = stageClosureNextStage bundle
      rebuiltNext = makeNextStageRequirementStageBundle
        (nextStageRequirementStageBase next)
        (reverseMap (nextStageRequirementStageRequirements next))
      rebuilt = makeStageClosureBundle (stageClosureConcrete bundle) rebuiltNext
  assert (stageClosureContractRevision bundle == stageClosureContractRevision rebuilt)
    "final closure revision changed under next-stage registry reconstruction"

nextStageSemanticChangeRevises :: Either String ()
nextStageSemanticChangeRevises = do
  bundle <- uploadStageClosureBundle
  let next = stageClosureNextStage bundle
  (oldRevision, oldRequirement) <- need "next-stage requirement"
    (Map.lookupMin (nextStageRequirementStageRequirements next))
  let provisional = oldRequirement
        { nextStageRequirementRequiredFactOrContract =
            nextStageRequirementRequiredFactOrContract oldRequirement
              <> " [identity-bearing-change]"
        }
      changedRequirement = provisional
        { nextStageRequirementRevision = deriveNextStageRequirementRevision provisional }
      requirements = Map.insert
        (nextStageRequirementRevision changedRequirement)
        changedRequirement
        (Map.delete oldRevision (nextStageRequirementStageRequirements next))
      changedNext = makeNextStageRequirementStageBundle
        (nextStageRequirementStageBase next) requirements
      changedClosure = makeStageClosureBundle
        (stageClosureConcrete bundle) changedNext
  assert (stageClosureContractRevision bundle /= stageClosureContractRevision changedClosure)
    "identity-bearing next-stage requirement failed to revise final StageContract identity"

concreteSemanticChangeRevises :: Either String ()
concreteSemanticChangeRevises = do
  bundle <- steveStageClosureBundle
  case stageClosureConcrete bundle of
    ConcreteThroughBranch concrete -> do
      let changedConcrete = concrete
            { branchResourceStageRevision =
                BranchResourceStageRevision "sys020.changed.concrete-revision" }
          changedClosure = makeStageClosureBundle
            (ConcreteThroughBranch changedConcrete)
            (stageClosureNextStage bundle)
      assert (stageClosureContractRevision bundle /= stageClosureContractRevision changedClosure)
        "identity-bearing concrete relation revision failed to revise final StageContract identity"
    ConcreteThroughBoundary _ -> Left "Steve unexpectedly closed through boundary correspondence"

reject
  :: (StageClosureBundle -> StageClosureBundle)
  -> Either String ()
reject mutate = do
  bundle <- uploadStageClosureBundle
  case verifyStageClosureBundle (mutate bundle) of
    Left _ -> Right ()
    Right () -> Left "mutation was accepted"

staleSystemsRevision :: StageClosureBundle -> StageClosureBundle
staleSystemsRevision bundle = bundle
  { stageClosureSystemsArtifactRevision = SystemsArtifactRevision "stale.systems.revision" }

staleContractRevision :: StageClosureBundle -> StageClosureBundle
staleContractRevision bundle = bundle
  { stageClosureContractRevision = ClosedStageContractRevision "stale.stage.revision" }

crossUploadConcreteSteveNextRejects :: Either String ()
crossUploadConcreteSteveNextRejects = do
  upload <- uploadStageClosureBundle
  steve <- steveStageClosureBundle
  let mixed = makeStageClosureBundle
        (stageClosureConcrete upload)
        (stageClosureNextStage steve)
  case verifyStageClosureBundle mixed of
    Left _ -> Right ()
    Right () -> Left "upload concrete trunk closed against Steve next-stage trunk"

crossSteveConcreteUploadNextRejects :: Either String ()
crossSteveConcreteUploadNextRejects = do
  upload <- uploadStageClosureBundle
  steve <- steveStageClosureBundle
  let mixed = makeStageClosureBundle
        (stageClosureConcrete steve)
        (stageClosureNextStage upload)
  case verifyStageClosureBundle mixed of
    Left _ -> Right ()
    Right () -> Left "Steve concrete trunk closed against upload next-stage trunk"

reconstructionStable :: Either String ()
reconstructionStable = do
  bundle <- uploadStageClosureBundle
  let rebuilt = makeStageClosureBundle
        (stageClosureConcrete bundle)
        (stageClosureNextStage bundle)
  assert (stageClosureSystemsArtifactRevision bundle
      == stageClosureSystemsArtifactRevision rebuilt
      && stageClosureContractRevision bundle
      == stageClosureContractRevision rebuilt)
    "identical final closure reconstruction changed a canonical revision"
  mapLeft show (verifyStageClosureBundle rebuilt)

uploadArtifact :: Either String SystemsArtifact
uploadArtifact = phase1StageSystemsArtifact <$> uploadCommonStage

uploadCommonStage :: Either String Phase1StageBundle
uploadCommonStage = do
  bundle <- uploadStageClosureBundle
  pure (subjectStageBase (concreteSubjectStage (stageClosureConcrete bundle)))

syntheticStage :: Phase1StageBundle -> SystemsArtifact -> Phase1StageBundle
syntheticStage template artifact = makePhase1StageBundle
  (phase1StageInstanceRevision template)
  (phase1StageRealizationRevision template)
  (phase1StageVerifierProfileRevision template)
  artifact
  dispositions
  justifications
  where
    facts = collectSourceFacts artifact
    mechanisms = collectSystemsMechanisms artifact
    dispositions = Map.fromSet (const (Phase1FactPreserved mechanisms)) facts
    justification = SystemsJustification
      { systemsJustificationSourceFacts = facts
      , systemsJustificationRealizationRefs = Set.singleton "sys020.synthetic.realization"
      , systemsJustificationQualificationRefs = Set.empty
      , systemsJustificationAssumptionRefs = Set.empty
      }
    justifications = Map.fromSet (const justification) mechanisms

insertDiagnostic :: Text -> SystemsArtifact -> SystemsArtifact
insertDiagnostic name = modifyFirstBlock
  (\blockValue -> blockValue
    { systemsBlockOps = OpDiagnostic name (DecisionId "sys020.diagnostic")
        : systemsBlockOps blockValue })

insertTrace :: Text -> SystemsArtifact -> SystemsArtifact
insertTrace event = modifyFirstBlock
  (\blockValue -> blockValue
    { systemsBlockOps = OpTraceEvent event : systemsBlockOps blockValue })

modifyFirstBlock
  :: (SystemsBlock -> SystemsBlock)
  -> SystemsArtifact
  -> SystemsArtifact
modifyFirstBlock f artifact = artifact
  { systemsArtifactProgram = program
      { systemsProgramFunctions = modifyFirstMap modifyFunction
          (systemsProgramFunctions program)
      }
  }
  where
    program = systemsArtifactProgram artifact
    modifyFunction function = function
      { systemsFunctionBlocks = modifyFirstMap f (systemsFunctionBlocks function) }

modifyFirstMap :: Ord k => (v -> v) -> Map.Map k v -> Map.Map k v
modifyFirstMap f values = case Map.lookupMin values of
  Nothing -> values
  Just (key, value) -> Map.insert key (f value) values

reverseMap :: Ord k => Map.Map k v -> Map.Map k v
reverseMap = Map.fromList . reverse . Map.toAscList

need :: String -> Maybe a -> Either String a
need label = maybe (Left (label <> " missing")) Right

assert :: Bool -> String -> Either String ()
assert ok message = if ok then Right () else Left message

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
