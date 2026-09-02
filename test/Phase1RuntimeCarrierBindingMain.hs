{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance.Types
import Phil.Core.Process (ProcessKey (..))
import Phil.Systems.IR
import Phil.Systems.ProcessRealization (PhysicalExecutionKey (..))
import Phil.Systems.RuntimeCarrierBinding
import Phil.Systems.RuntimeCarrierCoverage
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "DEP-001 exact selected runtime use binds exact established carrier/site" exactBindingAccepts
    , test "DEP-001 missing carrier binding cannot close RuntimeEnforced assurance" missingBindingRejects
    , test "DEP-001 merely asserted unknown carrier cannot close assurance" phantomCarrierRejects
    , test "DEP-001 carrier must own the exact retained obligation" wrongCarrierObligationRejects
    , test "DEP-001 unrelated runtime evidence cannot stand in for selected evidence" wrongSiteEvidenceRejects
    , test "DEP-001 selected RuntimeEnforced evidence must name a runtime mechanism" missingMechanismRejects
    , test "DEP-001 non-runtime evidence cannot be rebound as a carrier" nonRuntimeEvidenceRejects
    , test "DEP-001 exact runtime site must really occur in the Systems program" missingRuntimeSiteRejects
    , test "DEP-001 duplicate exact runtime sites cannot ambiguously establish one use" duplicateRuntimeSiteRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactBindingAccepts :: Either String ()
exactBindingAccepts =
  mapLeft show $ checkRuntimeCarrierBindings
    ledger manifest artifact carriers bindings

missingBindingRejects :: Either String ()
missingBindingRejects =
  case checkRuntimeCarrierBindings ledger manifest artifact carriers Map.empty of
    Left (RuntimeCarrierBindingDomainMismatch expected actual) ->
      assert
        (expected == Set.singleton runtimeUseId && Set.null actual)
        "missing-binding rejection lost the exact selected-use domain"
    other -> Left ("missing RuntimeBound carrier binding was accepted: " <> show other)

phantomCarrierRejects :: Either String ()
phantomCarrierRejects =
  case checkRuntimeCarrierBindings ledger manifest artifact Map.empty bindings of
    Left (RuntimeCarrierBindingCarrierMissing useId key) ->
      assert
        (useId == runtimeUseId && key == carrierKey)
        "phantom-carrier rejection lost exact use/carrier identity"
    other -> Left ("merely asserted carrier binding was accepted: " <> show other)

wrongCarrierObligationRejects :: Either String ()
wrongCarrierObligationRejects =
  let wrongCarrier = carrier { runtimeCarrierObligation = otherObligation }
  in case checkRuntimeCarrierBindings
      ledger manifest artifact (Map.singleton carrierKey wrongCarrier) bindings of
    Left (RuntimeCarrierBindingCarrierObligationMismatch useId key expected actual) ->
      assert
        ( useId == runtimeUseId
          && key == carrierKey
          && expected == obligation
          && actual == otherObligation
        )
        "carrier-obligation rejection lost exact identities"
    other -> Left ("carrier for a different obligation was accepted: " <> show other)

wrongSiteEvidenceRejects :: Either String ()
wrongSiteEvidenceRejects =
  let wrongSite = runtimeSite { runtimeSiteEvidence = otherEvidenceId }
      wrongBinding = binding { runtimeCarrierBindingRuntimeSite = wrongSite }
  in case checkRuntimeCarrierBindings
      ledger manifest artifact carriers (Map.singleton runtimeUseId wrongBinding) of
    Left (RuntimeCarrierBindingSiteEvidenceMismatch useId expected actual) ->
      assert
        (useId == runtimeUseId && expected == evidenceId && actual == otherEvidenceId)
        "site-evidence rejection lost exact evidence identity"
    other -> Left ("unrelated runtime evidence was accepted as the selected carrier site: " <> show other)

missingMechanismRejects :: Either String ()
missingMechanismRejects =
  let badEvidence = runtimeEvidence { evidenceRuntimeMechanism = Nothing }
      badLedger = ledger { ledgerEvidence = Map.singleton evidenceId badEvidence }
  in case checkRuntimeCarrierBindings badLedger manifest artifact carriers bindings of
    Left (RuntimeCarrierBindingEvidenceMechanismMissing useId actualEvidence) ->
      assert
        (useId == runtimeUseId && actualEvidence == evidenceId)
        "missing-mechanism rejection lost exact use/evidence identity"
    other -> Left ("RuntimeEnforced evidence without a runtime mechanism was accepted: " <> show other)

nonRuntimeEvidenceRejects :: Either String ()
nonRuntimeEvidenceRejects =
  let badEvidence = runtimeEvidence { evidenceAssuranceKind = PropertyTested }
      badLedger = ledger { ledgerEvidence = Map.singleton evidenceId badEvidence }
  in case checkRuntimeCarrierBindings badLedger manifest artifact carriers bindings of
    Left (RuntimeCarrierBindingEvidenceNotRuntimeEnforced useId actualEvidence actualKind) ->
      assert
        ( useId == runtimeUseId
          && actualEvidence == evidenceId
          && actualKind == PropertyTested
        )
        "non-runtime-evidence rejection lost exact use/evidence/kind identity"
    other -> Left ("non-RuntimeEnforced evidence was rebound as a carrier: " <> show other)

missingRuntimeSiteRejects :: Either String ()
missingRuntimeSiteRejects =
  let absentSite = runtimeSite { runtimeSiteKind = SourceSemanticRuntime "different-runtime-site" }
      absentBinding = binding { runtimeCarrierBindingRuntimeSite = absentSite }
  in case checkRuntimeCarrierBindings
      ledger manifest artifact carriers (Map.singleton runtimeUseId absentBinding) of
    Left (RuntimeCarrierBindingSiteMissing useId) ->
      assert (useId == runtimeUseId)
        "missing-site rejection lost exact assurance-use identity"
    other -> Left ("carrier binding to a runtime site absent from Systems was accepted: " <> show other)

duplicateRuntimeSiteRejects :: Either String ()
duplicateRuntimeSiteRejects =
  case checkRuntimeCarrierBindings ledger manifest duplicateSiteArtifact carriers bindings of
    Left (RuntimeCarrierBindingSiteAmbiguous useId count) ->
      assert (useId == runtimeUseId && count == 2)
        "duplicate-site rejection lost exact use/count identity"
    other -> Left ("two exact runtime sites ambiguously established one retained use: " <> show other)

runtimeUseId :: AssuranceUseId
runtimeUseId = AssuranceUseId "use.dep001.checked-overflow"

evidenceId, otherEvidenceId :: EvidenceEntryId
evidenceId = EvidenceEntryId "evidence.dep001.checked-overflow"
otherEvidenceId = EvidenceEntryId "evidence.dep001.other"

obligation, otherObligation :: RevisionId
obligation = RevisionId "obligation.dep001.checked-overflow"
otherObligation = RevisionId "obligation.dep001.other"

costRef :: Text
costRef = "cost.dep001.checked-overflow"

runtimeUse :: AssuranceUse
runtimeUse = RetainedRuntimeUse
  { assuranceUseId = runtimeUseId
  , assuranceUseDigest = Digest "use.dep001.digest"
  , useObligationRevision = obligation
  , useRuntimeEvidence = evidenceId
  , useCostRef = costRef
  }

runtimeEvidence :: EvidenceEntry
runtimeEvidence = EvidenceEntry
  { evidenceEntryId = evidenceId
  , evidenceEntryDigest = Digest "evidence.dep001.digest"
  , evidenceObligationRevision = obligation
  , evidenceAssuranceKind = RuntimeEnforced
  , evidenceRole = EvidenceRole "runtime-carrier"
  , evidenceProducer = "phil.systems.dep001"
  , evidenceChecker = "phil.systems.dep001"
  , evidenceArtifact = Nothing
  , evidenceInputDigests = []
  , evidenceAssumptions = []
  , evidenceDependsOn = []
  , evidenceValidityScope = ValidityScope Map.empty
  , evidenceResult = EvidenceAccepted
  , evidenceJustifies = ["exact RuntimeBound carrier"]
  , evidenceRuntimeMechanism = Just RuntimeMechanism
      { runtimeMechanismName = "checked-overflow"
      , runtimeExecutionPoint = "entry.check"
      , runtimeSuccessEvidenceType = "range-proof"
      , runtimeFailureContract = "overflow"
      , runtimeImplementation = Nothing
      }
  , evidenceRuntimeResidue = ["checked-overflow-runtime-carrier"]
  , evidenceCostRefs = [costRef]
  }

ledger :: AssuranceLedger
ledger = emptyLedger
  { ledgerEvidence = Map.singleton evidenceId runtimeEvidence
  , ledgerUses = Map.singleton runtimeUseId runtimeUse
  }

manifest :: AssuranceManifest
manifest = emptyManifest
  { manifestObligationRevisions = Set.singleton obligation
  , manifestCertificationScope = Set.singleton obligation
  , manifestEvidenceEntries = Set.singleton evidenceId
  , manifestAssuranceUses = Set.singleton runtimeUseId
  }

runtimeSite :: RuntimeSiteRef
runtimeSite = RuntimeSiteRef
  { runtimeSiteKind = SourceSemanticRuntime "uint.checked-overflow"
  , runtimeSiteRevision = obligation
  , runtimeSiteEvidence = evidenceId
  , runtimeSiteCostRef = costRef
  }

artifact :: SystemsArtifact
artifact = SystemsArtifact
  { systemsArtifactProgram = programWithOneSite
  , systemsArtifactStageContract = stageContract
  , systemsArtifactLoweringLedger = LoweringLedger Map.empty (Digest "ledger.dep001")
  }

duplicateSiteArtifact :: SystemsArtifact
duplicateSiteArtifact = artifact
  { systemsArtifactProgram = SystemsProgram
      { systemsProgramName = "dep001-duplicate"
      , systemsProgramProfile = CheckedRuntime
      , systemsProgramFunctions = Map.fromList
          [ ("first", runtimeFunction "first")
          , ("second", runtimeFunction "second")
          ]
      }
  }

programWithOneSite :: SystemsProgram
programWithOneSite = SystemsProgram
  { systemsProgramName = "dep001"
  , systemsProgramProfile = CheckedRuntime
  , systemsProgramFunctions = Map.singleton "main" (runtimeFunction "main")
  }

runtimeFunction :: Text -> SystemsFunction
runtimeFunction functionName = SystemsFunction
  { systemsFunctionName = functionName
  , systemsFunctionEntry = entryBlock
  , systemsFunctionValues = Map.empty
  , systemsFunctionBlocks = Map.fromList
      [ (entryBlock, SystemsBlock entryBlock []
          (TermRuntimeCheck [] runtimeSite successBlock failureBlock))
      , (successBlock, SystemsBlock successBlock [] (TermEnd "done"))
      , (failureBlock, SystemsBlock failureBlock [] (TermFatal "overflow"))
      ]
  }

entryBlock, successBlock, failureBlock :: BlockId
entryBlock = BlockId "entry"
successBlock = BlockId "success"
failureBlock = BlockId "failure"

stageContract :: StageContract
stageContract = StageContract
  { stageContractId = "stage.dep001"
  , stageSourceArtifactDigest = Digest "source.dep001"
  , stageTargetArtifactDigest = Digest "target.dep001"
  , stageFacts = []
  , stageInvariants = Map.empty
  , stageRequiredEdges = []
  , stageDerivedObligations = [obligation]
  , stageAssumptions = []
  , stageTraceRelation = []
  , stageResourceFailureRelation = []
  }

carrierKey :: RuntimeCarrierKey
carrierKey = RuntimeCarrierKey "carrier.dep001.checked-overflow"

carrier :: RuntimeCarrier
carrier = RuntimeCarrier
  { runtimeCarrierKey = carrierKey
  , runtimeCarrierObligation = obligation
  , runtimeCarrierProcess = ProcessKey "process.dep001"
  , runtimeCarrierExecutions = Set.singleton (PhysicalExecutionKey "worker.dep001")
  , runtimeCarrierFailureFactId = "failure.dep001.checked-overflow"
  }

carriers :: Map.Map RuntimeCarrierKey RuntimeCarrier
carriers = Map.singleton carrierKey carrier

binding :: RuntimeCarrierBinding
binding = RuntimeCarrierBinding
  { runtimeCarrierBindingUseId = runtimeUseId
  , runtimeCarrierBindingCarrierKey = carrierKey
  , runtimeCarrierBindingRuntimeSite = runtimeSite
  }

bindings :: Map.Map AssuranceUseId RuntimeCarrierBinding
bindings = Map.singleton runtimeUseId binding

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
