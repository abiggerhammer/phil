{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance.Phase0
  ( phase0UploadLedger
  , phase0UploadManifest
  , phase0UploadVerificationContext
  )
import Phil.Assurance.Types
import Phil.Core.Process (ProcessKey (..))
import Phil.Examples.Phase1.StageClosureWitnesses
  ( uploadStageClosureBundle
  )
import Phil.Systems.CostAttribution
  ( CostAttributionStageBundle (..)
  )
import Phil.Systems.IR
  ( RuntimeSiteRef (..)
  , StageContract (..)
  , SystemsArtifact (..)
  )
import Phil.Systems.NextStageRequirement
  ( NextStageRequirementStageBundle (..)
  )
import Phil.Systems.Phase1Stage
  ( Phase1StageBundle (..)
  )
import Phil.Systems.ProcessRealization
import Phil.Systems.RuntimeCarrierBinding
import Phil.Systems.RuntimeCarrierCertification
import Phil.Systems.RuntimeCarrierCoverage
import Phil.Systems.RuntimeClaimBinding
import Phil.Systems.RuntimePrimitiveReuse
  ( RuntimePrimitiveStageBundle (..)
  )
import Phil.Systems.StageClosure
  ( StageClosureBundle (..)
  , nextStageSubjectStage
  )
import Phil.Systems.StagingEffect
  ( StagingEffectStageBundle (..)
  )
import Phil.Systems.SubjectCorrespondence
  ( SubjectStageBundle (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "production Runtime Carrier certification accepts real upload assurance + StageClosure" exactProductionBindingAccepts
    , test "source-fact obligations are legitimate Runtime Carrier StageContract obligations" sourceFactObligationsAccept
    , test "covered target-use links must cover exactly the covered-use domain" missingUseLinkRejects
    , test "covered target use cannot borrow another retained assurance binding" wrongAssuranceLinkRejects
    , test "every carrier needs an exact verified runtime-claim identity" missingClaimLinkRejects
    , test "unknown runtime claim cannot stand in for the carrier claim" unknownClaimRejects
    , test "carrier obligation drift remains a native fail-closed rejection" carrierObligationDriftRejects
    , test "RuntimeBound carriers remain profile-gated" forbiddenProfileRejects
    , test "duplicate target-use identity cannot hide in list enumeration" duplicateUseIdRejects
    , test "duplicate transition identity cannot hide in list enumeration" duplicateTransitionIdRejects
    , test "discharge cannot leave the same obligation RuntimeBound at destination" dischargeDestinationRuntimeBoundRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactProductionBindingAccepts :: Either String ()
exactProductionBindingAccepts = fixture >>= verifyFixture

sourceFactObligationsAccept :: Either String ()
sourceFactObligationsAccept = do
  f <- fixture
  first <- firstBound f
  let contract = artifactContract (fixtureClosure f)
      obligation = runtimeCarrierObligation (boundCarrier first)
  assert
    (obligation `notElem` stageDerivedObligations contract)
    "fixture obligation unexpectedly came from stageDerivedObligations instead of a source fact"
  mapLeft show $ checkRuntimeCarrierCoverage
    (fixtureProfile f)
    contract
    (fixtureRealization f)
    (fixtureCarriers f)
    (fixtureUses f)
    (fixtureTransitions f)

missingUseLinkRejects :: Either String ()
missingUseLinkRejects = do
  f <- fixture
  first <- firstBound f
  let useId = runtimeCarrierUseId (boundUse first)
      witness0 = fixtureWitness f
      witness1 = witness0
        { runtimeCarrierCertificationUseLinks =
            Map.delete useId (runtimeCarrierCertificationUseLinks witness0)
        }
  case verifyFixture f { fixtureWitness = witness1 } of
    Left detail
      | "RuntimeCarrierCertificationUseLinkDomainMismatch" `contains` detail -> Right ()
    other -> Left ("missing covered-use link was not rejected at witness domain: " <> show other)

wrongAssuranceLinkRejects :: Either String ()
wrongAssuranceLinkRejects = do
  f <- fixture
  first <- firstBound f
  second <- secondBound f
  let useId = runtimeCarrierUseId (boundUse first)
      witness0 = fixtureWitness f
      witness1 = witness0
        { runtimeCarrierCertificationUseLinks = Map.insert
            useId
            (boundAssuranceId second)
            (runtimeCarrierCertificationUseLinks witness0)
        }
  case verifyFixture f { fixtureWitness = witness1 } of
    Left detail
      | "RuntimeCarrierCertificationRetainedUseUncovered" `contains` detail
          || "RuntimeCarrierCertificationCarrierBindingMismatch" `contains` detail
          || "RuntimeCarrierCertificationUseObligationMismatch" `contains` detail -> Right ()
    other -> Left ("cross-assurance carrier link was accepted: " <> show other)

missingClaimLinkRejects :: Either String ()
missingClaimLinkRejects = do
  f <- fixture
  first <- firstBound f
  let key = runtimeCarrierKey (boundCarrier first)
      witness0 = fixtureWitness f
      witness1 = witness0
        { runtimeCarrierCertificationClaims =
            Map.delete key (runtimeCarrierCertificationClaims witness0)
        }
  case verifyFixture f { fixtureWitness = witness1 } of
    Left detail
      | "RuntimeCarrierCertificationClaimDomainMismatch" `contains` detail -> Right ()
    other -> Left ("carrier without claim identity was accepted: " <> show other)

unknownClaimRejects :: Either String ()
unknownClaimRejects = do
  f <- fixture
  first <- firstBound f
  let key = runtimeCarrierKey (boundCarrier first)
      witness0 = fixtureWitness f
      witness1 = witness0
        { runtimeCarrierCertificationClaims = Map.insert
            key
            (RuntimeClaimRevision "claim.runtime-carrier.missing")
            (runtimeCarrierCertificationClaims witness0)
        }
  case verifyFixture f { fixtureWitness = witness1 } of
    Left detail
      | "RuntimeCarrierCertificationClaimMissing" `contains` detail -> Right ()
    other -> Left ("unknown runtime claim was accepted: " <> show other)

carrierObligationDriftRejects :: Either String ()
carrierObligationDriftRejects = do
  f <- fixture
  first <- firstBound f
  let carrier0 = boundCarrier first
      badCarrier = carrier0
        { runtimeCarrierObligation = RevisionId "obligation.runtime-carrier.drift" }
      carriers1 = Map.insert (runtimeCarrierKey carrier0) badCarrier (fixtureCarriers f)
  case verifyFixture f { fixtureCarriers = carriers1 } of
    Left detail
      | "RuntimeCarrierCertificationBindingError (RuntimeCarrierBindingCarrierObligationMismatch" `contains` detail
          || "RuntimeCarrierCertificationCoverageError" `contains` detail -> Right ()
    other -> Left ("carrier obligation drift was accepted: " <> show other)

forbiddenProfileRejects :: Either String ()
forbiddenProfileRejects = do
  f <- fixture
  let profile = (fixtureProfile f)
        { runtimeCarrierProfileRevision = "profile.certified-release.no-runtime-bound.v1"
        , runtimeCarrierProfilePermitsRuntimeBound = False
        }
  case verifyFixture f { fixtureProfile = profile } of
    Left detail
      | "RuntimeCarrierCertificationCoverageError" `contains` detail -> Right ()
    other -> Left ("forbidden RuntimeBound profile was accepted: " <> show other)

duplicateUseIdRejects :: Either String ()
duplicateUseIdRejects = do
  f <- fixture
  first <- firstBound f
  case verifyFixture f { fixtureUses = boundUse first : fixtureUses f } of
    Left detail
      | "RuntimeCarrierCertificationDuplicateUseId" `contains` detail -> Right ()
    other -> Left ("duplicate target-use identity was accepted: " <> show other)

duplicateTransitionIdRejects :: Either String ()
duplicateTransitionIdRejects = do
  f <- fixture
  case fixtureTransitions f of
    [] -> Left "fixture unexpectedly had no transitions"
    transition : _ ->
      case verifyFixture f { fixtureTransitions = transition : fixtureTransitions f } of
        Left detail
          | "RuntimeCarrierCertificationDuplicateTransitionId" `contains` detail -> Right ()
        other -> Left ("duplicate transition identity was accepted: " <> show other)

dischargeDestinationRuntimeBoundRejects :: Either String ()
dischargeDestinationRuntimeBoundRejects = do
  f <- fixture
  third <- thirdBound f
  let extraUse = (boundUse third)
        { runtimeCarrierUseId = runtimeCarrierUseId (boundUse third) <> ".destination"
        , runtimeCarrierUseExecution = fixtureExecutionTo f
        }
      witness0 = fixtureWitness f
      witness1 = witness0
        { runtimeCarrierCertificationUseLinks = Map.insert
            (runtimeCarrierUseId extraUse)
            (boundAssuranceId third)
            (runtimeCarrierCertificationUseLinks witness0)
        }
      f1 = f
        { fixtureUses = extraUse : fixtureUses f
        , fixtureWitness = witness1
        }
  case verifyFixture f1 of
    Left detail
      | "RuntimeCarrierTransitionDestinationStillRuntimeBound" `contains` detail -> Right ()
    other -> Left ("discharged carrier remained RuntimeBound at destination: " <> show other)

data BoundUse = BoundUse
  { boundAssuranceId :: AssuranceUseId
  , boundCarrier :: RuntimeCarrier
  , boundBinding :: RuntimeCarrierBinding
  , boundUse :: RuntimeCarrierUse
  , boundClaimRevision :: RuntimeClaimRevision
  }

data Fixture = Fixture
  { fixtureClosure :: StageClosureBundle
  , fixtureProfile :: RuntimeCarrierProfile
  , fixtureRealization :: ProcessExecutionRealization
  , fixtureCarriers :: Map.Map RuntimeCarrierKey RuntimeCarrier
  , fixtureBindings :: Map.Map AssuranceUseId RuntimeCarrierBinding
  , fixtureUses :: [RuntimeCarrierUse]
  , fixtureTransitions :: [RuntimeCarrierTransition]
  , fixtureWitness :: RuntimeCarrierCertificationWitness
  , fixtureBounds :: [BoundUse]
  , fixtureExecutionTo :: PhysicalExecutionKey
  }

verifyFixture :: Fixture -> Either String ()
verifyFixture f = mapLeft show $ verifyRuntimeCarrierCertification
  phase0UploadVerificationContext
  phase0UploadLedger
  phase0UploadManifest
  (fixtureClosure f)
  (fixtureProfile f)
  (fixtureRealization f)
  (fixtureCarriers f)
  (fixtureBindings f)
  (fixtureUses f)
  (fixtureTransitions f)
  (fixtureWitness f)

fixture :: Either String Fixture
fixture = do
  closure <- uploadStageClosureBundle
  let claimStage = runtimeClaimStageFromClosure closure
      process = ProcessKey "process.runtime-carrier.upload"
      executionFrom = PhysicalExecutionKey "runtime-carrier.execution.from"
      executionTo = PhysicalExecutionKey "runtime-carrier.execution.to"
      retained =
        [ (useId, use)
        | useId <- Set.toAscList (manifestAssuranceUses phase0UploadManifest)
        , Just use@RetainedRuntimeUse {} <- [Map.lookup useId (ledgerUses phase0UploadLedger)]
        ]
  bounds <- mapM (makeBound claimStage process executionFrom executionTo) retained
  (first, second, third, fourth) <- firstFour bounds

  let replacementKey = RuntimeCarrierKey
        (unRuntimeCarrierKey (runtimeCarrierKey (boundCarrier second)) <> ".replacement")
      replacementCarrier = (boundCarrier second)
        { runtimeCarrierKey = replacementKey
        , runtimeCarrierFailureFactId =
            runtimeCarrierFailureFactId (boundCarrier second) <> ".replacement"
        }
      baseCarriers = Map.fromList
        [ (runtimeCarrierKey (boundCarrier b), boundCarrier b)
        | b <- bounds
        ]
      carriers = Map.insert replacementKey replacementCarrier baseCarriers
      bindings = Map.fromList
        [ (boundAssuranceId b, boundBinding b)
        | b <- bounds
        ]
      uses = map boundUse bounds
      transitions =
        [ transition "preserve"
            (runtimeCarrierObligation (boundCarrier first))
            process executionFrom executionTo
            (CarrierPreserved (runtimeCarrierKey (boundCarrier first)))
        , transition "replace"
            (runtimeCarrierObligation (boundCarrier second))
            process executionFrom executionTo
            (CarrierReplaced
              (runtimeCarrierKey (boundCarrier second))
              replacementKey)
        , transition "discharge"
            (runtimeCarrierObligation (boundCarrier third))
            process executionFrom executionTo
            (CarrierDischarged
              (runtimeCarrierKey (boundCarrier third))
              "exact source obligation discharged before destination")
        , transition "validity-ended"
            (runtimeCarrierObligation (boundCarrier fourth))
            process executionFrom executionTo
            (CarrierValidityEnded
              (runtimeCarrierKey (boundCarrier fourth))
              "exact source obligation validity ended before destination")
        ]
      failureFacts = Set.fromList
        [ ProcessSemanticFact
            (runtimeCarrierFailureFactId carrier)
            process
            ProcessFailureFact
            "runtime-carrier-failure"
        | carrier <- Map.elems carriers
        ]
      realization = ProcessExecutionRealization
        { realizationProcessExecutions = Map.singleton process
            (Set.fromList [executionFrom, executionTo])
        , realizationEventExecutions = Map.empty
        , realizationPhysicalCausality = Set.empty
        , realizationRestrictedOwners = Map.empty
        , realizationSemanticFacts = failureFacts
        , realizationTerminalFacts = Map.empty
        , realizationExecutionDecisions = Map.empty
        , realizationAssumptions = Set.empty
        }
      useLinks = Map.fromList
        [ (runtimeCarrierUseId (boundUse b), boundAssuranceId b)
        | b <- bounds
        ]
      baseClaims = Map.fromList
        [ (runtimeCarrierKey (boundCarrier b), boundClaimRevision b)
        | b <- bounds
        ]
      claims = Map.insert replacementKey (boundClaimRevision second) baseClaims
      witness = RuntimeCarrierCertificationWitness
        { runtimeCarrierCertificationUseLinks = useLinks
        , runtimeCarrierCertificationClaims = claims
        }
  pure Fixture
    { fixtureClosure = closure
    , fixtureProfile = RuntimeCarrierProfile
        { runtimeCarrierProfileRevision = "profile.checked-runtime.phase1"
        , runtimeCarrierProfilePermitsRuntimeBound = True
        }
    , fixtureRealization = realization
    , fixtureCarriers = carriers
    , fixtureBindings = bindings
    , fixtureUses = uses
    , fixtureTransitions = transitions
    , fixtureWitness = witness
    , fixtureBounds = bounds
    , fixtureExecutionTo = executionTo
    }

makeBound
  :: RuntimeClaimStageBundle
  -> ProcessKey
  -> PhysicalExecutionKey
  -> PhysicalExecutionKey
  -> (AssuranceUseId, AssuranceUse)
  -> Either String BoundUse
makeBound claimStage process executionFrom executionTo (assuranceId, assuranceUse) =
  case assuranceUse of
    ErasureUse {} -> Left "non-retained use unexpectedly reached Runtime Carrier fixture"
    RetainedRuntimeUse
      { useObligationRevision = obligation
      , useRuntimeEvidence = evidence
      , useCostRef = costRef
      } -> do
        (siteKey, siteRef) <- uniqueMatchingSite claimStage obligation evidence costRef
        claimRevision <- case Set.toAscList
            (Map.findWithDefault Set.empty siteKey (runtimeClaimStageReverse claimStage)) of
          [] -> Left ("runtime site has no verified claim: " <> show siteKey)
          claim : _ -> Right claim
        let carrierKey = RuntimeCarrierKey
              ("carrier.production." <> unAssuranceUseId assuranceId)
            failureFactId = "failure.production." <> unAssuranceUseId assuranceId
            carrier = RuntimeCarrier
              { runtimeCarrierKey = carrierKey
              , runtimeCarrierObligation = obligation
              , runtimeCarrierProcess = process
              , runtimeCarrierExecutions = Set.fromList [executionFrom, executionTo]
              , runtimeCarrierFailureFactId = failureFactId
              }
            binding = RuntimeCarrierBinding
              { runtimeCarrierBindingUseId = assuranceId
              , runtimeCarrierBindingCarrierKey = carrierKey
              , runtimeCarrierBindingRuntimeSite = siteRef
              }
            use = RuntimeCarrierUse
              { runtimeCarrierUseId = "target.production." <> unAssuranceUseId assuranceId
              , runtimeCarrierUseObligation = obligation
              , runtimeCarrierUseProcess = process
              , runtimeCarrierUseExecution = executionFrom
              , runtimeCarrierUseFailureFactId = Just failureFactId
              , runtimeCarrierUseDisposition = RuntimeUseCovered carrierKey
              }
        pure BoundUse
          { boundAssuranceId = assuranceId
          , boundCarrier = carrier
          , boundBinding = binding
          , boundUse = use
          , boundClaimRevision = claimRevision
          }

uniqueMatchingSite
  :: RuntimeClaimStageBundle
  -> RevisionId
  -> EvidenceEntryId
  -> Text
  -> Either String (RuntimeSiteKey, RuntimeSiteRef)
uniqueMatchingSite claimStage obligation evidence costRef =
  case
    [ (siteKey, siteRef)
    | (siteKey, binding) <- Map.toAscList (runtimeClaimStageSites claimStage)
    , let siteRef = runtimeSiteBindingRef binding
    , runtimeSiteRevision siteRef == obligation
    , runtimeSiteEvidence siteRef == evidence
    , runtimeSiteCostRef siteRef == costRef
    ] of
    [] -> Left ("no StageClosure runtime site matched retained assurance use " <> show obligation)
    [value] -> Right value
    values -> Left ("ambiguous StageClosure runtime sites for retained assurance use: " <> show (length values))

transition
  :: Text
  -> RevisionId
  -> ProcessKey
  -> PhysicalExecutionKey
  -> PhysicalExecutionKey
  -> RuntimeCarrierTransitionDisposition
  -> RuntimeCarrierTransition
transition suffix obligation process executionFrom executionTo disposition =
  RuntimeCarrierTransition
    { runtimeCarrierTransitionId = "transition.production." <> suffix
    , runtimeCarrierTransitionObligation = obligation
    , runtimeCarrierTransitionProcess = process
    , runtimeCarrierTransitionFrom = executionFrom
    , runtimeCarrierTransitionTo = executionTo
    , runtimeCarrierTransitionDisposition = disposition
    }

runtimeClaimStageFromClosure :: StageClosureBundle -> RuntimeClaimStageBundle
runtimeClaimStageFromClosure =
  runtimePrimitiveStageBase
    . stagingEffectStageBase
    . costAttributionStageBase
    . nextStageRequirementStageBase
    . stageClosureNextStage

artifactContract :: StageClosureBundle -> StageContract
artifactContract =
  systemsArtifactStageContract
    . phase1StageSystemsArtifact
    . subjectStageBase
    . nextStageSubjectStage
    . stageClosureNextStage

firstBound :: Fixture -> Either String BoundUse
firstBound f = case fixtureBounds f of
  first : _ -> Right first
  [] -> Left "fixture had no retained runtime uses"

secondBound :: Fixture -> Either String BoundUse
secondBound f = case fixtureBounds f of
  _ : second : _ -> Right second
  _ -> Left "fixture had fewer than two retained runtime uses"

thirdBound :: Fixture -> Either String BoundUse
thirdBound f = case fixtureBounds f of
  _ : _ : third : _ -> Right third
  _ -> Left "fixture had fewer than three retained runtime uses"

firstFour :: [a] -> Either String (a, a, a, a)
firstFour values = case values of
  first : second : third : fourth : _ -> Right (first, second, third, fourth)
  _ -> Left "fixture needs at least four retained runtime uses"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

contains :: String -> String -> Bool
contains needle haystack = any (needle `prefixOf`) (tails haystack)

prefixOf :: String -> String -> Bool
prefixOf [] _ = True
prefixOf _ [] = False
prefixOf (x : xs) (y : ys) = x == y && prefixOf xs ys

tails :: [a] -> [[a]]
tails [] = [[]]
tails value@(_ : rest) = value : tails rest

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right