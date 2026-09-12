{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Compiler.CallableInvocation
import Phil.Compiler.SourceBundle
import Phil.Core.Callable
  ( CallableContract (..)
  , CalleeTransition (..)
  , SemanticEffect (..)
  )
import Phil.Core.CallableOutcome
  ( CallableOutcomeAtom (..)
  , CallableOutcomeClass (..)
  , CallableOutcomeContract (..)
  , CallableOutcomeError (..)
  , CallableOutcomeState (..)
  , CheckedCallableOutcomeContract (..)
  )
import Phil.Core.CallableRefinement
  ( CallableAuthorityRequirement (..)
  , CallableFailure (..)
  , CallableMachineShape (..)
  , CallableRefinementError (..)
  , CallableRefinementSurface (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , InterfaceRevision (..)
  , emptyStaticContext
  )
import Phil.Core.Syntax (Ty (..))
import Phil.Surface.Check
  ( SurfaceEnvironment (..)
  , emptySurfaceEnvironment
  )
import Phil.Surface.Lineage
  ( DeclarationSiteId (..)
  , PortableSourceBundle (..)
  , PortableSourceUnit (..)
  , SourceUnitId (..)
  , canonicalGrammarRevisionV1
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  let checks =
        [ ("exact named callable resolves to persisted declaration identity and complete semantic witness", exactResolution)
        , ("explicit callable lookup remains distinct from colliding provider primitive", namespaceCollision)
        , ("provider-only spelling is rejected as wrong callable category", primitiveOnlyRejects)
        , ("unknown callable fails closed", unknownRejects)
        , ("duplicate display spelling is rejected as ambiguous", ambiguousRejects)
        , ("stale declaration identity rejects", staleIdentityRejects)
        , ("stale callable interface revision rejects", staleRevisionRejects)
        , ("incompatible callable machine shape reuses refinement rejection", incompatibleRefinementRejects)
        , ("stronger caller authority rejects through callable refinement", authorityWideningRejects)
        , ("wider public may-effect rejects through callable refinement", effectWideningRejects)
        , ("wider modeled failure set rejects through callable refinement", failureWideningRejects)
        , ("incompatible global callee lifecycle rejects through callable refinement", lifecycleMismatchRejects)
        , ("branch-sensitive callee lifecycle mismatch rejects through outcome fidelity", outcomeLifecycleMismatchRejects)
        , ("residual obligation mismatch rejects through outcome fidelity", residualMismatchRejects)
        , ("residual obligation cannot be reclassified as a postcondition", residualReclassificationRejects)
        , ("missing callable contract rejects catalog construction", missingContractRejects)
        , ("out-of-bundle callable contract rejects catalog construction", outsideContractRejects)
        ]
  results <- mapM report checks
  if and results then pure () else exitFailure

report :: (String, Either String ()) -> IO Bool
report (label, result) = case result of
  Right () -> putStrLn ("PASS: CALL-019 " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: CALL-019 " <> label <> " -- " <> detail) >> pure False

exactResolution :: Either String ()
exactResolution = do
  (checked, contracts) <- baseChecked
  catalog <- mapLeft show $
    buildCallableInvocationCatalog Set.empty contracts checked
  resolved <- mapLeft show $
    resolveCallableInvocation catalog "Worker" workerExpectation
  let binding = resolvedCallableBinding resolved
      checkedOutcomes = resolvedCallableOutcomes resolved
  assert (sourceCallableDeclarationKey binding == workerKey)
    "resolved callable did not retain exact worker DeclarationKey"
  assert (sourceCallableContract binding == workerContract)
    "resolved callable did not retain exact checked worker semantic contract"
  assert
    (Map.keysSet (checkedCallableActualOutcomes checkedOutcomes)
      == Set.singleton CallableSuccessOutcome)
    "resolved invocation did not retain the exact checked outcome domain"

namespaceCollision :: Either String ()
namespaceCollision = do
  (checked, contracts) <- baseChecked
  catalog <- mapLeft show $
    buildCallableInvocationCatalog (Set.singleton "Worker") contracts checked
  resolved <- mapLeft show $
    resolveCallableInvocation catalog "Worker" workerExpectation
  assert
    (sourceCallableDeclarationKey (resolvedCallableBinding resolved) == workerKey)
    "provider primitive collision redirected explicit callable resolution"

primitiveOnlyRejects :: Either String ()
primitiveOnlyRejects = do
  (checked, contracts) <- baseChecked
  catalog <- mapLeft show $
    buildCallableInvocationCatalog (Set.singleton "digest_compute") contracts checked
  case resolveCallableInvocation catalog "digest_compute" workerExpectation of
    Left (CallableNameRefersOnlyToProviderPrimitive "digest_compute") -> Right ()
    other -> Left ("expected wrong-category provider primitive rejection, got " <> show other)

unknownRejects :: Either String ()
unknownRejects = do
  (checked, contracts) <- baseChecked
  catalog <- mapLeft show $
    buildCallableInvocationCatalog Set.empty contracts checked
  case resolveCallableInvocation catalog "Missing" workerExpectation of
    Left (CallableNameUnknown "Missing") -> Right ()
    other -> Left ("expected unknown callable rejection, got " <> show other)

ambiguousRejects :: Either String ()
ambiguousRejects = do
  checked <- checkedBundle
    [ (callerKey, "unit.caller", "site.caller", "Caller")
    , (workerKey, "unit.worker-a", "site.worker-a", "Worker")
    , (workerOtherKey, "unit.worker-b", "site.worker-b", "Worker")
    ]
  let contracts = Map.fromList
        [ (callerKey, callerContract)
        , (workerKey, workerContract)
        , (workerOtherKey, workerContract)
        ]
  catalog <- mapLeft show $
    buildCallableInvocationCatalog Set.empty contracts checked
  case resolveCallableInvocation catalog "Worker" workerExpectation of
    Left (CallableNameAmbiguous "Worker" keys)
      | keys == [workerKey, workerOtherKey] -> Right ()
      | otherwise -> Left ("ambiguous callable keys drifted: " <> show keys)
    other -> Left ("expected ambiguous callable rejection, got " <> show other)

staleIdentityRejects :: Either String ()
staleIdentityRejects = do
  (checked, contracts) <- baseChecked
  catalog <- mapLeft show $
    buildCallableInvocationCatalog Set.empty contracts checked
  let stale = workerExpectation
        { callableInvocationExpectedDeclarationKey = DeclarationKey "decl:worker-old" }
  case resolveCallableInvocation catalog "Worker" stale of
    Left (CallableDeclarationIdentityMismatch "Worker" expected actual)
      | expected == DeclarationKey "decl:worker-old" && actual == workerKey -> Right ()
    other -> Left ("expected stale declaration identity rejection, got " <> show other)

staleRevisionRejects :: Either String ()
staleRevisionRejects = do
  (checked, contracts) <- baseChecked
  catalog <- mapLeft show $
    buildCallableInvocationCatalog Set.empty contracts checked
  let expectedContract = workerContract
        { sourceCallableRefinementSurface = callableSurface "worker.v2" "Unit->Unit" }
      expectation = CallableInvocationExpectation workerKey expectedContract
  case resolveCallableInvocation catalog "Worker" expectation of
    Left (CallableInterfaceRevisionMismatch "Worker" expected actual)
      | expected == InterfaceRevision "worker.v2"
          && actual == InterfaceRevision "worker.v1" -> Right ()
    other -> Left ("expected stale interface revision rejection, got " <> show other)

incompatibleRefinementRejects :: Either String ()
incompatibleRefinementRejects = do
  (checked, contracts) <- baseChecked
  catalog <- mapLeft show $
    buildCallableInvocationCatalog Set.empty contracts checked
  let expectedContract = workerContract
        { sourceCallableRefinementSurface = callableSurface "worker.v1" "Bytes->Unit" }
      incompatible = CallableInvocationExpectation workerKey expectedContract
  case resolveCallableInvocation catalog "Worker" incompatible of
    Left (CallableRefinementRejected "Worker" (CallableMachineShapeMismatch expected actual))
      | expected == CallableMachineShape "Bytes->Unit"
          && actual == CallableMachineShape "Unit->Unit" -> Right ()
    other -> Left ("expected callable refinement rejection, got " <> show other)

authorityWideningRejects :: Either String ()
authorityWideningRejects =
  expectWorkerRefinementReject
    (workerInterface
      { callableRefinementCallerAuthority =
          Set.singleton (CallableAuthorityRequirement "authority:extra") })
    (\err -> case err of
      CallableAuthorityRequirementTooStrong extra ->
        extra == Set.singleton (CallableAuthorityRequirement "authority:extra")
      _ -> False)
    "authority widening"

effectWideningRejects :: Either String ()
effectWideningRejects =
  let actual = workerInterface
        { callableRefinementContract =
            (callableRefinementContract workerInterface)
              { callableContractEffectBound =
                  Set.singleton (SemanticEffect "effect:extra") } }
  in expectWorkerRefinementReject
      actual
      (\err -> case err of
        CallableEffectBoundTooWide extra ->
          extra == Set.singleton (SemanticEffect "effect:extra")
        _ -> False)
      "effect widening"

failureWideningRejects :: Either String ()
failureWideningRejects =
  expectWorkerRefinementReject
    (workerInterface
      { callableRefinementFailures =
          Set.singleton (CallableFatal "fatal:extra") })
    (\err -> case err of
      CallableFailureSetTooWide extra ->
        extra == Set.singleton (CallableFatal "fatal:extra")
      _ -> False)
    "failure widening"

lifecycleMismatchRejects :: Either String ()
lifecycleMismatchRejects =
  let actual = workerInterface
        { callableRefinementContract =
            (callableRefinementContract workerInterface)
              { callableContractCalleeTransition = ConsumeCallee } }
  in expectWorkerRefinementReject
      actual
      (\err -> case err of
        CallableCalleeTransitionIncompatible PreserveCallee ConsumeCallee -> True
        _ -> False)
      "callee lifecycle mismatch"

expectWorkerRefinementReject
  :: CallableRefinementSurface
  -> (CallableRefinementError -> Bool)
  -> String
  -> Either String ()
expectWorkerRefinementReject actualSurface matches label = do
  checked <- checkedBundle baseUnits
  let actualContract = workerContract
        { sourceCallableRefinementSurface = actualSurface }
      contracts = Map.fromList
        [ (callerKey, callerContract)
        , (workerKey, actualContract)
        ]
  catalog <- mapLeft show $
    buildCallableInvocationCatalog Set.empty contracts checked
  case resolveCallableInvocation catalog "Worker" workerExpectation of
    Left (CallableRefinementRejected "Worker" err)
      | matches err -> Right ()
    other -> Left ("expected " <> label <> " rejection, got " <> show other)

outcomeLifecycleMismatchRejects :: Either String ()
outcomeLifecycleMismatchRejects = do
  let actualOutcome = successOutcome
        { callableOutcomeCalleeTransition = ConsumeCallee }
  expectWorkerOutcomeReject
    [actualOutcome]
    (\err -> case err of
      CallableOutcomeCalleeTransitionMismatch
          CallableSuccessOutcome PreserveCallee ConsumeCallee -> True
      _ -> False)
    "outcome lifecycle mismatch"

residualMismatchRejects :: Either String ()
residualMismatchRejects = do
  let actualOutcome = successOutcome
        { callableOutcomeResidualObligations = Set.singleton residualAtom }
  expectWorkerOutcomeReject
    [actualOutcome]
    (\err -> case err of
      CallableResidualObligationMismatch CallableSuccessOutcome expected actual ->
        Set.null expected && actual == Set.singleton residualAtom
      _ -> False)
    "residual obligation mismatch"

residualReclassificationRejects :: Either String ()
residualReclassificationRejects = do
  checked <- checkedBundle baseUnits
  let expectedOutcome = successOutcome
        { callableOutcomeResidualObligations = Set.singleton residualAtom }
      actualOutcome = successOutcome
        { callableOutcomePostconditions = Set.singleton residualAtom }
      expectedContract = workerContract
        { sourceCallableOutcomeContracts = [expectedOutcome] }
      actualContract = workerContract
        { sourceCallableOutcomeContracts = [actualOutcome] }
      contracts = Map.fromList
        [ (callerKey, callerContract)
        , (workerKey, actualContract)
        ]
      expectation = CallableInvocationExpectation workerKey expectedContract
  catalog <- mapLeft show $
    buildCallableInvocationCatalog Set.empty contracts checked
  case resolveCallableInvocation catalog "Worker" expectation of
    Left (CallableOutcomeFidelityRejected "Worker"
      (CallableResidualObligationReclassified
        CallableSuccessOutcome atom _))
      | atom == residualAtom -> Right ()
    other -> Left
      ("expected residual-obligation reclassification rejection, got " <> show other)

expectWorkerOutcomeReject
  :: [CallableOutcomeContract]
  -> (CallableOutcomeError -> Bool)
  -> String
  -> Either String ()
expectWorkerOutcomeReject actualOutcomes matches label = do
  checked <- checkedBundle baseUnits
  let actualContract = workerContract
        { sourceCallableOutcomeContracts = actualOutcomes }
      contracts = Map.fromList
        [ (callerKey, callerContract)
        , (workerKey, actualContract)
        ]
  catalog <- mapLeft show $
    buildCallableInvocationCatalog Set.empty contracts checked
  case resolveCallableInvocation catalog "Worker" workerExpectation of
    Left (CallableOutcomeFidelityRejected "Worker" err)
      | matches err -> Right ()
    other -> Left ("expected " <> label <> " rejection, got " <> show other)

missingContractRejects :: Either String ()
missingContractRejects = do
  checked <- checkedBundle baseUnits
  let contracts = Map.singleton callerKey callerContract
  case buildCallableInvocationCatalog Set.empty contracts checked of
    Left (CallableContractMissing key) | key == workerKey -> Right ()
    other -> Left ("expected missing contract rejection, got " <> show other)

outsideContractRejects :: Either String ()
outsideContractRejects = do
  (checked, contracts) <- baseChecked
  let outsideKey = DeclarationKey "decl:outside"
      withOutside = Map.insert outsideKey workerContract contracts
  case buildCallableInvocationCatalog Set.empty withOutside checked of
    Left (CallableContractOutsideBundle key) | key == outsideKey -> Right ()
    other -> Left ("expected outside-bundle contract rejection, got " <> show other)

baseChecked
  :: Either
      String
      (CheckedSourceBundle, Map.Map DeclarationKey SourceCallableSemanticContract)
baseChecked = do
  checked <- checkedBundle baseUnits
  pure
    ( checked
    , Map.fromList
        [ (callerKey, callerContract)
        , (workerKey, workerContract)
        ]
    )

baseUnits :: [(DeclarationKey, Text.Text, Text.Text, Text.Text)]
baseUnits =
  [ (callerKey, "unit.caller", "site.caller", "Caller")
  , (workerKey, "unit.worker", "site.worker", "Worker")
  ]

checkedBundle
  :: [(DeclarationKey, Text.Text, Text.Text, Text.Text)]
  -> Either String CheckedSourceBundle
checkedBundle units =
  mapLeft show $
    checkPortableSourceBundle
      (Map.singleton "program:test" callerKey)
      (Map.fromList [(key, unitEnvironment) | (key, _, _, _) <- units])
      PortableSourceBundle
        { portableGrammarRevision = canonicalGrammarRevisionV1
        , portableSelectedProgramRoot = "program:test"
        , portableSourceUnits =
            [ PortableSourceUnit
                (SourceUnitId unitId)
                (DeclarationSiteId siteId)
                (Just (unDeclarationKey key))
                ("component " <> name <> " provides Unit { return unit }")
            | (key, unitId, siteId, name) <- units
            ]
        , portableInstanceLineage = []
        , portableProcessLineage = []
        }

unitEnvironment :: SurfaceEnvironment
unitEnvironment = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceExpectedProvides = Just TyUnit }

workerExpectation :: CallableInvocationExpectation
workerExpectation = CallableInvocationExpectation workerKey workerContract

callerContract, workerContract :: SourceCallableSemanticContract
callerContract = SourceCallableSemanticContract callerInterface [successOutcome]
workerContract = SourceCallableSemanticContract workerInterface [successOutcome]

callerInterface, workerInterface :: CallableRefinementSurface
callerInterface = callableSurface "caller.v1" "Unit->Unit"
workerInterface = callableSurface "worker.v1" "Unit->Unit"

callableSurface :: Text.Text -> Text.Text -> CallableRefinementSurface
callableSurface revision shape = CallableRefinementSurface
  { callableRefinementMachineShape = CallableMachineShape shape
  , callableRefinementContract = CallableContract
      { callableContractInterfaceRevision = InterfaceRevision revision
      , callableContractCalleeTransition = PreserveCallee
      , callableContractEffectBound = Set.empty
      }
  , callableRefinementCallerAuthority = Set.empty
  , callableRefinementFailures = Set.empty
  }

successOutcome :: CallableOutcomeContract
successOutcome = CallableOutcomeContract
  { callableOutcomeClass = CallableSuccessOutcome
  , callableOutcomeState = CallableOutcomeState "state:unit"
  , callableOutcomeCalleeTransition = PreserveCallee
  , callableOutcomePostconditions = Set.empty
  , callableOutcomeResidualObligations = Set.empty
  , callableOutcomeAssumptions = Set.empty
  , callableOutcomeEffects = Set.empty
  , callableOutcomeDischargedFacts = Set.empty
  }

residualAtom :: CallableOutcomeAtom
residualAtom = CallableOutcomeAtom "obligation:worker-output"

callerKey, workerKey, workerOtherKey :: DeclarationKey
callerKey = DeclarationKey "decl:caller"
workerKey = DeclarationKey "decl:worker"
workerOtherKey = DeclarationKey "decl:worker-other"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
