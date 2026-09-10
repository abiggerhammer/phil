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
  )
import Phil.Core.CallableRefinement
  ( CallableMachineShape (..)
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
        [ ("exact named callable resolves to persisted declaration identity", exactResolution)
        , ("explicit callable lookup remains distinct from colliding provider primitive", namespaceCollision)
        , ("provider-only spelling is rejected as wrong callable category", primitiveOnlyRejects)
        , ("unknown callable fails closed", unknownRejects)
        , ("duplicate display spelling is rejected as ambiguous", ambiguousRejects)
        , ("stale declaration identity rejects", staleIdentityRejects)
        , ("stale callable interface revision rejects", staleRevisionRejects)
        , ("incompatible callable surface reuses refinement rejection", incompatibleRefinementRejects)
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
  assert (sourceCallableDeclarationKey binding == workerKey)
    "resolved callable did not retain exact worker DeclarationKey"
  assert (sourceCallableInterface binding == workerInterface)
    "resolved callable did not retain exact checked worker interface"

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
        [ (callerKey, callerInterface)
        , (workerKey, workerInterface)
        , (workerOtherKey, workerInterface)
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
  let expectedInterface = callableSurface "worker.v2" "Unit->Unit"
      expectation = CallableInvocationExpectation workerKey expectedInterface
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
  let incompatible = CallableInvocationExpectation
        workerKey
        (callableSurface "worker.v1" "Bytes->Unit")
  case resolveCallableInvocation catalog "Worker" incompatible of
    Left (CallableRefinementRejected "Worker" (CallableMachineShapeMismatch expected actual))
      | expected == CallableMachineShape "Bytes->Unit"
          && actual == CallableMachineShape "Unit->Unit" -> Right ()
    other -> Left ("expected callable refinement rejection, got " <> show other)

missingContractRejects :: Either String ()
missingContractRejects = do
  checked <- checkedBundle baseUnits
  let contracts = Map.singleton callerKey callerInterface
  case buildCallableInvocationCatalog Set.empty contracts checked of
    Left (CallableContractMissing key) | key == workerKey -> Right ()
    other -> Left ("expected missing contract rejection, got " <> show other)

outsideContractRejects :: Either String ()
outsideContractRejects = do
  (checked, contracts) <- baseChecked
  let outsideKey = DeclarationKey "decl:outside"
      withOutside = Map.insert outsideKey workerInterface contracts
  case buildCallableInvocationCatalog Set.empty withOutside checked of
    Left (CallableContractOutsideBundle key) | key == outsideKey -> Right ()
    other -> Left ("expected outside-bundle contract rejection, got " <> show other)

baseChecked :: Either String (CheckedSourceBundle, Map.Map DeclarationKey CallableRefinementSurface)
baseChecked = do
  checked <- checkedBundle baseUnits
  pure
    ( checked
    , Map.fromList
        [ (callerKey, callerInterface)
        , (workerKey, workerInterface)
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
workerExpectation = CallableInvocationExpectation workerKey workerInterface

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
