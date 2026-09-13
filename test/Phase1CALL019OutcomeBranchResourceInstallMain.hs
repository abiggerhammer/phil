{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Compiler.CallableOutcomeBranchResourceInstall
  ( SurfaceCallableOutcomeBranchResourceInstallError (..)
  , installSurfaceCallableOutcomeBranchResources
  )
import Phil.Compiler.CallableOutcomeBranchResources
  ( SurfaceCallableOutcomeBranchResourceEnvironment (..)
  , SurfaceCallableOutcomeResourceExpectation (..)
  , SurfaceCallableOutcomeResourceResidueBinding (..)
  , bindSurfaceCallableOutcomeBranchResources
  )
import Phil.Compiler.CallableOutcomeContinuation
  ( SurfaceCallableOutcomeContinuation (..)
  , SurfaceCallableOutcomeContinuationDisposition (..)
  )
import Phil.Core.Callable (CalleeTransition (..))
import Phil.Core.CallableOutcome
  ( CallableOutcomeClass (..)
  , CallableOutcomeContract (..)
  , CallableOutcomeState (..)
  )
import Phil.Core.CallableRefinement (CallableFailure (..))
import Phil.Core.Static
  ( DeclarationKey (..)
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Outcome (..)
  , Ty (..)
  )
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , CallableOutcomeControlSpec (..)
  , CallableOutcomeResourceBinding (..)
  , CallableOutcomeResourceSpec (..)
  , CallableOutcomeSpec (..)
  , SurfaceEnvironment (..)
  , SurfaceShape (..)
  , emptySurfaceEnvironment
  )
import Phil.Surface.Syntax
  ( SourcePoint (..)
  , SourceSpan (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-019 installs exact occurrence-scoped neutral resource residue"
        exactInstallation
    , test "CALL-019 resource installation erases semantic state and lifecycle keys"
        semanticKeysDoNotCrossSurfaceBoundary
    , test "CALL-019 terminal branch installs no caller resource residue"
        terminalBranchStaysAbsent
    , test "CALL-019 identical resource reinstall is idempotent"
        identicalReinstallIsIdempotent
    , test "CALL-019 conflicting resource reinstall rejects"
        conflictingReinstallRejects
    , test "CALL-019 resource installer rejects dispatch control substitution"
        controlSubstitutionRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

workerKey :: DeclarationKey
workerKey = DeclarationKey "decl.worker"

invocationSpan :: SourceSpan
invocationSpan = spanAt "call019-resource-install" 1 10

spanAt :: Text -> Int -> Int -> SourceSpan
spanAt file line offset = SourceSpan
  (SourcePoint file line 1 offset)
  (SourcePoint file line 2 (offset + 1))

successState, retryState, haltState :: CallableOutcomeState
successState = CallableOutcomeState "state.success"
retryState = CallableOutcomeState "state.retry"
haltState = CallableOutcomeState "state.halt"

haltOutcome :: Outcome
haltOutcome = Outcome "halt"

successContract, retryContract, haltContract :: CallableOutcomeContract
successContract = contract CallableSuccessOutcome successState
retryContract = contract
  (CallableNonSuccessOutcome (CallableTypedNegative (Outcome "retry")))
  retryState
haltContract = contract
  (CallableNonSuccessOutcome (CallableDeclaredTerminal haltOutcome))
  haltState

contract :: CallableOutcomeClass -> CallableOutcomeState -> CallableOutcomeContract
contract outcomeClass outcomeState = CallableOutcomeContract
  { callableOutcomeClass = outcomeClass
  , callableOutcomeState = outcomeState
  , callableOutcomeCalleeTransition = PreserveCallee
  , callableOutcomePostconditions = Set.empty
  , callableOutcomeResidualObligations = Set.empty
  , callableOutcomeAssumptions = Set.empty
  , callableOutcomeEffects = Set.empty
  , callableOutcomeDischargedFacts = Set.empty
  }

continuations :: [SurfaceCallableOutcomeContinuation]
continuations =
  [ continuation "ok" 2 SurfaceCallableOutcomeCallerContinues successContract
  , continuation "retry" 3 SurfaceCallableOutcomeCallerContinues retryContract
  , continuation "halt" 4 (SurfaceCallableOutcomeCallerTerminates haltOutcome) haltContract
  ]

continuation
  :: Text
  -> Int
  -> SurfaceCallableOutcomeContinuationDisposition
  -> CallableOutcomeContract
  -> SurfaceCallableOutcomeContinuation
continuation label line disposition outcomeContract =
  SurfaceCallableOutcomeContinuation
    { surfaceContinuationInvocationSpan = invocationSpan
    , surfaceContinuationArmSpan = spanAt "call019-resource-install" line (line * 10)
    , surfaceContinuationDeclarationKey = workerKey
    , surfaceContinuationSourceLabel = label
    , surfaceContinuationPayload = []
    , surfaceContinuationOutcomeClass = callableOutcomeClass outcomeContract
    , surfaceContinuationDisposition = disposition
    , surfaceContinuationState = callableOutcomeState outcomeContract
    , surfaceContinuationCalleeTransition =
        callableOutcomeCalleeTransition outcomeContract
    , surfaceContinuationPostconditions = Set.empty
    , surfaceContinuationResidualObligations = Set.empty
    , surfaceContinuationAssumptions = Set.empty
    , surfaceContinuationEffects = Set.empty
    , surfaceContinuationDischargedFacts = Set.empty
    , surfaceContinuationContract = outcomeContract
    }

ownerMeta, endpointMeta :: BindingMeta
ownerMeta = BindingMeta Linear (TyOpaque "Owner") PlainShape
endpointMeta = BindingMeta Linear (TyEndpoint (error "endpoint session is intentionally opaque in installer test")) PlainShape

successBinding, retryBinding :: SurfaceCallableOutcomeResourceResidueBinding
successBinding = resourceBinding
  "ok"
  successState
  (Map.fromList
    [ ("owner", SurfaceCallableResourcePresent ownerMeta)
    , ("scratch", SurfaceCallableResourceAbsent)
    ])
  Nothing
retryBinding = resourceBinding
  "retry"
  retryState
  (Map.singleton "owner" (SurfaceCallableResourcePresent ownerMeta))
  Nothing

resourceBinding
  :: Text
  -> CallableOutcomeState
  -> Map.Map Text SurfaceCallableOutcomeResourceExpectation
  -> Maybe Text
  -> SurfaceCallableOutcomeResourceResidueBinding
resourceBinding label outcomeState bindings active =
  SurfaceCallableOutcomeResourceResidueBinding
    { surfaceOutcomeResourceInvocationSpan = invocationSpan
    , surfaceOutcomeResourceDeclarationKey = workerKey
    , surfaceOutcomeResourceSourceLabel = label
    , surfaceOutcomeResourceState = outcomeState
    , surfaceOutcomeResourceCalleeTransition = PreserveCallee
    , surfaceOutcomeResourceBindings = bindings
    , surfaceOutcomeResourceActiveEndpoint = active
    }

baseEnvironment :: SurfaceEnvironment
baseEnvironment = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceCallableOutcomes = Map.singleton workerKey
      [ outcomeSpec "ok" CallableOutcomeContinues
      , outcomeSpec "retry" CallableOutcomeContinues
      , outcomeSpec "halt" (CallableOutcomeCloses haltOutcome)
      ]
  }

outcomeSpec :: Text -> CallableOutcomeControlSpec -> CallableOutcomeSpec
outcomeSpec label control = CallableOutcomeSpec
  { callableOutcomeLabel = label
  , callableOutcomePayload = []
  , callableOutcomeControl = control
  , callableOutcomeFacts = []
  , callableOutcomeResidualObligationArity = 0
  , callableOutcomeObligations = []
  }

installedEnvironment :: Either String SurfaceEnvironment
installedEnvironment = do
  branchEnvironments <- mapLeft show $
    bindSurfaceCallableOutcomeBranchResources
      [successBinding, retryBinding]
      continuations
  mapLeft show $
    installSurfaceCallableOutcomeBranchResources branchEnvironments baseEnvironment

exactInstallation :: Either String ()
exactInstallation = do
  environment <- installedEnvironment
  let resources = surfaceCallableOutcomeResources environment
      successKey = (invocationSpan, workerKey, "ok")
      retryKey = (invocationSpan, workerKey, "retry")
  assert (Map.size resources == 2)
    "expected exactly two continuing occurrence resource entries"
  success <- maybe (Left "missing success resource entry") Right $
    Map.lookup successKey resources
  retry <- maybe (Left "missing retry resource entry") Right $
    Map.lookup retryKey resources
  assert
    (Map.lookup "owner" (callableOutcomeResourceBindings success)
      == Just (CallableOutcomeResourcePresent ownerMeta))
    "success owner metadata changed during neutral installation"
  assert
    (Map.lookup "scratch" (callableOutcomeResourceBindings success)
      == Just CallableOutcomeResourceAbsent)
    "explicit consumed resource was lost"
  assert
    (Map.lookup "owner" (callableOutcomeResourceBindings retry)
      == Just (CallableOutcomeResourcePresent ownerMeta))
    "retry owner metadata changed"

semanticKeysDoNotCrossSurfaceBoundary :: Either String ()
semanticKeysDoNotCrossSurfaceBoundary = do
  environment <- installedEnvironment
  let rendered = show (surfaceCallableOutcomeResources environment)
  assert (not (contains "state.success" rendered))
    "opaque semantic state crossed into neutral Surface resource table"
  assert (not (contains "PreserveCallee" rendered))
    "callee lifecycle key crossed into neutral Surface resource table"

terminalBranchStaysAbsent :: Either String ()
terminalBranchStaysAbsent = do
  environment <- installedEnvironment
  assert
    (Map.notMember (invocationSpan, workerKey, "halt")
      (surfaceCallableOutcomeResources environment))
    "terminal branch acquired caller-visible resource residue"

identicalReinstallIsIdempotent :: Either String ()
identicalReinstallIsIdempotent = do
  branchEnvironments <- mapLeft show $
    bindSurfaceCallableOutcomeBranchResources [successBinding, retryBinding] continuations
  first <- mapLeft show $
    installSurfaceCallableOutcomeBranchResources branchEnvironments baseEnvironment
  second <- mapLeft show $
    installSurfaceCallableOutcomeBranchResources branchEnvironments first
  assert
    (surfaceCallableOutcomeResources second == surfaceCallableOutcomeResources first)
    "identical reinstall changed occurrence resource table"

conflictingReinstallRejects :: Either String ()
conflictingReinstallRejects = do
  environment <- installedEnvironment
  let key = (invocationSpan, workerKey, "ok")
      poisoned = environment
        { surfaceCallableOutcomeResources = Map.insert key
            (CallableOutcomeResourceSpec Map.empty Nothing)
            (surfaceCallableOutcomeResources environment)
        }
  branchEnvironments <- mapLeft show $
    bindSurfaceCallableOutcomeBranchResources [successBinding, retryBinding] continuations
  case installSurfaceCallableOutcomeBranchResources branchEnvironments poisoned of
    Left (SurfaceCallableOutcomeResourceInstallConflict actualSpan actualKey actualLabel)
      | actualSpan == invocationSpan
          && actualKey == workerKey
          && actualLabel == "ok" -> Right ()
    Left other -> Left ("wrong conflicting-install rejection: " <> show other)
    Right accepted -> Left ("conflicting resource reinstall accepted: " <> show accepted)

controlSubstitutionRejects :: Either String ()
controlSubstitutionRejects = do
  branchEnvironments <- mapLeft show $
    bindSurfaceCallableOutcomeBranchResources [successBinding, retryBinding] continuations
  let poisoned = baseEnvironment
        { surfaceCallableOutcomes = Map.adjust
            (map poisonSuccess)
            workerKey
            (surfaceCallableOutcomes baseEnvironment)
        }
  case installSurfaceCallableOutcomeBranchResources branchEnvironments poisoned of
    Left (SurfaceCallableOutcomeResourceInstallControlMismatch actualKey actualLabel actual)
      | actualKey == workerKey
          && actualLabel == "ok"
          && actual == CallableOutcomeCloses haltOutcome -> Right ()
    Left other -> Left ("wrong control-substitution rejection: " <> show other)
    Right accepted -> Left ("control-substituted dispatch accepted: " <> show accepted)
  where
    poisonSuccess spec
      | callableOutcomeLabel spec == "ok" =
          spec { callableOutcomeControl = CallableOutcomeCloses haltOutcome }
      | otherwise = spec

contains :: String -> String -> Bool
contains needle haystack = any (needle `prefixOf`) (tails haystack)
  where
    prefixOf [] _ = True
    prefixOf _ [] = False
    prefixOf (x : xs) (y : ys) = x == y && prefixOf xs ys
    tails [] = [[]]
    tails value@(_ : rest) = value : tails rest

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
