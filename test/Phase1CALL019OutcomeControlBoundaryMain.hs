{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Compiler.CallableInvocationSemantics
  ( SurfaceCallableInvocationSemanticAccount (..)
  )
import Phil.Compiler.CallableOutcomeDispatch
  ( SurfaceCallableOutcomeBinding (..)
  , SurfaceCallableOutcomeControl (..)
  , SurfaceCallableOutcomeDispatchError (..)
  , installSurfaceCallableOutcomeDispatch
  , planSurfaceCallableOutcomeDispatch
  )
import Phil.Core.Callable
  ( CalleeTransition (..)
  )
import Phil.Core.CallableOutcome
  ( CallableOutcomeClass (..)
  , CallableOutcomeContract (..)
  , CallableOutcomeState (..)
  )
import Phil.Core.CallableRefinement
  ( CallableFailure (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Control (..)
  , Mode (..)
  , Outcome (..)
  , Ty (..)
  )
import Phil.Surface.Check
  ( CallableOutcomeControlSpec (..)
  , RejectionClass (..)
  , SurfaceCallableSignature (..)
  , SurfaceCheckError (..)
  , SurfaceCheckResult (..)
  , SurfaceEnvironment (..)
  , checkSurfaceComponent
  , emptySurfaceEnvironment
  )
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Syntax
  ( Component
  , Located
  , SourcePoint (..)
  , SourceSpan (..)
  , SurfaceFile (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-019 continuing outcomes remain surface-representable"
        continuingOutcomesInstall
    , test "CALL-019 declared-terminal outcome installs exact close control"
        declaredTerminalInstalls
    , test "CALL-019 decide invoke closes exact declared-terminal branch"
        declaredTerminalCloses
    , test "CALL-019 declared-terminal arm cannot contain continuation statements"
        declaredTerminalBodyRejects
    , test "CALL-019 declared-terminal arm cannot bind a caller payload"
        declaredTerminalBinderRejects
    , test "CALL-019 declared-terminal contract cannot expose a payload telescope"
        declaredTerminalPayloadRejects
    , test "CALL-019 fatal outcome remains fail-closed without exact Core fatal control"
        fatalRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

workerKey :: DeclarationKey
workerKey = DeclarationKey "decl.worker"

span1 :: SourceSpan
span1 = SourceSpan
  (SourcePoint "call019-outcome-control" 1 1 0)
  (SourcePoint "call019-outcome-control" 1 20 19)

successClass :: CallableOutcomeClass
successClass = CallableSuccessOutcome

typedFailure, terminalFailure, fatalFailure :: CallableFailure
typedFailure = CallableTypedNegative (Outcome "retry")
terminalFailure = CallableDeclaredTerminal (Outcome "closed")
fatalFailure = CallableFatal "fatal:worker"

typedClass, terminalClass, fatalClass :: CallableOutcomeClass
typedClass = CallableNonSuccessOutcome typedFailure
terminalClass = CallableNonSuccessOutcome terminalFailure
fatalClass = CallableNonSuccessOutcome fatalFailure

outcome :: Text -> CallableOutcomeClass -> CallableOutcomeContract
outcome stateName outcomeClass = CallableOutcomeContract
  { callableOutcomeClass = outcomeClass
  , callableOutcomeState = CallableOutcomeState stateName
  , callableOutcomeCalleeTransition = PreserveCallee
  , callableOutcomePostconditions = Set.empty
  , callableOutcomeResidualObligations = Set.empty
  , callableOutcomeAssumptions = Set.empty
  , callableOutcomeEffects = Set.empty
  , callableOutcomeDischargedFacts = Set.empty
  }

account :: [CallableOutcomeContract] -> SurfaceCallableInvocationSemanticAccount
account outcomes = SurfaceCallableInvocationSemanticAccount
  { surfaceSemanticInvocationSpan = span1
  , surfaceSemanticInvocationDisplayName = "Worker"
  , surfaceSemanticInvocationDeclarationKey = workerKey
  , surfaceSemanticInvocationCallerAuthority = Set.empty
  , surfaceSemanticInvocationPublicEffectBound = Set.empty
  , surfaceSemanticInvocationCalleeTransition = PreserveCallee
  , surfaceSemanticInvocationModeledFailures = Set.fromList
      [ failure
      | CallableOutcomeContract
          { callableOutcomeClass = CallableNonSuccessOutcome failure } <- outcomes
      ]
  , surfaceSemanticInvocationOutcomes = outcomes
  }

binding :: CallableOutcomeClass -> Text -> SurfaceCallableOutcomeBinding
binding outcomeClass label = SurfaceCallableOutcomeBinding
  { surfaceOutcomeBindingClass = outcomeClass
  , surfaceOutcomeBindingLabel = label
  , surfaceOutcomeBindingPayload = []
  }

environment :: SurfaceEnvironment
environment = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceCallables = Map.singleton "Worker" SurfaceCallableSignature
      { surfaceCallableDeclarationKey = workerKey
      , surfaceCallableParameters = []
      , surfaceCallableResult = Nothing
      }
  }

continuingOutcomesInstall :: Either String ()
continuingOutcomesInstall = do
  let outcomes = [outcome "success" successClass, outcome "retry" typedClass]
      bindings = Map.fromList
        [ (successClass, binding successClass "ok")
        , (typedClass, binding typedClass "retry")
        ]
  plan <- mapLeft show (planSurfaceCallableOutcomeDispatch bindings (account outcomes))
  installed <- mapLeft show (installSurfaceCallableOutcomeDispatch plan environment)
  case Map.lookup workerKey (surfaceCallableOutcomes installed) of
    Just specs
      | length specs == 2 -> Right ()
      | otherwise -> Left ("unexpected installed outcome count: " <> show (length specs))
    Nothing -> Left "continuing outcome dispatch was not installed"

declaredTerminalPlan
  :: Either String SurfaceEnvironment
declaredTerminalPlan = do
  let outcomes = [outcome "success" successClass, outcome "closed" terminalClass]
      bindings = Map.fromList
        [ (successClass, binding successClass "ok")
        , (terminalClass, binding terminalClass "closed")
        ]
  plan <- mapLeft show (planSurfaceCallableOutcomeDispatch bindings (account outcomes))
  mapLeft show (installSurfaceCallableOutcomeDispatch plan environment)

declaredTerminalInstalls :: Either String ()
declaredTerminalInstalls = do
  installed <- declaredTerminalPlan
  case Map.lookup workerKey (surfaceCallableOutcomes installed) of
    Just [successSpec, terminalSpec]
      | callableOutcomeControl successSpec == CallableOutcomeContinues
          && callableOutcomeControl terminalSpec
            == CallableOutcomeCloses (Outcome "closed") -> Right ()
      | otherwise -> Left
          ("wrong installed controls: "
            <> show (callableOutcomeControl successSpec, callableOutcomeControl terminalSpec))
    other -> Left ("unexpected installed outcomes: " <> show other)

declaredTerminalCloses :: Either String ()
declaredTerminalCloses = do
  installed <- declaredTerminalPlan
  component <- parseOne
    "component Caller { decide invoke Worker() { ok => { return unit } closed => { } } }"
  checked <- mapLeft show (checkSurfaceComponent installed component)
  assert
    (checkedTerminalControls checked == [Return TyUnit, Closed (Outcome "closed")])
    ("unexpected terminal controls: " <> show (checkedTerminalControls checked))

declaredTerminalBodyRejects :: Either String ()
declaredTerminalBodyRejects = do
  installed <- declaredTerminalPlan
  component <- parseOne
    "component Caller { decide invoke Worker() { ok => { return unit } closed => { return unit } } }"
  expectSurfaceError ControlAfterTerminal installed component

declaredTerminalBinderRejects :: Either String ()
declaredTerminalBinderRejects = do
  installed <- declaredTerminalPlan
  component <- parseOne
    "component Caller { decide invoke Worker() { ok => { return unit } closed(reason) => { } } }"
  expectSurfaceError TypeMismatch installed component

declaredTerminalPayloadRejects :: Either String ()
declaredTerminalPayloadRejects = do
  let outcomes = [outcome "success" successClass, outcome "closed" terminalClass]
      terminalBinding = (binding terminalClass "closed")
        { surfaceOutcomeBindingPayload = [(Unrestricted, TyOpaque "Never")]
        }
      bindings = Map.fromList
        [ (successClass, binding successClass "ok")
        , (terminalClass, terminalBinding)
        ]
  plan <- mapLeft show (planSurfaceCallableOutcomeDispatch bindings (account outcomes))
  case installSurfaceCallableOutcomeDispatch plan environment of
    Left (SurfaceCallableTerminalOutcomePayloadUnsupported actual)
      | actual == terminalClass -> Right ()
    Left other -> Left ("wrong terminal payload rejection: " <> show other)
    Right installed -> Left ("terminal payload was accepted: " <> show installed)

fatalRejects :: Either String ()
fatalRejects = do
  let outcomes = [outcome "success" successClass, outcome "fatal" fatalClass]
      bindings = Map.fromList
        [ (successClass, binding successClass "ok")
        , (fatalClass, binding fatalClass "fatal")
        ]
  plan <- mapLeft show (planSurfaceCallableOutcomeDispatch bindings (account outcomes))
  expectControlError
    fatalClass
    SurfaceCallableOutcomeFatalTerminal
    (installSurfaceCallableOutcomeDispatch plan environment)

expectControlError
  :: CallableOutcomeClass
  -> SurfaceCallableOutcomeControl
  -> Either SurfaceCallableOutcomeDispatchError SurfaceEnvironment
  -> Either String ()
expectControlError expectedClass expectedControl result = case result of
  Left (SurfaceCallableOutcomeControlRequiresSurfaceRepresentation
      actualClass actualControl)
    | actualClass == expectedClass && actualControl == expectedControl -> Right ()
    | otherwise -> Left
        ("wrong control rejection: " <> show (actualClass, actualControl))
  Left other -> Left ("wrong rejection: " <> show other)
  Right _ -> Left "fatal callable outcome was accepted without exact Surface/Core control"

expectSurfaceError
  :: RejectionClass
  -> SurfaceEnvironment
  -> Located Component
  -> Either String ()
expectSurfaceError expected env component =
  case checkSurfaceComponent env component of
    Left err | surfaceErrorClass err == expected -> Right ()
    Left err -> Left ("unexpected surface error: " <> show err)
    Right checked -> Left ("expected rejection, got " <> show checked)

parseOne :: Text -> Either String (Located Component)
parseOne source = do
  parsed <- mapLeft show (parseSurfaceFile "call019-outcome-control" source)
  case surfaceComponents parsed of
    [component] -> Right component
    components -> Left ("expected one component, got " <> show (length components))

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
