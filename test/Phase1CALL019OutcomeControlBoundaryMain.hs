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
  ( Outcome (..)
  )
import Phil.Surface.Check
  ( CallableOutcomeControlSpec (..)
  , CallableOutcomeSpec (..)
  , SurfaceCallableSignature (..)
  , SurfaceEnvironment (..)
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
    [ test "CALL-019 continuing outcomes remain surface-representable"
        continuingOutcomesInstall
    , test "CALL-019 declared-terminal outcome installs exact close control"
        declaredTerminalInstalls
    , test "CALL-019 fatal outcome rejects before Surface installation"
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

declaredTerminalInstalls :: Either String ()
declaredTerminalInstalls = do
  let outcomes = [outcome "success" successClass, outcome "closed" terminalClass]
      bindings = Map.fromList
        [ (successClass, binding successClass "ok")
        , (terminalClass, binding terminalClass "closed")
        ]
  plan <- mapLeft show (planSurfaceCallableOutcomeDispatch bindings (account outcomes))
  installed <- mapLeft show (installSurfaceCallableOutcomeDispatch plan environment)
  case Map.lookup workerKey (surfaceCallableOutcomes installed) of
    Just [successSpec, terminalSpec]
      | callableOutcomeControl successSpec == CallableOutcomeContinues
          && callableOutcomeControl terminalSpec
            == CallableOutcomeCloses (Outcome "closed") -> Right ()
      | otherwise -> Left
          ("wrong installed controls: "
            <> show (callableOutcomeControl successSpec, callableOutcomeControl terminalSpec))
    other -> Left ("unexpected installed outcomes: " <> show other)

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
  Right _ -> Left "terminal callable outcome was accepted by neutral Surface dispatch"

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
