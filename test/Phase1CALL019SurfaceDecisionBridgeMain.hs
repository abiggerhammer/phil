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
  ( PrimitiveSemantics (..)
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
    [ test "CALL-019 decide invoke uses exact installed callable outcome dispatch"
        exactDispatchChecks
    , test "CALL-019 decide invoke enforces exact branch exhaustiveness"
        missingArmRejects
    , test "CALL-019 decide invoke enforces typed payload binder arity"
        wrongBinderArityRejects
    , test "CALL-019 dispatch installation rejects declaration substitution"
        declarationMismatchRejects
    , test "CALL-019 dispatch installation rejects conflicting reinstallation"
        conflictingReinstallRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

lookupKey, wrongKey :: DeclarationKey
lookupKey = DeclarationKey "decl.lookup"
wrongKey = DeclarationKey "decl.other"

negativeFailure :: CallableFailure
negativeFailure = CallableTypedNegative (Outcome "not-found")

successClass, negativeClass :: CallableOutcomeClass
successClass = CallableSuccessOutcome
negativeClass = CallableNonSuccessOutcome negativeFailure

successOutcome, negativeOutcome :: CallableOutcomeContract
successOutcome = CallableOutcomeContract
  { callableOutcomeClass = successClass
  , callableOutcomeState = CallableOutcomeState "lookup.success"
  , callableOutcomeCalleeTransition = PreserveCallee
  , callableOutcomePostconditions = Set.empty
  , callableOutcomeResidualObligations = Set.empty
  , callableOutcomeAssumptions = Set.empty
  , callableOutcomeEffects = Set.empty
  , callableOutcomeDischargedFacts = Set.empty
  }
negativeOutcome = CallableOutcomeContract
  { callableOutcomeClass = negativeClass
  , callableOutcomeState = CallableOutcomeState "lookup.missing"
  , callableOutcomeCalleeTransition = PreserveCallee
  , callableOutcomePostconditions = Set.empty
  , callableOutcomeResidualObligations = Set.empty
  , callableOutcomeAssumptions = Set.empty
  , callableOutcomeEffects = Set.empty
  , callableOutcomeDischargedFacts = Set.empty
  }

span1 :: SourceSpan
span1 = SourceSpan
  (SourcePoint "call019-surface-decision" 1 1 0)
  (SourcePoint "call019-surface-decision" 1 20 19)

account :: DeclarationKey -> SurfaceCallableInvocationSemanticAccount
account key = SurfaceCallableInvocationSemanticAccount
  { surfaceSemanticInvocationSpan = span1
  , surfaceSemanticInvocationDisplayName = "Lookup"
  , surfaceSemanticInvocationDeclarationKey = key
  , surfaceSemanticInvocationCallerAuthority = Set.empty
  , surfaceSemanticInvocationPublicEffectBound = Set.empty
  , surfaceSemanticInvocationCalleeTransition = PreserveCallee
  , surfaceSemanticInvocationModeledFailures = Set.singleton negativeFailure
  , surfaceSemanticInvocationOutcomes = [successOutcome, negativeOutcome]
  }

bindings :: Map.Map CallableOutcomeClass SurfaceCallableOutcomeBinding
bindings = Map.fromList
  [ (successClass, SurfaceCallableOutcomeBinding
      { surfaceOutcomeBindingClass = successClass
      , surfaceOutcomeBindingLabel = "ok"
      , surfaceOutcomeBindingPayload = [(Linear, TyOpaque "Blob")]
      })
  , (negativeClass, SurfaceCallableOutcomeBinding
      { surfaceOutcomeBindingClass = negativeClass
      , surfaceOutcomeBindingLabel = "missing"
      , surfaceOutcomeBindingPayload = [(Unrestricted, TyOpaque "Reason")]
      })
  ]

baseEnvironment :: SurfaceEnvironment
baseEnvironment = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceCallables = Map.singleton "Lookup" SurfaceCallableSignature
      { surfaceCallableDeclarationKey = lookupKey
      , surfaceCallableParameters = []
      , surfaceCallableResult = Nothing
      }
  , surfacePrimitives = Map.singleton "Use" PrimitiveUse
  }

installedEnvironment :: Either String SurfaceEnvironment
installedEnvironment = do
  plan <- mapLeft show $
    planSurfaceCallableOutcomeDispatch bindings (account lookupKey)
  mapLeft show (installSurfaceCallableOutcomeDispatch plan baseEnvironment)

exactDispatchChecks :: Either String ()
exactDispatchChecks = do
  environment <- installedEnvironment
  component <- parseOne
    "component Caller { decide invoke Lookup() { ok(blob) => { Use(blob) return unit } missing(reason) => { return unit } } }"
  checked <- mapLeft show (checkSurfaceComponent environment component)
  assert
    (checkedTerminalControls checked == [Return TyUnit, Return TyUnit])
    ("unexpected terminal controls: " <> show (checkedTerminalControls checked))

missingArmRejects :: Either String ()
missingArmRejects = do
  environment <- installedEnvironment
  component <- parseOne
    "component Caller { decide invoke Lookup() { ok(blob) => { Use(blob) return unit } } }"
  expectSurfaceError BranchExhaustiveness environment component

wrongBinderArityRejects :: Either String ()
wrongBinderArityRejects = do
  environment <- installedEnvironment
  component <- parseOne
    "component Caller { decide invoke Lookup() { ok => { return unit } missing(reason) => { return unit } } }"
  expectSurfaceError TypeMismatch environment component

declarationMismatchRejects :: Either String ()
declarationMismatchRejects = do
  plan <- mapLeft show $
    planSurfaceCallableOutcomeDispatch bindings (account wrongKey)
  case installSurfaceCallableOutcomeDispatch plan baseEnvironment of
    Left (SurfaceCallableOutcomeDeclarationMismatch expected actual)
      | expected == wrongKey && actual == lookupKey -> Right ()
    Left err -> Left ("unexpected declaration mismatch error: " <> show err)
    Right environment -> Left ("expected declaration mismatch rejection, got " <> show environment)

conflictingReinstallRejects :: Either String ()
conflictingReinstallRejects = do
  environment <- installedEnvironment
  let changedBindings = Map.adjust
        (\binding -> binding { surfaceOutcomeBindingLabel = "found" })
        successClass
        bindings
  changedPlan <- mapLeft show $
    planSurfaceCallableOutcomeDispatch changedBindings (account lookupKey)
  case installSurfaceCallableOutcomeDispatch changedPlan environment of
    Left (SurfaceCallableOutcomeDispatchConflict key)
      | key == lookupKey -> Right ()
    Left err -> Left ("unexpected conflicting dispatch error: " <> show err)
    Right installed -> Left ("expected conflicting dispatch rejection, got " <> show installed)

expectSurfaceError
  :: RejectionClass
  -> SurfaceEnvironment
  -> Located Component
  -> Either String ()
expectSurfaceError expected environment component =
  case checkSurfaceComponent environment component of
    Left err | surfaceErrorClass err == expected -> Right ()
    Left err -> Left ("unexpected surface error: " <> show err)
    Right checked -> Left ("expected rejection, got " <> show checked)

parseOne :: Text -> Either String (Located Component)
parseOne source = do
  parsed <- mapLeft show (parseSurfaceFile "call019-surface-decision" source)
  case surfaceComponents parsed of
    [component] -> Right component
    components -> Left ("expected one component, got " <> show (length components))

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
