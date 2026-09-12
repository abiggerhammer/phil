{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Compiler.CallableInvocationSemantics
  ( SurfaceCallableInvocationSemanticAccount (..)
  )
import Phil.Compiler.CallableOutcomeBranchSemantics
  ( SurfaceCallableOutcomeArmSemanticWitness (..)
  , SurfaceCallableOutcomeBranchSemanticError (..)
  , bindSurfaceCallableOutcomeDecision
  )
import Phil.Compiler.CallableOutcomeDispatch
  ( SurfaceCallableOutcomeBinding (..)
  , SurfaceCallableOutcomeControl (..)
  , SurfaceCallableOutcomeDispatchPlan
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
  ( Mode (..)
  , Outcome (..)
  , Ty (..)
  )
import Phil.Surface.Check
  ( SurfaceCallableSignature (..)
  , SurfaceEnvironment (..)
  , checkSurfaceComponent
  , emptySurfaceEnvironment
  )
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Syntax
  ( Block (..)
  , Component (..)
  , Located (..)
  , SourcePoint (..)
  , SourceSpan (..)
  , Statement (..)
  , SurfaceExpression (..)
  , SurfaceFile (..)
  , pattern InvokeExpression
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-019 source arms retain exact branch-local semantic contracts"
        exactArmWitnesses
    , test "CALL-019 branch witness rejects missing source outcome arm"
        missingArmRejects
    , test "CALL-019 branch witness rejects neutral dispatch substitution"
        neutralDispatchSubstitutionRejects
    , test "CALL-019 branch witness rejects declaration substitution"
        declarationSubstitutionRejects
    , test "CALL-019 branch witness rejects invocation-span substitution"
        invocationSpanSubstitutionRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

workerKey, wrongKey :: DeclarationKey
workerKey = DeclarationKey "decl.worker"
wrongKey = DeclarationKey "decl.other"

successClass :: CallableOutcomeClass
successClass = CallableSuccessOutcome

typedFailure, terminalFailure :: CallableFailure
typedFailure = CallableTypedNegative (Outcome "retry")
terminalFailure = CallableDeclaredTerminal (Outcome "closed")

typedClass, terminalClass :: CallableOutcomeClass
typedClass = CallableNonSuccessOutcome typedFailure
terminalClass = CallableNonSuccessOutcome terminalFailure

successOutcome, typedOutcome, terminalOutcome :: CallableOutcomeContract
successOutcome = outcome "success" successClass
typedOutcome = outcome "retry" typedClass
terminalOutcome = outcome "closed" terminalClass

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

account :: SourceSpan -> SurfaceCallableInvocationSemanticAccount
account invocationSpan = SurfaceCallableInvocationSemanticAccount
  { surfaceSemanticInvocationSpan = invocationSpan
  , surfaceSemanticInvocationDisplayName = "Worker"
  , surfaceSemanticInvocationDeclarationKey = workerKey
  , surfaceSemanticInvocationCallerAuthority = Set.empty
  , surfaceSemanticInvocationPublicEffectBound = Set.empty
  , surfaceSemanticInvocationCalleeTransition = PreserveCallee
  , surfaceSemanticInvocationModeledFailures = Set.fromList
      [typedFailure, terminalFailure]
  , surfaceSemanticInvocationOutcomes =
      [successOutcome, typedOutcome, terminalOutcome]
  }

bindings :: Map.Map CallableOutcomeClass SurfaceCallableOutcomeBinding
bindings = Map.fromList
  [ (successClass, binding successClass "ok" [])
  , (typedClass, binding typedClass "retry" [(Unrestricted, TyOpaque "Reason")])
  , (terminalClass, binding terminalClass "closed" [])
  ]

binding
  :: CallableOutcomeClass
  -> Text
  -> [(Mode, Ty)]
  -> SurfaceCallableOutcomeBinding
binding outcomeClass label payload = SurfaceCallableOutcomeBinding
  { surfaceOutcomeBindingClass = outcomeClass
  , surfaceOutcomeBindingLabel = label
  , surfaceOutcomeBindingPayload = payload
  }

baseEnvironment :: SurfaceEnvironment
baseEnvironment = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceCallables = Map.singleton "Worker" workerSignature
  }

workerSignature :: SurfaceCallableSignature
workerSignature = SurfaceCallableSignature
  { surfaceCallableDeclarationKey = workerKey
  , surfaceCallableParameters = []
  , surfaceCallableResult = Nothing
  }

source :: Text
source =
  "component Caller { decide invoke Worker() { retry(reason) => { return unit } closed => { } ok => { return unit } } }"

prepare
  :: Text
  -> Either String
       ( Located Component
       , Located SurfaceExpression
       , SurfaceCallableOutcomeDispatchPlan
       , SurfaceEnvironment
       )
prepare sourceText = do
  component <- parseOne sourceText
  decision <- decisionExpression component
  invocationSpan <- directInvokeSpan decision
  plan <- mapLeft show (planSurfaceCallableOutcomeDispatch bindings (account invocationSpan))
  installed <- mapLeft show (installSurfaceCallableOutcomeDispatch plan baseEnvironment)
  _ <- mapLeft show (checkSurfaceComponent installed component)
  Right (component, decision, plan, installed)

exactArmWitnesses :: Either String ()
exactArmWitnesses = do
  (_, decision, plan, installed) <- prepare source
  witnesses <- mapLeft show (bindSurfaceCallableOutcomeDecision installed plan decision)
  assert
    (map surfaceOutcomeArmSourceLabel witnesses == ["retry", "closed", "ok"])
    ("source arm order changed: " <> show (map surfaceOutcomeArmSourceLabel witnesses))
  case witnesses of
    [retryWitness, closedWitness, okWitness] -> do
      assert
        (surfaceOutcomeArmDeclarationKey retryWitness == workerKey
          && surfaceOutcomeArmDeclarationKey closedWitness == workerKey
          && surfaceOutcomeArmDeclarationKey okWitness == workerKey)
        "exact declaration identity was not retained on every arm"
      assert
        (surfaceOutcomeArmContract retryWitness == typedOutcome
          && surfaceOutcomeArmContract closedWitness == terminalOutcome
          && surfaceOutcomeArmContract okWitness == successOutcome)
        "complete semantic outcome contracts were substituted or reordered"
      assert
        (surfaceOutcomeArmControl retryWitness == SurfaceCallableOutcomeContinues
          && surfaceOutcomeArmControl closedWitness
            == SurfaceCallableOutcomeDeclaredTerminal
          && surfaceOutcomeArmControl okWitness == SurfaceCallableOutcomeContinues)
        "branch-local control classification changed"
      assert
        (surfaceOutcomeArmPayload retryWitness == [(Unrestricted, TyOpaque "Reason")]
          && null (surfaceOutcomeArmPayload closedWitness)
          && null (surfaceOutcomeArmPayload okWitness))
        "source payload telescope did not remain paired with its semantic outcome"
    other -> Left ("unexpected witness count: " <> show (length other))

missingArmRejects :: Either String ()
missingArmRejects = do
  component <- parseOne
    "component Caller { decide invoke Worker() { retry(reason) => { return unit } ok => { return unit } } }"
  decision <- decisionExpression component
  invocationSpan <- directInvokeSpan decision
  plan <- mapLeft show (planSurfaceCallableOutcomeDispatch bindings (account invocationSpan))
  installed <- mapLeft show (installSurfaceCallableOutcomeDispatch plan baseEnvironment)
  case bindSurfaceCallableOutcomeDecision installed plan decision of
    Left (SurfaceCallableOutcomeArmDomainMismatch expected actual)
      | expected == Set.fromList ["ok", "retry", "closed"]
          && actual == Set.fromList ["ok", "retry"] -> Right ()
    Left other -> Left ("wrong missing-arm rejection: " <> show other)
    Right witnesses -> Left ("missing source arm accepted: " <> show witnesses)

neutralDispatchSubstitutionRejects :: Either String ()
neutralDispatchSubstitutionRejects = do
  (_, decision, plan, installed) <- prepare source
  specs <- maybe
    (Left "installed neutral dispatch disappeared")
    Right
    (Map.lookup workerKey (surfaceCallableOutcomes installed))
  let substituted = installed
        { surfaceCallableOutcomes = Map.insert workerKey (reverse specs)
            (surfaceCallableOutcomes installed)
        }
  case bindSurfaceCallableOutcomeDecision substituted plan decision of
    Left (SurfaceCallableOutcomeNeutralDispatchMismatch key)
      | key == workerKey -> Right ()
    Left other -> Left ("wrong neutral-substitution rejection: " <> show other)
    Right witnesses -> Left ("neutral dispatch substitution accepted: " <> show witnesses)

declarationSubstitutionRejects :: Either String ()
declarationSubstitutionRejects = do
  (_, decision, plan, installed) <- prepare source
  let substitutedSignature = workerSignature
        { surfaceCallableDeclarationKey = wrongKey }
      substituted = installed
        { surfaceCallables = Map.singleton "Worker" substitutedSignature
        }
  case bindSurfaceCallableOutcomeDecision substituted plan decision of
    Left (SurfaceCallableOutcomeDeclarationMismatch expected actual)
      | expected == workerKey && actual == wrongKey -> Right ()
    Left other -> Left ("wrong declaration-substitution rejection: " <> show other)
    Right witnesses -> Left ("declaration substitution accepted: " <> show witnesses)

invocationSpanSubstitutionRejects :: Either String ()
invocationSpanSubstitutionRejects = do
  (_, decision, _, installed) <- prepare source
  let wrongSpan = SourceSpan
        (SourcePoint "wrong" 1 1 0)
        (SourcePoint "wrong" 1 2 1)
  wrongPlan <- mapLeft show
    (planSurfaceCallableOutcomeDispatch bindings (account wrongSpan))
  case bindSurfaceCallableOutcomeDecision installed wrongPlan decision of
    Left (SurfaceCallableOutcomeInvocationSpanMismatch expected actual)
      | expected == wrongSpan && actual /= wrongSpan -> Right ()
    Left other -> Left ("wrong span-substitution rejection: " <> show other)
    Right witnesses -> Left ("invocation-span substitution accepted: " <> show witnesses)

decisionExpression :: Located Component -> Either String (Located SurfaceExpression)
decisionExpression component =
  case blockStatements (locatedValue (componentBody (locatedValue component))) of
    [statement] -> case locatedValue statement of
      ExpressionStatement expression -> case locatedValue expression of
        DecideExpression {} -> Right expression
        _ -> Left "component statement was not a decide expression"
      _ -> Left "component statement was not an expression statement"
    statements -> Left ("expected one component statement, got " <> show (length statements))

directInvokeSpan :: Located SurfaceExpression -> Either String SourceSpan
directInvokeSpan decision = case locatedValue decision of
  DecideExpression scrutinee _ -> case locatedValue scrutinee of
    InvokeExpression _ _ -> Right (locatedSpan scrutinee)
    _ -> Left "decision scrutinee was not direct invoke"
  _ -> Left "not a decision expression"

parseOne :: Text -> Either String (Located Component)
parseOne sourceText = do
  parsed <- mapLeft show (parseSurfaceFile "call019-branch-semantic-witness" sourceText)
  case surfaceComponents parsed of
    [component] -> Right component
    components -> Left ("expected one component, got " <> show (length components))

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
