{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Compiler.CallableInvocationSemantics
  ( SurfaceCallableInvocationSemanticAccount (..)
  )
import Phil.Compiler.CallableOutcomeBranchFacts
  ( SurfaceCallableOutcomeBranchFactError (..)
  , SurfaceCallableOutcomeFactBinding (..)
  , bindSurfaceCallableOutcomeBranchFacts
  , installSurfaceCallableOutcomeBranchFacts
  )
import Phil.Compiler.CallableOutcomeContinuation
  ( SurfaceCallableOutcomeContinuation (..)
  , SurfaceCallableOutcomeContinuationDisposition (..)
  )
import Phil.Compiler.CallableOutcomeDispatch
  ( SurfaceCallableOutcomeBinding (..)
  , installSurfaceCallableOutcomeDispatch
  , planSurfaceCallableOutcomeDispatch
  )
import Phil.Core.Callable (CalleeTransition (..))
import Phil.Core.CallableOutcome
  ( CallableOutcomeAtom (..)
  , CallableOutcomeClass (..)
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
  , Proposition (..)
  )
import Phil.Surface.Check
  ( CallableOutcomeSpec (..)
  , SurfaceCallableSignature (..)
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
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-019 exact occurrence facts reach matching Surface arms"
        exactFactsReachArmBodies
    , test "CALL-019 arm facts are unavailable before compiler installation"
        factsUnavailableBeforeInstall
    , test "CALL-019 sibling outcome facts do not leak"
        siblingFactsDoNotLeak
    , test "CALL-019 invocation span participates in fact lookup"
        wrongOccurrenceDoesNotBind
    , test "CALL-019 declaration dispatch stays occurrence-neutral"
        declarationDispatchStaysNeutral
    , test "CALL-019 conflicting occurrence fact reinstall rejects"
        conflictingOccurrenceInstallRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

workerKey :: DeclarationKey
workerKey = DeclarationKey "decl.worker"

successClass, retryClass :: CallableOutcomeClass
successClass = CallableSuccessOutcome
retryClass = CallableNonSuccessOutcome retryFailure

retryFailure :: CallableFailure
retryFailure = CallableTypedNegative (Outcome "retry")

atom :: Text -> CallableOutcomeAtom
atom = CallableOutcomeAtom

okPost, okAssume, okFact, retryPost :: CallableOutcomeAtom
okPost = atom "semantic.ok.post"
okAssume = atom "semantic.ok.assume"
okFact = atom "semantic.ok.fact"
retryPost = atom "semantic.retry.post"

successContract, retryContract :: CallableOutcomeContract
successContract = CallableOutcomeContract
  { callableOutcomeClass = successClass
  , callableOutcomeState = CallableOutcomeState "success"
  , callableOutcomeCalleeTransition = PreserveCallee
  , callableOutcomePostconditions = Set.singleton okPost
  , callableOutcomeResidualObligations = Set.empty
  , callableOutcomeAssumptions = Set.singleton okAssume
  , callableOutcomeEffects = Set.empty
  , callableOutcomeDischargedFacts = Set.singleton okFact
  }
retryContract = CallableOutcomeContract
  { callableOutcomeClass = retryClass
  , callableOutcomeState = CallableOutcomeState "retry"
  , callableOutcomeCalleeTransition = PreserveCallee
  , callableOutcomePostconditions = Set.singleton retryPost
  , callableOutcomeResidualObligations = Set.empty
  , callableOutcomeAssumptions = Set.empty
  , callableOutcomeEffects = Set.empty
  , callableOutcomeDischargedFacts = Set.empty
  }

baseEnvironment :: SurfaceEnvironment
baseEnvironment = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceCallables = Map.singleton "Worker" SurfaceCallableSignature
      { surfaceCallableDeclarationKey = workerKey
      , surfaceCallableParameters = []
      , surfaceCallableResult = Nothing
      }
  }

dispatchBinding :: CallableOutcomeClass -> Text -> SurfaceCallableOutcomeBinding
dispatchBinding outcomeClass label = SurfaceCallableOutcomeBinding
  { surfaceOutcomeBindingClass = outcomeClass
  , surfaceOutcomeBindingLabel = label
  , surfaceOutcomeBindingPayload = []
  }

account :: SourceSpan -> SurfaceCallableInvocationSemanticAccount
account invocationSpan = SurfaceCallableInvocationSemanticAccount
  { surfaceSemanticInvocationSpan = invocationSpan
  , surfaceSemanticInvocationDisplayName = "Worker"
  , surfaceSemanticInvocationDeclarationKey = workerKey
  , surfaceSemanticInvocationCallerAuthority = Set.empty
  , surfaceSemanticInvocationPublicEffectBound = Set.empty
  , surfaceSemanticInvocationCalleeTransition = PreserveCallee
  , surfaceSemanticInvocationModeledFailures = Set.singleton retryFailure
  , surfaceSemanticInvocationOutcomes = [successContract, retryContract]
  }

dispatchEnvironment :: SourceSpan -> Either String SurfaceEnvironment
dispatchEnvironment invocationSpan = do
  let bindings = Map.fromList
        [ (successClass, dispatchBinding successClass "ok")
        , (retryClass, dispatchBinding retryClass "retry")
        ]
  plan <- mapLeft show
    (planSurfaceCallableOutcomeDispatch bindings (account invocationSpan))
  mapLeft show (installSurfaceCallableOutcomeDispatch plan baseEnvironment)

continuation
  :: SourceSpan
  -> Text
  -> CallableOutcomeContract
  -> SurfaceCallableOutcomeContinuation
continuation invocationSpan label outcomeContract =
  SurfaceCallableOutcomeContinuation
    { surfaceContinuationInvocationSpan = invocationSpan
    , surfaceContinuationArmSpan = invocationSpan
    , surfaceContinuationDeclarationKey = workerKey
    , surfaceContinuationSourceLabel = label
    , surfaceContinuationPayload = []
    , surfaceContinuationOutcomeClass = callableOutcomeClass outcomeContract
    , surfaceContinuationDisposition = SurfaceCallableOutcomeCallerContinues
    , surfaceContinuationState = callableOutcomeState outcomeContract
    , surfaceContinuationCalleeTransition = callableOutcomeCalleeTransition outcomeContract
    , surfaceContinuationPostconditions = callableOutcomePostconditions outcomeContract
    , surfaceContinuationResidualObligations = callableOutcomeResidualObligations outcomeContract
    , surfaceContinuationAssumptions = callableOutcomeAssumptions outcomeContract
    , surfaceContinuationEffects = callableOutcomeEffects outcomeContract
    , surfaceContinuationDischargedFacts = callableOutcomeDischargedFacts outcomeContract
    , surfaceContinuationContract = outcomeContract
    }

explicitFactBindings :: Map.Map CallableOutcomeAtom SurfaceCallableOutcomeFactBinding
explicitFactBindings = Map.fromList
  [ (okPost, factBinding okPost "ok_post" "OkPost")
  , (okAssume, factBinding okAssume "ok_assume" "OkAssume")
  , (okFact, factBinding okFact "ok_fact" "OkFact")
  , (retryPost, factBinding retryPost "retry_post" "RetryPost")
  ]

factBinding
  :: CallableOutcomeAtom
  -> Text
  -> Text
  -> SurfaceCallableOutcomeFactBinding
factBinding semanticAtom evidenceName propositionName = SurfaceCallableOutcomeFactBinding
  { surfaceOutcomeFactAtom = semanticAtom
  , surfaceOutcomeFactEvidenceName = evidenceName
  , surfaceOutcomeFactProposition = Atom propositionName []
  }

installFactsFor
  :: SourceSpan
  -> SurfaceEnvironment
  -> Either String SurfaceEnvironment
installFactsFor invocationSpan environment = do
  branchFacts <- mapLeft show $
    bindSurfaceCallableOutcomeBranchFacts
      explicitFactBindings
      [ continuation invocationSpan "ok" successContract
      , continuation invocationSpan "retry" retryContract
      ]
  mapLeft show (installSurfaceCallableOutcomeBranchFacts branchFacts environment)

validSource :: Text
validSource =
  "component Caller { decide invoke Worker() { "
    <> "ok => { let a = ok_post let b = ok_assume let c = ok_fact return unit } "
    <> "retry => { let d = retry_post return unit } } }"

leakingSource :: Text
leakingSource =
  "component Caller { decide invoke Worker() { "
    <> "ok => { let a = ok_post return unit } "
    <> "retry => { let d = ok_post return unit } } }"

exactFactsReachArmBodies :: Either String ()
exactFactsReachArmBodies = do
  component <- parseOne validSource
  invocationSpan <- invocationSpanOf component
  dispatched <- dispatchEnvironment invocationSpan
  installed <- installFactsFor invocationSpan dispatched
  _ <- mapLeft show (checkSurfaceComponent installed component)
  Right ()

factsUnavailableBeforeInstall :: Either String ()
factsUnavailableBeforeInstall = do
  component <- parseOne validSource
  invocationSpan <- invocationSpanOf component
  dispatched <- dispatchEnvironment invocationSpan
  case checkSurfaceComponent dispatched component of
    Left _ -> Right ()
    Right checked -> Left
      ("branch-local fact was visible before installation: " <> show checked)

siblingFactsDoNotLeak :: Either String ()
siblingFactsDoNotLeak = do
  component <- parseOne leakingSource
  invocationSpan <- invocationSpanOf component
  dispatched <- dispatchEnvironment invocationSpan
  installed <- installFactsFor invocationSpan dispatched
  case checkSurfaceComponent installed component of
    Left _ -> Right ()
    Right checked -> Left
      ("success-only fact leaked into retry arm: " <> show checked)

wrongOccurrenceDoesNotBind :: Either String ()
wrongOccurrenceDoesNotBind = do
  component <- parseOne validSource
  invocationSpan <- invocationSpanOf component
  dispatched <- dispatchEnvironment invocationSpan
  let wrongSpan = SourceSpan
        (SourcePoint "wrong-occurrence" 9 1 900)
        (SourcePoint "wrong-occurrence" 9 2 901)
  installed <- installFactsFor wrongSpan dispatched
  case checkSurfaceComponent installed component of
    Left _ -> Right ()
    Right checked -> Left
      ("facts from another invocation occurrence became visible: " <> show checked)

declarationDispatchStaysNeutral :: Either String ()
declarationDispatchStaysNeutral = do
  component <- parseOne validSource
  invocationSpan <- invocationSpanOf component
  dispatched <- dispatchEnvironment invocationSpan
  installed <- installFactsFor invocationSpan dispatched
  specs <- maybe
    (Left "callable dispatch disappeared during fact installation")
    Right
    (Map.lookup workerKey (surfaceCallableOutcomes installed))
  assert
    (all (null . callableOutcomeFacts) specs)
    "occurrence facts contaminated declaration-wide outcome specs"
  assert
    (Map.size (surfaceCallableOutcomeFacts installed) == 2)
    "expected one fact entry per continuing source outcome"

conflictingOccurrenceInstallRejects :: Either String ()
conflictingOccurrenceInstallRejects = do
  component <- parseOne validSource
  invocationSpan <- invocationSpanOf component
  dispatched <- dispatchEnvironment invocationSpan
  branchFacts <- mapLeft show $
    bindSurfaceCallableOutcomeBranchFacts
      explicitFactBindings
      [ continuation invocationSpan "ok" successContract
      , continuation invocationSpan "retry" retryContract
      ]
  installed <- mapLeft show
    (installSurfaceCallableOutcomeBranchFacts branchFacts dispatched)
  let key = (invocationSpan, workerKey, "ok")
      poisoned = installed
        { surfaceCallableOutcomeFacts = Map.insert
            key [("wrong", Atom "Wrong" [])]
            (surfaceCallableOutcomeFacts installed)
        }
  case installSurfaceCallableOutcomeBranchFacts branchFacts poisoned of
    Left (SurfaceCallableOutcomeFactInstallConflict actualSpan actualKey actualLabel)
      | actualSpan == invocationSpan
          && actualKey == workerKey
          && actualLabel == "ok" -> Right ()
    Left other -> Left ("wrong conflict rejection: " <> show other)
    Right accepted -> Left ("conflicting occurrence facts accepted: " <> show accepted)

invocationSpanOf :: Located Component -> Either String SourceSpan
invocationSpanOf locatedComponent =
  case blockStatements (locatedValue (componentBody (locatedValue locatedComponent))) of
    [Located _ (ExpressionStatement decision)] ->
      case locatedValue decision of
        DecideExpression scrutinee _ -> Right (locatedSpan scrutinee)
        other -> Left ("expected decide expression, got " <> show other)
    statements -> Left
      ("expected one decision statement, got " <> show (length statements))

parseOne :: Text -> Either String (Located Component)
parseOne source = do
  parsed <- mapLeft show (parseSurfaceFile "call019-surface-arm-facts" source)
  case surfaceComponents parsed of
    [component] -> Right component
    components -> Left ("expected one component, got " <> show (length components))

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
