{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Compiler.CallableInvocationSemantics
  ( SurfaceCallableInvocationSemanticAccount (..)
  )
import Phil.Compiler.CallableOutcomeBranchResidue
  ( SurfaceCallableOutcomeBranchResidueError (..)
  , SurfaceCallableOutcomeObligationBinding (..)
  , bindSurfaceCallableOutcomeBranchResidue
  , installSurfaceCallableOutcomeBranchResidue
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
import Phil.Core.CallableRefinement (CallableFailure (..))
import Phil.Core.Static
  ( DeclarationKey (..)
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Outcome (..)
  , Proposition (..)
  , Ty (..)
  )
import Phil.Surface.Check
  ( CallableOutcomeSpec (..)
  , InitialBinding (..)
  , RejectionClass (..)
  , SurfaceCheckError (..)
  , SurfaceCallableSignature (..)
  , SurfaceEnvironment (..)
  , SurfaceShape (..)
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
    [ test "CALL-019 exact residual obligations discharge before branch join"
        exactResidualsDischarge
    , test "CALL-019 missing residual binding rejects before installation"
        missingResidualBindingRejects
    , test "CALL-019 missing occurrence installation fails closed"
        missingOccurrenceInstallationRejects
    , test "CALL-019 sibling evidence cannot discharge another outcome"
        siblingEvidenceDoesNotDischarge
    , test "CALL-019 invocation span participates in residual lookup"
        wrongOccurrenceDoesNotInstall
    , test "CALL-019 declaration dispatch retains only neutral residual arity"
        declarationDispatchStaysNeutral
    , test "CALL-019 conflicting residual reinstall rejects"
        conflictingResidualInstallRejects
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

okNeed, retryNeed :: CallableOutcomeAtom
okNeed = CallableOutcomeAtom "semantic.ok.need"
retryNeed = CallableOutcomeAtom "semantic.retry.need"

okProposition, retryProposition :: Proposition
okProposition = Atom "OkNeed" []
retryProposition = Atom "RetryNeed" []

successContract, retryContract :: CallableOutcomeContract
successContract = CallableOutcomeContract
  { callableOutcomeClass = successClass
  , callableOutcomeState = CallableOutcomeState "success"
  , callableOutcomeCalleeTransition = PreserveCallee
  , callableOutcomePostconditions = Set.empty
  , callableOutcomeResidualObligations = Set.singleton okNeed
  , callableOutcomeAssumptions = Set.empty
  , callableOutcomeEffects = Set.empty
  , callableOutcomeDischargedFacts = Set.empty
  }
retryContract = CallableOutcomeContract
  { callableOutcomeClass = retryClass
  , callableOutcomeState = CallableOutcomeState "retry"
  , callableOutcomeCalleeTransition = PreserveCallee
  , callableOutcomePostconditions = Set.empty
  , callableOutcomeResidualObligations = Set.singleton retryNeed
  , callableOutcomeAssumptions = Set.empty
  , callableOutcomeEffects = Set.empty
  , callableOutcomeDischargedFacts = Set.empty
  }

baseEnvironment :: Bool -> Bool -> SurfaceEnvironment
baseEnvironment includeOk includeRetry =
  (emptySurfaceEnvironment emptyStaticContext)
    { surfaceCallables = Map.singleton "Worker" SurfaceCallableSignature
        { surfaceCallableDeclarationKey = workerKey
        , surfaceCallableParameters = []
        , surfaceCallableResult = Nothing
        }
    , surfaceInitialBindings = Map.fromList
        (concat
          [ if includeOk
              then [("ok_evidence", proofBinding okProposition)]
              else []
          , if includeRetry
              then [("retry_evidence", proofBinding retryProposition)]
              else []
          ])
    }
  where
    proofBinding proposition = InitialBinding
      { initialMode = Unrestricted
      , initialType = TyProof proposition
      , initialShape = PlainShape
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

dispatchEnvironment
  :: Bool
  -> Bool
  -> SourceSpan
  -> Either String SurfaceEnvironment
dispatchEnvironment includeOk includeRetry invocationSpan = do
  let bindings = Map.fromList
        [ (successClass, dispatchBinding successClass "ok")
        , (retryClass, dispatchBinding retryClass "retry")
        ]
  plan <- mapLeft show
    (planSurfaceCallableOutcomeDispatch bindings (account invocationSpan))
  mapLeft show
    (installSurfaceCallableOutcomeDispatch plan (baseEnvironment includeOk includeRetry))

continuation
  :: SourceSpan
  -> Text
  -> CallableOutcomeContract
  -> SurfaceCallableOutcomeContinuation
continuation invocationSpan label contract =
  SurfaceCallableOutcomeContinuation
    { surfaceContinuationInvocationSpan = invocationSpan
    , surfaceContinuationArmSpan = invocationSpan
    , surfaceContinuationDeclarationKey = workerKey
    , surfaceContinuationSourceLabel = label
    , surfaceContinuationPayload = []
    , surfaceContinuationOutcomeClass = callableOutcomeClass contract
    , surfaceContinuationDisposition = SurfaceCallableOutcomeCallerContinues
    , surfaceContinuationState = callableOutcomeState contract
    , surfaceContinuationCalleeTransition = callableOutcomeCalleeTransition contract
    , surfaceContinuationPostconditions = callableOutcomePostconditions contract
    , surfaceContinuationResidualObligations = callableOutcomeResidualObligations contract
    , surfaceContinuationAssumptions = callableOutcomeAssumptions contract
    , surfaceContinuationEffects = callableOutcomeEffects contract
    , surfaceContinuationDischargedFacts = callableOutcomeDischargedFacts contract
    , surfaceContinuationContract = contract
    }

obligationBindings
  :: Map.Map CallableOutcomeAtom SurfaceCallableOutcomeObligationBinding
obligationBindings = Map.fromList
  [ (okNeed, obligation okNeed "ok_need" okProposition)
  , (retryNeed, obligation retryNeed "retry_need" retryProposition)
  ]
  where
    obligation semanticAtom name proposition =
      SurfaceCallableOutcomeObligationBinding
        { surfaceOutcomeObligationAtom = semanticAtom
        , surfaceOutcomeObligationName = name
        , surfaceOutcomeObligationProposition = proposition
        }

installResidueFor
  :: SourceSpan
  -> SurfaceEnvironment
  -> Either String SurfaceEnvironment
installResidueFor invocationSpan environment = do
  residue <- mapLeft show $
    bindSurfaceCallableOutcomeBranchResidue
      obligationBindings
      [ continuation invocationSpan "ok" successContract
      , continuation invocationSpan "retry" retryContract
      ]
  mapLeft show (installSurfaceCallableOutcomeBranchResidue residue environment)

continuingSource :: Text
continuingSource =
  "component Caller { let joined = decide invoke Worker() { "
    <> "ok => { unit } retry => { unit } } return joined }"

exactResidualsDischarge :: Either String ()
exactResidualsDischarge = do
  component <- parseOne continuingSource
  invocationSpan <- invocationSpanOf component
  dispatched <- dispatchEnvironment True True invocationSpan
  installed <- installResidueFor invocationSpan dispatched
  _ <- mapLeft show (checkSurfaceComponent installed component)
  Right ()

missingResidualBindingRejects :: Either String ()
missingResidualBindingRejects = do
  component <- parseOne continuingSource
  invocationSpan <- invocationSpanOf component
  let incomplete = Map.delete retryNeed obligationBindings
  case bindSurfaceCallableOutcomeBranchResidue
      incomplete
      [ continuation invocationSpan "ok" successContract
      , continuation invocationSpan "retry" retryContract
      ] of
    Left (SurfaceCallableOutcomeResidualBindingDomainMismatch expected actual)
      | Set.member retryNeed expected && not (Set.member retryNeed actual) -> Right ()
    Left other -> Left ("wrong missing-binding rejection: " <> show other)
    Right accepted -> Left ("incomplete residual binding accepted: " <> show accepted)

missingOccurrenceInstallationRejects :: Either String ()
missingOccurrenceInstallationRejects = do
  component <- parseOne continuingSource
  invocationSpan <- invocationSpanOf component
  dispatched <- dispatchEnvironment True True invocationSpan
  case checkSurfaceComponent dispatched component of
    Left errorValue
      | surfaceErrorClass errorValue == MissingEvidence -> Right ()
    Left other -> Left ("wrong missing-installation rejection: " <> show other)
    Right checked -> Left ("missing residual installation accepted: " <> show checked)

siblingEvidenceDoesNotDischarge :: Either String ()
siblingEvidenceDoesNotDischarge = do
  component <- parseOne continuingSource
  invocationSpan <- invocationSpanOf component
  dispatched <- dispatchEnvironment True False invocationSpan
  installed <- installResidueFor invocationSpan dispatched
  case checkSurfaceComponent installed component of
    Left errorValue
      | surfaceErrorClass errorValue == MissingEvidence -> Right ()
    Left other -> Left ("wrong sibling-evidence rejection: " <> show other)
    Right checked -> Left ("success evidence discharged retry obligation: " <> show checked)

wrongOccurrenceDoesNotInstall :: Either String ()
wrongOccurrenceDoesNotInstall = do
  component <- parseOne continuingSource
  invocationSpan <- invocationSpanOf component
  dispatched <- dispatchEnvironment True True invocationSpan
  let wrongSpan = SourceSpan
        (SourcePoint "wrong-occurrence" 9 1 900)
        (SourcePoint "wrong-occurrence" 9 2 901)
  installed <- installResidueFor wrongSpan dispatched
  case checkSurfaceComponent installed component of
    Left errorValue
      | surfaceErrorClass errorValue == MissingEvidence -> Right ()
    Left other -> Left ("wrong occurrence rejection: " <> show other)
    Right checked -> Left ("wrong-occurrence residuals became visible: " <> show checked)

declarationDispatchStaysNeutral :: Either String ()
declarationDispatchStaysNeutral = do
  component <- parseOne continuingSource
  invocationSpan <- invocationSpanOf component
  dispatched <- dispatchEnvironment True True invocationSpan
  installed <- installResidueFor invocationSpan dispatched
  specs <- maybe
    (Left "callable dispatch disappeared during residual installation")
    Right
    (Map.lookup workerKey (surfaceCallableOutcomes installed))
  assert
    (all (null . callableOutcomeObligations) specs)
    "occurrence residual propositions contaminated declaration dispatch"
  assert
    (map callableOutcomeResidualObligationArity specs == [1, 1])
    "declaration dispatch lost exact residual obligation arity"
  assert
    (Map.size (surfaceCallableOutcomeObligations installed) == 2)
    "expected one residual entry per continuing outcome"

conflictingResidualInstallRejects :: Either String ()
conflictingResidualInstallRejects = do
  component <- parseOne continuingSource
  invocationSpan <- invocationSpanOf component
  dispatched <- dispatchEnvironment True True invocationSpan
  residue <- mapLeft show $
    bindSurfaceCallableOutcomeBranchResidue
      obligationBindings
      [ continuation invocationSpan "ok" successContract
      , continuation invocationSpan "retry" retryContract
      ]
  installed <- mapLeft show
    (installSurfaceCallableOutcomeBranchResidue residue dispatched)
  let key = (invocationSpan, workerKey, "ok")
      poisoned = installed
        { surfaceCallableOutcomeObligations = Map.insert
            key [("wrong", Atom "Wrong" [])]
            (surfaceCallableOutcomeObligations installed)
        }
  case installSurfaceCallableOutcomeBranchResidue residue poisoned of
    Left (SurfaceCallableOutcomeResidueInstallConflict actualSpan actualKey actualLabel)
      | actualSpan == invocationSpan
          && actualKey == workerKey
          && actualLabel == "ok" -> Right ()
    Left other -> Left ("wrong reinstall rejection: " <> show other)
    Right accepted -> Left ("conflicting residual reinstall accepted: " <> show accepted)

invocationSpanOf :: Located Component -> Either String SourceSpan
invocationSpanOf locatedComponent =
  case blockStatements (locatedValue (componentBody (locatedValue locatedComponent))) of
    Located _ (LetStatement _ decision) : _ -> fromDecision decision
    Located _ (ExpressionStatement decision) : _ -> fromDecision decision
    statements -> Left
      ("expected leading decision statement, got " <> show (length statements))
  where
    fromDecision decision = case locatedValue decision of
      DecideExpression scrutinee _ -> Right (locatedSpan scrutinee)
      other -> Left ("expected decide expression, got " <> show other)

parseOne :: Text -> Either String (Located Component)
parseOne source = do
  parsed <- mapLeft show (parseSurfaceFile "call019-branch-residue" source)
  case surfaceComponents parsed of
    [component] -> Right component
    components -> Left ("expected one component, got " <> show (length components))

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
