{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Compiler.CallableInvocationContext
  ( CheckedSurfaceCallableInvocationLifecycleContext (..)
  , SurfaceCallableCallerContext (..)
  , SurfaceCallableInvocationContextError (..)
  , checkSurfaceCallableInvocationSummaryWithOutcomeBranchesAndLifecycle
  )
import Phil.Compiler.CallableInvocationLifecycle
  ( SurfaceCallableInvocationLifecycleBinding (..)
  , SurfaceCallableInvocationLifecycleError (..)
  )
import Phil.Compiler.CallableInvocationSemantics
  ( SurfaceCallableInvocationSemanticAccount (..)
  , SurfaceCallableSemanticSummary (..)
  , summarizeSurfaceCallableSemantics
  )
import Phil.Compiler.CallableSurfaceSemantics
  ( checkSurfaceComponentWithCallableSemantics
  )
import Phil.Core.Callable
  ( CalleeTransition (..)
  , CallableContract (..)
  , CallableInvocationBodySummary (..)
  , CallableOccurrence (..)
  , ClosureCaptureSummary
  , CallableOccurrenceKey (..)
  , CallableResourceState (..)
  , CallableStateKey (..)
  , checkClosureCaptures
  )
import Phil.Core.CallableOutcome
  ( CallableOutcomeClass (..)
  , CallableOutcomeContract (..)
  , CallableOutcomeState (..)
  )
import Phil.Core.CallableRefinement
  ( CallableMachineShape (..)
  , CallableRefinementSurface (..)
  )
import Phil.Core.CallableSemanticContract
  ( SourceCallableSemanticContract (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , InterfaceRevision (..)
  , emptyStaticContext
  )
import Phil.Surface.Check
  ( SurfaceCallableSignature (..)
  , SurfaceEnvironment (..)
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

data Expected
  = AcceptFinal [CallableOccurrenceKey] Int
  | RejectUnavailable CallableOccurrenceKey
  | RejectDomain
  | RejectBindingIdentity

data Case = Case
  { caseLabel :: String
  , caseSource :: Text
  , caseInitial :: CallableResourceState
  , caseBindingMode :: BindingMode
  , caseExpected :: Expected
  }

data BindingMode = ExactBindings | MissingBindings | WrongRepeatedIdentity

main :: IO ()
main = do
  results <- mapM runCase cases
  if and results then pure () else exitFailure

runCase :: Case -> IO Bool
runCase testCase =
  case prepare testCase of
    Left detail -> failCase detail
    Right (summary, bindings) ->
      case checkSurfaceCallableInvocationSummaryWithOutcomeBranchesAndLifecycle
          bindings
          (caseInitial testCase)
          []
          callerContext
          summary of
        Right checked -> case caseExpected testCase of
          AcceptFinal expectedKeys expectedWitnesses -> do
            let finalState = checkedInvocationFinalCallableState checked
                witnesses = checkedInvocationLifecycleWitnesses checked
                actualKeys = Map.keys (callableResourceOccurrences finalState)
            if Set.fromList actualKeys == Set.fromList expectedKeys
                && length witnesses == expectedWitnesses
              then passCase
              else failCase
                ("wrong accepted final state/witness count: "
                  <> show (actualKeys, length witnesses))
          expected -> failCase ("unexpected acceptance for " <> showExpected expected)
        Left errorValue -> case caseExpected testCase of
          RejectUnavailable key ->
            case errorValue of
              SurfaceInvocationLifecycleRejected
                (SurfaceCallableLifecyclePredecessorUnavailable _ actual)
                  | actual == key -> passCase
              other -> failCase ("wrong unavailable rejection: " <> show other)
          RejectDomain ->
            case errorValue of
              SurfaceInvocationLifecycleRejected
                (SurfaceCallableLifecycleBindingDomainMismatch _ _) -> passCase
              other -> failCase ("wrong binding-domain rejection: " <> show other)
          RejectBindingIdentity ->
            case errorValue of
              SurfaceInvocationLifecycleRejected
                (SurfaceCallableLifecycleBindingIdentityMismatch _ _) -> passCase
              other -> failCase ("wrong binding-identity rejection: " <> show other)
          expected -> failCase
            ("unexpected rejection for " <> showExpected expected <> ": " <> show errorValue)
  where
    prefix = "PHIL-AUD-CALL-LIFECYCLE-PATH-001 " <> caseLabel testCase
    passCase = putStrLn ("PASS: " <> prefix) >> pure True
    failCase detail = putStrLn ("FAIL: " <> prefix <> " -- " <> detail) >> pure False

showExpected :: Expected -> String
showExpected expected = case expected of
  AcceptFinal keys count -> "accept " <> show keys <> " witnesses=" <> show count
  RejectUnavailable key -> "reject unavailable " <> show key
  RejectDomain -> "reject binding domain"
  RejectBindingIdentity -> "reject binding identity"

prepare
  :: Case
  -> Either String
       ( SurfaceCallableSemanticSummary
       , Map (SourceSpan, DeclarationKey) SurfaceCallableInvocationLifecycleBinding
       )
prepare testCase = do
  component <- parseOne (caseSource testCase)
  checked <- mapLeft show $
    checkSurfaceComponentWithCallableSemantics contracts environment component
  let summary = summarizeSurfaceCallableSemantics checked
      accounts = surfaceCallableSemanticAccounts summary
      exact = Map.fromList
        [ ( identity account
          , bindingFor account
          )
        | account <- accounts
        ]
  bindings <- case caseBindingMode testCase of
    ExactBindings -> Right exact
    MissingBindings -> Right Map.empty
    WrongRepeatedIdentity -> case Map.toAscList exact of
      [] -> Left "cannot corrupt an empty binding map"
      (key, value) : rest ->
        let wrongSpan = SourceSpan
              (SourcePoint "audit-wrong-binding" 1 1 0)
              (SourcePoint "audit-wrong-binding" 1 2 1)
            wrong = value { surfaceLifecycleBindingInvocationSpan = wrongSpan }
        in Right (Map.fromList ((key, wrong) : rest))
  Right (summary, bindings)

identity :: SurfaceCallableInvocationSemanticAccount -> (SourceSpan, DeclarationKey)
identity account =
  ( surfaceSemanticInvocationSpan account
  , surfaceSemanticInvocationDeclarationKey account
  )

bindingFor
  :: SurfaceCallableInvocationSemanticAccount
  -> SurfaceCallableInvocationLifecycleBinding
bindingFor account = SurfaceCallableInvocationLifecycleBinding
  { surfaceLifecycleBindingInvocationSpan = surfaceSemanticInvocationSpan account
  , surfaceLifecycleBindingDeclarationKey =
      surfaceSemanticInvocationDeclarationKey account
  , surfaceLifecycleBindingPredecessor = predecessor
  , surfaceLifecycleBindingBodySummary = body
  }
  where
    (predecessor, body) = case surfaceSemanticInvocationDisplayName account of
      "Advance" -> (predecessorKey, advanceBody)
      "Finish" -> (successorKey, emptyBody)
      "Once" -> (onceKey, emptyBody)
      "Observe" -> (observeKey, emptyBody)
      other -> error ("unknown audit callable: " <> show other)

parseOne :: Text -> Either String (Located Component)
parseOne source = do
  parsed <- mapLeft show (parseSurfaceFile "audit-call-lifecycle-path.phil" source)
  case surfaceComponents parsed of
    [component] -> Right component
    components -> Left ("expected one component, got " <> show (length components))

advanceKey, finishKey, onceDeclKey, observeDeclKey :: DeclarationKey
advanceKey = DeclarationKey "decl.audit.advance"
finishKey = DeclarationKey "decl.audit.finish"
onceDeclKey = DeclarationKey "decl.audit.once"
observeDeclKey = DeclarationKey "decl.audit.observe"

predecessorKey, successorKey, onceKey, observeKey :: CallableOccurrenceKey
predecessorKey = CallableOccurrenceKey "audit.predecessor"
successorKey = CallableOccurrenceKey "audit.successor"
onceKey = CallableOccurrenceKey "audit.once"
observeKey = CallableOccurrenceKey "audit.observe"

successorInterface :: InterfaceRevision
successorInterface = InterfaceRevision "audit.successor.v1"

successorState :: CallableStateKey
successorState = CallableStateKey "audit.successor.S1"

advanceTransition :: CalleeTransition
advanceTransition = ReplaceCallee successorInterface (Just successorState)

finishTransition, onceTransition, observeTransition :: CalleeTransition
finishTransition = ConsumeCallee
onceTransition = ConsumeCallee
observeTransition = PreserveCallee

contract :: InterfaceRevision -> CalleeTransition -> CallableContract
contract revision transition = CallableContract
  { callableContractInterfaceRevision = revision
  , callableContractCalleeTransition = transition
  , callableContractEffectBound = Set.empty
  }

advanceContract, finishContract, onceContract, observeContract :: CallableContract
advanceContract = contract (InterfaceRevision "audit.advance.v1") advanceTransition
finishContract = contract successorInterface finishTransition
onceContract = contract (InterfaceRevision "audit.once.v1") onceTransition
observeContract = contract (InterfaceRevision "audit.observe.v1") observeTransition

semanticContract :: CallableContract -> SourceCallableSemanticContract
semanticContract publicContract = SourceCallableSemanticContract
  { sourceCallableRefinementSurface = CallableRefinementSurface
      { callableRefinementMachineShape = CallableMachineShape "Unit->Unit"
      , callableRefinementContract = publicContract
      , callableRefinementCallerAuthority = Set.empty
      , callableRefinementFailures = Set.empty
      }
  , sourceCallableOutcomeContracts =
      [ CallableOutcomeContract
          { callableOutcomeClass = CallableSuccessOutcome
          , callableOutcomeState = CallableOutcomeState "success"
          , callableOutcomeCalleeTransition =
              callableContractCalleeTransition publicContract
          , callableOutcomePostconditions = Set.empty
          , callableOutcomeResidualObligations = Set.empty
          , callableOutcomeAssumptions = Set.empty
          , callableOutcomeEffects = Set.empty
          , callableOutcomeDischargedFacts = Set.empty
          }
      ]
  }

signature :: DeclarationKey -> SurfaceCallableSignature
signature key = SurfaceCallableSignature
  { surfaceCallableDeclarationKey = key
  , surfaceCallableParameters = []
  , surfaceCallableResult = Nothing
  }

environment :: SurfaceEnvironment
environment = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceCallables = Map.fromList
      [ ("Advance", signature advanceKey)
      , ("Finish", signature finishKey)
      , ("Once", signature onceDeclKey)
      , ("Observe", signature observeDeclKey)
      ]
  }

contracts :: Map DeclarationKey SourceCallableSemanticContract
contracts = Map.fromList
  [ (advanceKey, semanticContract advanceContract)
  , (finishKey, semanticContract finishContract)
  , (onceDeclKey, semanticContract onceContract)
  , (observeDeclKey, semanticContract observeContract)
  ]

emptyCaptures :: ClosureCaptureSummary
emptyCaptures = case checkClosureCaptures [] of
  Right value -> value
  Left errorValue -> error (show errorValue)

predecessorOccurrence, successorOccurrence, onceOccurrence, observeOccurrence
  :: CallableOccurrence
predecessorOccurrence = CallableOccurrence
  { callableOccurrenceKey = predecessorKey
  , callableOccurrenceContract = advanceContract
  , callableOccurrenceCaptures = emptyCaptures
  , callableOccurrenceStateKey = Just (CallableStateKey "audit.predecessor.S0")
  }
successorOccurrence = CallableOccurrence
  { callableOccurrenceKey = successorKey
  , callableOccurrenceContract = finishContract
  , callableOccurrenceCaptures = emptyCaptures
  , callableOccurrenceStateKey = Just successorState
  }
onceOccurrence = CallableOccurrence
  { callableOccurrenceKey = onceKey
  , callableOccurrenceContract = onceContract
  , callableOccurrenceCaptures = emptyCaptures
  , callableOccurrenceStateKey = Nothing
  }
observeOccurrence = CallableOccurrence
  { callableOccurrenceKey = observeKey
  , callableOccurrenceContract = observeContract
  , callableOccurrenceCaptures = emptyCaptures
  , callableOccurrenceStateKey = Nothing
  }

advanceBody, emptyBody :: CallableInvocationBodySummary
advanceBody = CallableInvocationBodySummary
  { invocationRestrictedCaptureResidue = Set.empty
  , invocationSuccessorCallable = Just successorOccurrence
  }
emptyBody = CallableInvocationBodySummary
  { invocationRestrictedCaptureResidue = Set.empty
  , invocationSuccessorCallable = Nothing
  }

resourceState :: [CallableOccurrence] -> CallableResourceState
resourceState occurrences = CallableResourceState
  (Map.fromList [(callableOccurrenceKey occurrence, occurrence) | occurrence <- occurrences])

callerContext :: SurfaceCallableCallerContext
callerContext = SurfaceCallableCallerContext
  { surfaceCallerAvailableAuthority = Set.empty
  , surfaceCallerPublicContract = CallableRefinementSurface
      { callableRefinementMachineShape = CallableMachineShape "Caller"
      , callableRefinementContract = contract (InterfaceRevision "caller.v1") PreserveCallee
      , callableRefinementCallerAuthority = Set.empty
      , callableRefinementFailures = Set.empty
      }
  }

cases :: [Case]
cases =
  [ Case "p01 sequential Advance then Finish"
      "component Caller { invoke Advance() invoke Finish() return unit }"
      (resourceState [predecessorOccurrence])
      ExactBindings
      (AcceptFinal [] 2)
  , Case "p02 exclusive Advance/Finish arms"
      "component Caller(flag: Bool) { decide flag { true => { invoke Advance() } false => { invoke Finish() } } return unit }"
      (resourceState [predecessorOccurrence])
      ExactBindings
      (RejectUnavailable successorKey)
  , Case "p03 reordered exclusive arms"
      "component Caller(flag: Bool) { decide flag { false => { invoke Finish() } true => { invoke Advance() } } return unit }"
      (resourceState [predecessorOccurrence])
      ExactBindings
      (RejectUnavailable successorKey)
  , Case "p04 Finish without Advance"
      "component Caller { invoke Finish() return unit }"
      (resourceState [predecessorOccurrence])
      ExactBindings
      (RejectUnavailable successorKey)
  , Case "p05 one Once call in each exclusive arm"
      "component Caller(flag: Bool) { decide flag { true => { invoke Once() } false => { invoke Once() } } return unit }"
      (resourceState [onceOccurrence])
      ExactBindings
      (AcceptFinal [] 2)
  , Case "p06 two sequential Once calls"
      "component Caller { invoke Once() invoke Once() return unit }"
      (resourceState [onceOccurrence])
      ExactBindings
      (RejectUnavailable onceKey)
  , Case "p07 Advance alone"
      "component Caller { invoke Advance() return unit }"
      (resourceState [predecessorOccurrence])
      ExactBindings
      (AcceptFinal [successorKey] 1)
  , Case "p08 preserving Observe in each alternative"
      "component Caller(flag: Bool) { decide flag { true => { invoke Observe() } false => { invoke Observe() } } return unit }"
      (resourceState [observeOccurrence])
      ExactBindings
      (AcceptFinal [observeKey] 2)
  , Case "p09 missing lifecycle bindings"
      "component Caller { invoke Advance() invoke Finish() return unit }"
      (resourceState [predecessorOccurrence])
      MissingBindings
      RejectDomain
  , Case "p10 repeated binding identity mismatch"
      "component Caller { invoke Advance() invoke Finish() return unit }"
      (resourceState [predecessorOccurrence])
      WrongRepeatedIdentity
      RejectBindingIdentity
  , Case "p11 empty invocation summary preserves observer"
      "component Caller { return unit }"
      (resourceState [observeOccurrence])
      ExactBindings
      (AcceptFinal [observeKey] 0)
  , Case "p12 conditional Advance cannot justify continuation Finish"
      "component Caller(flag: Bool) { decide flag { true => { invoke Advance() } false => { unit } } invoke Finish() return unit }"
      (resourceState [predecessorOccurrence])
      ExactBindings
      (RejectUnavailable successorKey)
  ]

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
