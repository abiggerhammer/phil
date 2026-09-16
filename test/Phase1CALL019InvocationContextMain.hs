{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Compiler.CallableInvocationContext
  ( CheckedSurfaceCallableInvocationContext (..)
  , SurfaceCallableCallerContext (..)
  , SurfaceCallableInvocationContextError (..)
  , checkSurfaceComponentWithInvocationContext
  )
import Phil.Compiler.CallableInvocationSemantics
  ( SurfaceCallableSemanticSummary (..)
  )
import Phil.Core.Callable
  ( CallableCheckError (..)
  , CallableContract (..)
  , CalleeTransition (..)
  , SemanticEffect (..)
  )
import Phil.Core.CallableOutcome
  ( CallableOutcomeAtom (..)
  , CallableOutcomeClass (..)
  , CallableOutcomeContract (..)
  , CallableOutcomeState (..)
  )
import Phil.Core.CallableRefinement
  ( CallableAuthorityRequirement (..)
  , CallableFailure (..)
  , CallableMachineShape (..)
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
import Phil.Core.Syntax (Outcome (..))
import Phil.Surface.Check
  ( PrimitiveSemantics (..)
  , SurfaceCallableSignature (..)
  , SurfaceEnvironment (..)
  , emptySurfaceEnvironment
  )
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Syntax (Component, Located, SurfaceFile (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-019 caller context accepts authority/effects/failures within contract"
        completeContextAccepts
    , test "CALL-019 caller context rejects missing caller authority"
        missingAuthorityRejects
    , test "CALL-019 caller context rejects reachable effect widening"
        effectWideningRejects
    , test "CALL-019 caller context rejects undeclared modeled failure"
        undeclaredFailureRejects
    , test "CALL-019 direct named invoke rejects branch-sensitive outcome contract"
        branchSensitiveRejects
    , test "CALL-019 direct named invoke rejects consuming callee lifecycle"
        consumingDirectCallRejects
    , test "CALL-019 ordinary provider call requires no callable context facts"
        ordinaryProviderCallAccepts
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

readKey, writeKey, branchKey, consumeKey :: DeclarationKey
readKey = DeclarationKey "decl.read"
writeKey = DeclarationKey "decl.write"
branchKey = DeclarationKey "decl.branch"
consumeKey = DeclarationKey "decl.consume"

readEffect, writeEffect :: SemanticEffect
readEffect = SemanticEffect "effect:read"
writeEffect = SemanticEffect "effect:write"

readAuthority, writeAuthority :: CallableAuthorityRequirement
readAuthority = CallableAuthorityRequirement "authority:read"
writeAuthority = CallableAuthorityRequirement "authority:write"

writeFailure :: CallableFailure
writeFailure = CallableFatal "fatal:write"

successOutcome :: Text -> CalleeTransition -> CallableOutcomeContract
successOutcome state transition = CallableOutcomeContract
  { callableOutcomeClass = CallableSuccessOutcome
  , callableOutcomeState = CallableOutcomeState state
  , callableOutcomeCalleeTransition = transition
  , callableOutcomePostconditions = Set.singleton (CallableOutcomeAtom ("post:" <> state))
  , callableOutcomeResidualObligations = Set.empty
  , callableOutcomeAssumptions = Set.empty
  , callableOutcomeEffects = Set.empty
  , callableOutcomeDischargedFacts = Set.empty
  }

negativeOutcome :: CallableOutcomeContract
negativeOutcome = CallableOutcomeContract
  { callableOutcomeClass = CallableNonSuccessOutcome
      (CallableTypedNegative (Outcome "negative"))
  , callableOutcomeState = CallableOutcomeState "branch.negative"
  , callableOutcomeCalleeTransition = PreserveCallee
  , callableOutcomePostconditions = Set.empty
  , callableOutcomeResidualObligations = Set.empty
  , callableOutcomeAssumptions = Set.empty
  , callableOutcomeEffects = Set.empty
  , callableOutcomeDischargedFacts = Set.empty
  }

semanticContract
  :: Text
  -> CalleeTransition
  -> Set.Set SemanticEffect
  -> Set.Set CallableAuthorityRequirement
  -> Set.Set CallableFailure
  -> [CallableOutcomeContract]
  -> SourceCallableSemanticContract
semanticContract revision transition effects authority failures outcomes =
  SourceCallableSemanticContract
    { sourceCallableRefinementSurface = CallableRefinementSurface
        { callableRefinementMachineShape = CallableMachineShape "Unit->Unit"
        , callableRefinementContract = CallableContract
            { callableContractInterfaceRevision = InterfaceRevision revision
            , callableContractCalleeTransition = transition
            , callableContractEffectBound = effects
            }
        , callableRefinementCallerAuthority = authority
        , callableRefinementFailures = failures
        }
    , sourceCallableOutcomeContracts = outcomes
    }

readContract, writeContract, branchContract, consumeContract
  :: SourceCallableSemanticContract
readContract = semanticContract
  "read.v1"
  PreserveCallee
  (Set.singleton readEffect)
  (Set.singleton readAuthority)
  Set.empty
  [successOutcome "read.success" PreserveCallee]
writeContract = semanticContract
  "write.v1"
  PreserveCallee
  (Set.singleton writeEffect)
  (Set.singleton writeAuthority)
  (Set.singleton writeFailure)
  [successOutcome "write.success" PreserveCallee]
branchContract = semanticContract
  "branch.v1"
  PreserveCallee
  Set.empty
  Set.empty
  (Set.singleton (CallableTypedNegative (Outcome "negative")))
  [ successOutcome "branch.success" PreserveCallee
  , negativeOutcome
  ]
consumeContract = semanticContract
  "consume.v1"
  ConsumeCallee
  Set.empty
  Set.empty
  Set.empty
  [successOutcome "consume.success" ConsumeCallee]

signature :: DeclarationKey -> SurfaceCallableSignature
signature key = SurfaceCallableSignature
  { surfaceCallableDeclarationKey = key
  , surfaceCallableParameters = []
  , surfaceCallableResult = Nothing
  }

callEnvironment :: SurfaceEnvironment
callEnvironment = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceCallables = Map.fromList
      [ ("Read", signature readKey)
      , ("Write", signature writeKey)
      , ("Branch", signature branchKey)
      , ("Consume", signature consumeKey)
      ]
  }

contracts :: Map.Map DeclarationKey SourceCallableSemanticContract
contracts = Map.fromList
  [ (readKey, readContract)
  , (writeKey, writeContract)
  , (branchKey, branchContract)
  , (consumeKey, consumeContract)
  ]

callerSurface
  :: Set.Set SemanticEffect
  -> Set.Set CallableFailure
  -> CallableRefinementSurface
callerSurface effects failures = CallableRefinementSurface
  { callableRefinementMachineShape = CallableMachineShape "Caller"
  , callableRefinementContract = CallableContract
      { callableContractInterfaceRevision = InterfaceRevision "caller.v1"
      , callableContractCalleeTransition = PreserveCallee
      , callableContractEffectBound = effects
      }
  , callableRefinementCallerAuthority = Set.empty
  , callableRefinementFailures = failures
  }

completeContext :: SurfaceCallableCallerContext
completeContext = SurfaceCallableCallerContext
  { surfaceCallerAvailableAuthority = Set.fromList [readAuthority, writeAuthority]
  , surfaceCallerPublicContract = callerSurface
      (Set.fromList [readEffect, writeEffect])
      (Set.singleton writeFailure)
  }

completeContextAccepts :: Either String ()
completeContextAccepts = do
  component <- parseOne
    "component Caller { invoke Read() invoke Write() return unit }"
  checked <- mapLeft show $
    checkSurfaceComponentWithInvocationContext
      contracts completeContext callEnvironment component
  let summary = checkedInvocationSemanticSummary checked
  assert
    (surfaceRequiredCallerAuthority summary == Set.fromList [readAuthority, writeAuthority])
    "accepted context lost exact authority requirements"
  assert
    (surfaceReachableCallableEffects summary == Set.fromList [readEffect, writeEffect])
    "accepted context lost reachable callable effects"

missingAuthorityRejects :: Either String ()
missingAuthorityRejects = do
  let context = completeContext
        { surfaceCallerAvailableAuthority = Set.singleton readAuthority }
  expectError
    (\err -> case err of
      SurfaceInvocationMissingCallerAuthority missing ->
        missing == Set.singleton writeAuthority
      _ -> False)
    context
    "component Caller { invoke Read() invoke Write() return unit }"
    "missing caller authority"

effectWideningRejects :: Either String ()
effectWideningRejects = do
  let context = completeContext
        { surfaceCallerPublicContract = callerSurface
            (Set.singleton readEffect)
            (Set.singleton writeFailure)
        }
  expectError
    (\err -> case err of
      SurfaceInvocationEffectRejected
        (CallableEffectBoundExceeded _ extra publicBound) ->
          extra == Set.singleton writeEffect
            && publicBound == Set.singleton readEffect
      _ -> False)
    context
    "component Caller { invoke Read() invoke Write() return unit }"
    "effect widening"

undeclaredFailureRejects :: Either String ()
undeclaredFailureRejects = do
  let context = completeContext
        { surfaceCallerPublicContract = callerSurface
            (Set.fromList [readEffect, writeEffect])
            Set.empty
        }
  expectError
    (\err -> case err of
      SurfaceInvocationFailureSetExceeded extra ->
        extra == Set.singleton writeFailure
      _ -> False)
    context
    "component Caller { invoke Write() return unit }"
    "undeclared modeled failure"

branchSensitiveRejects :: Either String ()
branchSensitiveRejects =
  expectError
    (\err -> case err of
      SurfaceInvocationOutcomeShapeUnsupported _ classes ->
        classes ==
          [ CallableSuccessOutcome
          , CallableNonSuccessOutcome (CallableTypedNegative (Outcome "negative"))
          ]
      _ -> False)
    completeContext
    "component Caller { invoke Branch() return unit }"
    "branch-sensitive outcome"

consumingDirectCallRejects :: Either String ()
consumingDirectCallRejects =
  expectError
    (\err -> case err of
      SurfaceInvocationDirectCalleeTransitionUnsupported _ ConsumeCallee -> True
      _ -> False)
    completeContext
    "component Caller { invoke Consume() return unit }"
    "consuming direct named callee"

ordinaryProviderCallAccepts :: Either String ()
ordinaryProviderCallAccepts = do
  component <- parseOne "component Caller { Worker() return unit }"
  let environment = (emptySurfaceEnvironment emptyStaticContext)
        { surfacePrimitives = Map.singleton "Worker" PrimitiveUse
        }
      context = SurfaceCallableCallerContext
        { surfaceCallerAvailableAuthority = Set.empty
        , surfaceCallerPublicContract = callerSurface Set.empty Set.empty
        }
  checked <- mapLeft show $
    checkSurfaceComponentWithInvocationContext Map.empty context environment component
  let summary = checkedInvocationSemanticSummary checked
  assert
    (null (surfaceCallableSemanticAccounts summary)
      && Set.null (surfaceReachableCallableEffects summary)
      && Set.null (surfaceRequiredCallerAuthority summary)
      && Set.null (surfaceReachableCallableFailures summary))
    "ordinary provider call leaked into callable caller-context checking"

expectError
  :: (SurfaceCallableInvocationContextError -> Bool)
  -> SurfaceCallableCallerContext
  -> Text
  -> String
  -> Either String ()
expectError predicate context source label = do
  component <- parseOne source
  case checkSurfaceComponentWithInvocationContext contracts context callEnvironment component of
    Left err | predicate err -> Right ()
    Left err -> Left ("unexpected " <> label <> " error: " <> show err)
    Right result -> Left ("expected " <> label <> " rejection, got " <> show result)

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

parseOne :: Text -> Either String (Located Component)
parseOne source = do
  parsed <- mapLeft show (parseSurfaceFile "call019-invocation-context" source)
  case surfaceComponents parsed of
    [component] -> Right component
    components -> Left ("expected one component, got " <> show (length components))

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
