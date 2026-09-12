{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Compiler.CallableInvocationSemantics
  ( SurfaceCallableInvocationSemanticAccount (..)
  , SurfaceCallableSemanticSummary (..)
  , summarizeSurfaceCallableSemantics
  )
import Phil.Compiler.CallableSurfaceSemantics
  ( checkSurfaceComponentWithCallableSemantics
  )
import Phil.Core.Callable
  ( CallableContract (..)
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
    [ test "CALL-019 semantic account preserves invocation order and exact categories"
        exactInvocationAccounts
    , test "CALL-019 reachable invocation imports public may-effects through CALL effect semantics"
        reachableEffectsCompose
    , test "CALL-019 caller authority and modeled failures accumulate without reclassification"
        authorityAndFailuresCompose
    , test "CALL-019 ordinary provider call contributes no callable semantic account"
        ordinaryProviderCallIgnored
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

readKey, writeKey :: DeclarationKey
readKey = DeclarationKey "decl.read"
writeKey = DeclarationKey "decl.write"

readEffect, writeEffect :: SemanticEffect
readEffect = SemanticEffect "effect:read"
writeEffect = SemanticEffect "effect:write"

readAuthority, writeAuthority :: CallableAuthorityRequirement
readAuthority = CallableAuthorityRequirement "authority:read"
writeAuthority = CallableAuthorityRequirement "authority:write"

writeFailure :: CallableFailure
writeFailure = CallableFatal "fatal:write"

readOutcome, writeOutcome :: CallableOutcomeContract
readOutcome = outcome "read.success" "post:read" "residual:read" "assumption:read" "effect:read" "fact:read"
writeOutcome = outcome "write.success" "post:write" "residual:write" "assumption:write" "effect:write" "fact:write"

outcome :: Text -> Text -> Text -> Text -> Text -> Text -> CallableOutcomeContract
outcome state postcondition residual assumption effect discharged = CallableOutcomeContract
  { callableOutcomeClass = CallableSuccessOutcome
  , callableOutcomeState = CallableOutcomeState state
  , callableOutcomeCalleeTransition = PreserveCallee
  , callableOutcomePostconditions = Set.singleton (CallableOutcomeAtom postcondition)
  , callableOutcomeResidualObligations = Set.singleton (CallableOutcomeAtom residual)
  , callableOutcomeAssumptions = Set.singleton (CallableOutcomeAtom assumption)
  , callableOutcomeEffects = Set.singleton (CallableOutcomeAtom effect)
  , callableOutcomeDischargedFacts = Set.singleton (CallableOutcomeAtom discharged)
  }

readContract, writeContract :: SourceCallableSemanticContract
readContract = semanticContract
  "Unit->Unit"
  "read.v1"
  (Set.singleton readEffect)
  (Set.singleton readAuthority)
  Set.empty
  [readOutcome]
writeContract = semanticContract
  "Unit->Unit"
  "write.v1"
  (Set.singleton writeEffect)
  (Set.singleton writeAuthority)
  (Set.singleton writeFailure)
  [writeOutcome]

semanticContract
  :: Text
  -> Text
  -> Set.Set SemanticEffect
  -> Set.Set CallableAuthorityRequirement
  -> Set.Set CallableFailure
  -> [CallableOutcomeContract]
  -> SourceCallableSemanticContract
semanticContract shape revision effects authority failures outcomes =
  SourceCallableSemanticContract
    { sourceCallableRefinementSurface = CallableRefinementSurface
        { callableRefinementMachineShape = CallableMachineShape shape
        , callableRefinementContract = CallableContract
            { callableContractInterfaceRevision = InterfaceRevision revision
            , callableContractCalleeTransition = PreserveCallee
            , callableContractEffectBound = effects
            }
        , callableRefinementCallerAuthority = authority
        , callableRefinementFailures = failures
        }
    , sourceCallableOutcomeContracts = outcomes
    }

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
      ]
  }

contracts :: Map.Map DeclarationKey SourceCallableSemanticContract
contracts = Map.fromList
  [ (readKey, readContract)
  , (writeKey, writeContract)
  ]

checkedSummary :: Either String SurfaceCallableSemanticSummary
checkedSummary = do
  component <- parseOne
    "component Caller { invoke Read() invoke Write() return unit }"
  checked <- mapLeft show $
    checkSurfaceComponentWithCallableSemantics contracts callEnvironment component
  Right (summarizeSurfaceCallableSemantics checked)

exactInvocationAccounts :: Either String ()
exactInvocationAccounts = do
  summary <- checkedSummary
  case surfaceCallableSemanticAccounts summary of
    [readAccount, writeAccount] -> do
      assert
        (surfaceSemanticInvocationDisplayName readAccount == "Read"
          && surfaceSemanticInvocationDeclarationKey readAccount == readKey)
        "first invocation account lost exact Read identity"
      assert
        (surfaceSemanticInvocationDisplayName writeAccount == "Write"
          && surfaceSemanticInvocationDeclarationKey writeAccount == writeKey)
        "second invocation account lost exact Write identity"
      assert
        (surfaceSemanticInvocationSpan readAccount /= surfaceSemanticInvocationSpan writeAccount)
        "distinct source invocations collapsed to one occurrence"
      assert
        (surfaceSemanticInvocationCallerAuthority readAccount == Set.singleton readAuthority
          && surfaceSemanticInvocationPublicEffectBound readAccount == Set.singleton readEffect
          && surfaceSemanticInvocationCalleeTransition readAccount == PreserveCallee
          && Set.null (surfaceSemanticInvocationModeledFailures readAccount)
          && surfaceSemanticInvocationOutcomes readAccount == [readOutcome])
        "Read invocation semantic categories were weakened or reclassified"
      assert
        (surfaceSemanticInvocationCallerAuthority writeAccount == Set.singleton writeAuthority
          && surfaceSemanticInvocationPublicEffectBound writeAccount == Set.singleton writeEffect
          && surfaceSemanticInvocationCalleeTransition writeAccount == PreserveCallee
          && surfaceSemanticInvocationModeledFailures writeAccount == Set.singleton writeFailure
          && surfaceSemanticInvocationOutcomes writeAccount == [writeOutcome])
        "Write invocation semantic categories were weakened or reclassified"
    accounts -> Left ("expected two semantic invocation accounts, got " <> show accounts)

reachableEffectsCompose :: Either String ()
reachableEffectsCompose = do
  summary <- checkedSummary
  assert
    (surfaceReachableCallableEffects summary == Set.fromList [readEffect, writeEffect])
    "reachable invocation did not import the exact public may-effect bounds"

authorityAndFailuresCompose :: Either String ()
authorityAndFailuresCompose = do
  summary <- checkedSummary
  assert
    (surfaceRequiredCallerAuthority summary == Set.fromList [readAuthority, writeAuthority])
    "caller authority requirements did not compose exactly"
  assert
    (surfaceReachableCallableFailures summary == Set.singleton writeFailure)
    "modeled callable failures did not compose exactly"

ordinaryProviderCallIgnored :: Either String ()
ordinaryProviderCallIgnored = do
  component <- parseOne "component Caller { Worker() return unit }"
  let environment = (emptySurfaceEnvironment emptyStaticContext)
        { surfacePrimitives = Map.singleton "Worker" PrimitiveUse
        }
  checked <- mapLeft show $
    checkSurfaceComponentWithCallableSemantics Map.empty environment component
  let summary = summarizeSurfaceCallableSemantics checked
  assert
    (null (surfaceCallableSemanticAccounts summary)
      && Set.null (surfaceReachableCallableEffects summary)
      && Set.null (surfaceRequiredCallerAuthority summary)
      && Set.null (surfaceReachableCallableFailures summary))
    "ordinary provider call leaked into callable invocation semantics"

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

parseOne :: Text -> Either String (Located Component)
parseOne source = do
  parsed <- mapLeft show (parseSurfaceFile "call019-invocation-account" source)
  case surfaceComponents parsed of
    [component] -> Right component
    components -> Left ("expected one component, got " <> show (length components))

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
