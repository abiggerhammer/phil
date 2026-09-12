{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Compiler.CallableSurfaceSemantics
  ( SurfaceCallableInvocationWitness (..)
  , SurfaceSemanticCheckResult (..)
  , checkSurfaceComponentWithCallableSemantics
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
import Phil.Core.Syntax (Mode (..), Ty (..))
import Phil.Surface.Check
  ( InitialBinding (..)
  , PrimitiveSemantics (..)
  , RejectionClass (..)
  , SurfaceCallableSignature (..)
  , SurfaceCheckError (..)
  , SurfaceEnvironment (..)
  , SurfaceShape (..)
  , checkSurfaceComponent
  , emptySurfaceEnvironment
  )
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Syntax (Component, Located, SurfaceFile (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-019 invoke accepts exact checked signature" validLinearInvoke
    , test "CALL-019 invoke transfers a restricted argument" invokeConsumesLinear
    , test "CALL-019 unknown callable rejects at callable competence" unknownCallableRejects
    , test "CALL-019 provider primitive cannot rescue invoke lookup" primitiveCannotRescueInvoke
    , test "CALL-019 ordinary call remains provider primitive lookup" ordinaryCallRemainsPrimitive
    , test "CALL-019 callable result carries declared restricted mode" restrictedResultReturns
    , test "CALL-019 semantic bridge retains the exact complete callable contract" semanticWitnessRetained
    , test "CALL-019 semantic bridge preserves repeated invocation occurrences" semanticOccurrencesPreserved
    , test "CALL-019 semantic bridge fails closed when an exact contract is missing" semanticContractMissingRejects
    , test "CALL-019 semantic bridge does not reinterpret ordinary provider calls" semanticOrdinaryCallIgnored
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

blobType :: Ty
blobType = TyOpaque "Blob"

candidateBinding :: InitialBinding
candidateBinding = InitialBinding Linear blobType PlainShape

callable :: Text -> [(Mode, Ty)] -> Maybe (Mode, Ty) -> SurfaceCallableSignature
callable key parameters result = SurfaceCallableSignature
  { surfaceCallableDeclarationKey = DeclarationKey key
  , surfaceCallableParameters = parameters
  , surfaceCallableResult = result
  }

takeSignature :: SurfaceCallableSignature
takeSignature = callable "decl.take" [(Linear, blobType)] Nothing

pingSignature :: SurfaceCallableSignature
pingSignature = callable "decl.ping" [] Nothing

takeSemanticContract :: SourceCallableSemanticContract
takeSemanticContract = SourceCallableSemanticContract
  { sourceCallableRefinementSurface = CallableRefinementSurface
      { callableRefinementMachineShape = CallableMachineShape "Blob->Unit"
      , callableRefinementContract = CallableContract
          { callableContractInterfaceRevision = InterfaceRevision "take.v1"
          , callableContractCalleeTransition = PreserveCallee
          , callableContractEffectBound = Set.singleton (SemanticEffect "effect:write")
          }
      , callableRefinementCallerAuthority =
          Set.singleton (CallableAuthorityRequirement "authority:write")
      , callableRefinementFailures = Set.empty
      }
  , sourceCallableOutcomeContracts =
      [ CallableOutcomeContract
          { callableOutcomeClass = CallableSuccessOutcome
          , callableOutcomeState = CallableOutcomeState "take.success"
          , callableOutcomeCalleeTransition = PreserveCallee
          , callableOutcomePostconditions =
              Set.singleton (CallableOutcomeAtom "post:stored")
          , callableOutcomeResidualObligations =
              Set.singleton (CallableOutcomeAtom "residual:audit")
          , callableOutcomeAssumptions =
              Set.singleton (CallableOutcomeAtom "assumption:storage-live")
          , callableOutcomeEffects =
              Set.singleton (CallableOutcomeAtom "effect:write")
          , callableOutcomeDischargedFacts =
              Set.singleton (CallableOutcomeAtom "fact:authorized")
          }
      ]
  }

pingSemanticContract :: SourceCallableSemanticContract
pingSemanticContract = takeSemanticContract
  { sourceCallableRefinementSurface =
      (sourceCallableRefinementSurface takeSemanticContract)
        { callableRefinementMachineShape = CallableMachineShape "Unit->Unit"
        , callableRefinementContract =
            (callableRefinementContract
              (sourceCallableRefinementSurface takeSemanticContract))
              { callableContractInterfaceRevision = InterfaceRevision "ping.v1"
              }
        }
  }

baseWithCandidate :: SurfaceEnvironment
baseWithCandidate = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceInitialBindings = Map.singleton "candidate" candidateBinding
  , surfaceCallables = Map.singleton "Take" takeSignature
  }

pingEnvironment :: SurfaceEnvironment
pingEnvironment = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceCallables = Map.singleton "Ping" pingSignature
  }

semanticContracts :: Map.Map DeclarationKey SourceCallableSemanticContract
semanticContracts =
  Map.singleton (DeclarationKey "decl.take") takeSemanticContract

pingContracts :: Map.Map DeclarationKey SourceCallableSemanticContract
pingContracts =
  Map.singleton (DeclarationKey "decl.ping") pingSemanticContract

validLinearInvoke :: Either String ()
validLinearInvoke = expectAccept baseWithCandidate
  "component Caller(candidate) { invoke Take(candidate) return unit }"

invokeConsumesLinear :: Either String ()
invokeConsumesLinear = expectReject StructuralUse baseWithCandidate
  "component Caller(candidate) { invoke Take(candidate) return candidate }"

unknownCallableRejects :: Either String ()
unknownCallableRejects = expectReject UnknownCallable
  (emptySurfaceEnvironment emptyStaticContext)
  "component Caller { invoke Missing() return unit }"

namespaceEnvironment :: SurfaceEnvironment
namespaceEnvironment = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceInitialBindings = Map.singleton "candidate" candidateBinding
  , surfacePrimitives = Map.singleton "Worker" PrimitiveUse
  , surfaceCallables = Map.singleton "Worker"
      (callable "decl.worker" [] Nothing)
  }

primitiveCannotRescueInvoke :: Either String ()
primitiveCannotRescueInvoke = expectReject TypeMismatch namespaceEnvironment
  "component Caller(candidate) { invoke Worker(candidate) return unit }"

ordinaryCallRemainsPrimitive :: Either String ()
ordinaryCallRemainsPrimitive = expectAccept namespaceEnvironment
  "component Caller(candidate) { Worker(candidate) return unit }"

restrictedResultReturns :: Either String ()
restrictedResultReturns = expectAccept
  ((emptySurfaceEnvironment emptyStaticContext)
    { surfaceCallables = Map.singleton "Maker"
        (callable "decl.maker" [] (Just (Linear, blobType)))
    })
  "component Caller { let result = invoke Maker() return result }"

semanticWitnessRetained :: Either String ()
semanticWitnessRetained = do
  component <- parseOne
    "component Caller(candidate) { invoke Take(candidate) return unit }"
  checked <- mapLeft show $
    checkSurfaceComponentWithCallableSemantics
      semanticContracts
      baseWithCandidate
      component
  case checkedCallableInvocations checked of
    [witness] -> do
      assert
        (surfaceInvocationDisplayName witness == "Take")
        "semantic witness lost source lookup spelling"
      assert
        (surfaceInvocationDeclarationKey witness == DeclarationKey "decl.take")
        "semantic witness lost exact DeclarationKey"
      assert
        (surfaceInvocationSemanticContract witness == takeSemanticContract)
        "semantic witness weakened or reconstructed the complete callable contract"
    witnesses -> Left
      ("expected one retained semantic invocation witness, got " <> show witnesses)

semanticOccurrencesPreserved :: Either String ()
semanticOccurrencesPreserved = do
  component <- parseOne
    "component Caller { invoke Ping() invoke Ping() return unit }"
  checked <- mapLeft show $
    checkSurfaceComponentWithCallableSemantics pingContracts pingEnvironment component
  case checkedCallableInvocations checked of
    [first, second] -> do
      assert
        (surfaceInvocationDeclarationKey first == DeclarationKey "decl.ping"
          && surfaceInvocationDeclarationKey second == DeclarationKey "decl.ping")
        "repeated calls did not retain the exact callable identity"
      assert
        (surfaceInvocationSpan first /= surfaceInvocationSpan second)
        "repeated calls collapsed to one source occurrence"
    witnesses -> Left
      ("expected two retained invocation occurrences, got " <> show witnesses)

semanticContractMissingRejects :: Either String ()
semanticContractMissingRejects = do
  component <- parseOne
    "component Caller(candidate) { invoke Take(candidate) return unit }"
  case checkSurfaceComponentWithCallableSemantics Map.empty baseWithCandidate component of
    Left err
      | surfaceErrorClass err == UnknownCallable -> Right ()
      | otherwise -> Left ("expected UnknownCallable, got " <> show err)
    Right result -> Left
      ("expected missing semantic contract rejection, got " <> show result)

semanticOrdinaryCallIgnored :: Either String ()
semanticOrdinaryCallIgnored = do
  component <- parseOne
    "component Caller(candidate) { Worker(candidate) return unit }"
  checked <- mapLeft show $
    checkSurfaceComponentWithCallableSemantics Map.empty namespaceEnvironment component
  assert
    (null (checkedCallableInvocations checked))
    "ordinary provider call was incorrectly promoted to a source callable witness"

expectAccept :: SurfaceEnvironment -> Text -> Either String ()
expectAccept environment source = do
  component <- parseOne source
  _ <- mapLeft show (checkSurfaceComponent environment component)
  Right ()

expectReject :: RejectionClass -> SurfaceEnvironment -> Text -> Either String ()
expectReject expected environment source = do
  component <- parseOne source
  case checkSurfaceComponent environment component of
    Left err
      | surfaceErrorClass err == expected -> Right ()
      | otherwise -> Left ("expected " <> show expected <> ", got " <> show err)
    Right result -> Left ("expected rejection, got acceptance: " <> show result)

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

parseOne :: Text -> Either String (Located Component)
parseOne source = do
  parsed <- mapLeft show (parseSurfaceFile "call019-surface" source)
  case surfaceComponents parsed of
    [component] -> Right component
    components -> Left ("expected one component, got " <> show (length components))

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
