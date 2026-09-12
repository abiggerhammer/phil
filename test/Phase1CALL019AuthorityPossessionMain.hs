{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Compiler.CallableAuthorityPossession
  ( CallableAuthorityPossessionBinding (..)
  , CallableAuthorityPossessionError (..)
  , CheckedCallableAuthorityPossession (..)
  , CheckedSurfaceCallableAuthorityContext (..)
  , SurfaceCallableAuthorityContextError (..)
  , checkSurfaceComponentWithAuthorityPossession
  )
import Phil.Compiler.CallableInvocationContext
  ( SurfaceCallableInvocationContextError (..)
  )
import Phil.Core.Authority
  ( AuthorityCapability (..)
  , AuthorityCheckError (..)
  , AuthorityContractKey (..)
  , AuthorityOperationKey (..)
  , AuthorityRequirement (..)
  , AuthoritySubjectKey (..)
  , CapabilityOccurrenceKey (..)
  , CheckedAuthorityExercise (..)
  , emptyAuthorityState
  , insertAuthorityCapability
  )
import Phil.Core.Callable
  ( CallableCheckError (..)
  , CallableContract (..)
  , CalleeTransition (..)
  , SemanticEffect (..)
  )
import Phil.Core.CallableOutcome
  ( CallableOutcomeClass (..)
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
import Phil.Core.Syntax (Mode (..))
import Phil.Surface.Check
  ( SurfaceCallableSignature (..)
  , SurfaceEnvironment (..)
  , emptySurfaceEnvironment
  )
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Syntax (Component, Located, SurfaceFile (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-019 authority bridge accepts exact possessed capability" exactPossessionAccepts
    , test "CALL-019 authority bridge rejects missing explicit binding" missingBindingRejects
    , test "CALL-019 authority bridge rejects callable-label substitution" bindingKeyMismatchRejects
    , test "CALL-019 authority bridge rejects wrong exact authority subject" subjectMismatchRejects
    , test "CALL-019 authority bridge rejects unavailable capability occurrence" unknownOccurrenceRejects
    , test "CALL-019 authority possession cannot bypass caller effect bound" effectBoundStillRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

callableAuthority :: CallableAuthorityRequirement
callableAuthority = CallableAuthorityRequirement "caller.storage.write"

otherCallableAuthority :: CallableAuthorityRequirement
otherCallableAuthority = CallableAuthorityRequirement "caller.storage.read"

contractKey :: AuthorityContractKey
contractKey = AuthorityContractKey "storage.v1"

subjectKey, wrongSubjectKey :: AuthoritySubjectKey
subjectKey = AuthoritySubjectKey "blob:subject-001"
wrongSubjectKey = AuthoritySubjectKey "blob:subject-002"

operationKey :: AuthorityOperationKey
operationKey = AuthorityOperationKey "write"

capabilityKey, missingCapabilityKey :: CapabilityOccurrenceKey
capabilityKey = CapabilityOccurrenceKey "capability:storage-write-001"
missingCapabilityKey = CapabilityOccurrenceKey "capability:missing"

exactRequirement :: AuthorityRequirement
exactRequirement = AuthorityRequirement
  { requiredAuthorityContract = contractKey
  , requiredAuthoritySubject = subjectKey
  , requiredAuthorityOperation = operationKey
  }

exactCapability :: AuthorityCapability
exactCapability = AuthorityCapability
  { authorityCapabilityOccurrence = capabilityKey
  , authorityCapabilityContract = contractKey
  , authorityCapabilitySubject = subjectKey
  , authorityCapabilityMode = Unrestricted
  , authorityCapabilityOperations = Set.singleton operationKey
  }

authorityState = mapLeft show $
  insertAuthorityCapability exactCapability emptyAuthorityState

binding :: CallableAuthorityPossessionBinding
binding = CallableAuthorityPossessionBinding
  { callableAuthorityBindingRequirement = callableAuthority
  , callableAuthorityBindingExactRequirement = exactRequirement
  , callableAuthorityBindingCapabilityOccurrence = capabilityKey
  }

bindingMap :: Map.Map CallableAuthorityRequirement CallableAuthorityPossessionBinding
bindingMap = Map.singleton callableAuthority binding

writeEffect :: SemanticEffect
writeEffect = SemanticEffect "effect:write"

callableKey :: DeclarationKey
callableKey = DeclarationKey "decl.write"

semanticContract :: SourceCallableSemanticContract
semanticContract = SourceCallableSemanticContract
  { sourceCallableRefinementSurface = CallableRefinementSurface
      { callableRefinementMachineShape = CallableMachineShape "Unit->Unit"
      , callableRefinementContract = CallableContract
          { callableContractInterfaceRevision = InterfaceRevision "write.v1"
          , callableContractCalleeTransition = PreserveCallee
          , callableContractEffectBound = Set.singleton writeEffect
          }
      , callableRefinementCallerAuthority = Set.singleton callableAuthority
      , callableRefinementFailures = Set.empty
      }
  , sourceCallableOutcomeContracts =
      [ CallableOutcomeContract
          { callableOutcomeClass = CallableSuccessOutcome
          , callableOutcomeState = CallableOutcomeState "write.success"
          , callableOutcomeCalleeTransition = PreserveCallee
          , callableOutcomePostconditions = Set.empty
          , callableOutcomeResidualObligations = Set.empty
          , callableOutcomeAssumptions = Set.empty
          , callableOutcomeEffects = Set.empty
          , callableOutcomeDischargedFacts = Set.empty
          }
      ]
  }

contracts :: Map.Map DeclarationKey SourceCallableSemanticContract
contracts = Map.singleton callableKey semanticContract

environment :: SurfaceEnvironment
environment = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceCallables = Map.singleton "Write" SurfaceCallableSignature
      { surfaceCallableDeclarationKey = callableKey
      , surfaceCallableParameters = []
      , surfaceCallableResult = Nothing
      }
  }

callerContract :: Set.Set SemanticEffect -> CallableRefinementSurface
callerContract effects = CallableRefinementSurface
  { callableRefinementMachineShape = CallableMachineShape "Caller"
  , callableRefinementContract = CallableContract
      { callableContractInterfaceRevision = InterfaceRevision "caller.v1"
      , callableContractCalleeTransition = PreserveCallee
      , callableContractEffectBound = effects
      }
  , callableRefinementCallerAuthority = Set.empty
  , callableRefinementFailures = Set.empty
  }

source :: Text
source = "component Caller { invoke Write() return unit }"

exactPossessionAccepts :: Either String ()
exactPossessionAccepts = do
  state <- authorityState
  component <- parseOne source
  checked <- mapLeft show $
    checkSurfaceComponentWithAuthorityPossession
      contracts bindingMap state (callerContract (Set.singleton writeEffect))
      environment component
  case checkedSurfaceCallableAuthorityPossessions checked of
    [possession] -> do
      assert
        (checkedCallableAuthorityRequirement possession == callableAuthority)
        "checked possession lost opaque callable authority identity"
      assert
        (checkedAuthorityRequirement
          (checkedCallableAuthorityExercise possession) == exactRequirement)
        "checked possession lost exact Core authority requirement"
      assert
        (authorityCapabilityOccurrence
          (checkedAuthorityCapability
            (checkedCallableAuthorityExercise possession)) == capabilityKey)
        "checked possession lost exact capability occurrence"
    possessions -> Left ("expected one checked authority possession, got " <> show possessions)

missingBindingRejects :: Either String ()
missingBindingRejects = do
  state <- authorityState
  expectError
    (\err -> case err of
      SurfaceCallableAuthorityPossessionRejected
        (CallableAuthorityBindingMissing requirement) -> requirement == callableAuthority
      _ -> False)
    Map.empty state (callerContract (Set.singleton writeEffect))
    "missing explicit authority binding"

bindingKeyMismatchRejects :: Either String ()
bindingKeyMismatchRejects = do
  state <- authorityState
  let substituted = binding
        { callableAuthorityBindingRequirement = otherCallableAuthority }
  expectError
    (\err -> case err of
      SurfaceCallableAuthorityPossessionRejected
        (CallableAuthorityBindingKeyMismatch expected actual) ->
          expected == callableAuthority && actual == otherCallableAuthority
      _ -> False)
    (Map.singleton callableAuthority substituted)
    state
    (callerContract (Set.singleton writeEffect))
    "callable authority key substitution"

subjectMismatchRejects :: Either String ()
subjectMismatchRejects = do
  state <- authorityState
  let wrongRequirement = exactRequirement
        { requiredAuthoritySubject = wrongSubjectKey }
      wrongBinding = binding
        { callableAuthorityBindingExactRequirement = wrongRequirement }
  expectError
    (\err -> case err of
      SurfaceCallableAuthorityPossessionRejected
        (CallableAuthorityExerciseRejected requirement
          (AuthoritySubjectMismatch expected actual)) ->
            requirement == callableAuthority
              && expected == wrongSubjectKey
              && actual == subjectKey
      _ -> False)
    (Map.singleton callableAuthority wrongBinding)
    state
    (callerContract (Set.singleton writeEffect))
    "exact subject mismatch"

unknownOccurrenceRejects :: Either String ()
unknownOccurrenceRejects = do
  state <- authorityState
  let wrongBinding = binding
        { callableAuthorityBindingCapabilityOccurrence = missingCapabilityKey }
  expectError
    (\err -> case err of
      SurfaceCallableAuthorityPossessionRejected
        (CallableAuthorityExerciseRejected requirement
          (UnknownCapabilityOccurrence occurrence)) ->
            requirement == callableAuthority
              && occurrence == missingCapabilityKey
      _ -> False)
    (Map.singleton callableAuthority wrongBinding)
    state
    (callerContract (Set.singleton writeEffect))
    "unknown capability occurrence"

effectBoundStillRejects :: Either String ()
effectBoundStillRejects = do
  state <- authorityState
  expectError
    (\err -> case err of
      SurfaceCallableAuthorityInvocationContextRejected
        (SurfaceInvocationEffectRejected
          (CallableEffectBoundExceeded _ extra bound)) ->
            extra == Set.singleton writeEffect && Set.null bound
      _ -> False)
    bindingMap state (callerContract Set.empty)
    "caller effect bound"

expectError
  :: (SurfaceCallableAuthorityContextError -> Bool)
  -> Map.Map CallableAuthorityRequirement CallableAuthorityPossessionBinding
  -> Phil.Core.Authority.AuthorityState
  -> CallableRefinementSurface
  -> String
  -> Either String ()
expectError predicate bindings state publicContract label = do
  component <- parseOne source
  case checkSurfaceComponentWithAuthorityPossession
      contracts bindings state publicContract environment component of
    Left err | predicate err -> Right ()
    Left err -> Left ("unexpected " <> label <> " error: " <> show err)
    Right result -> Left ("expected " <> label <> " rejection, got " <> show result)

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

parseOne :: Text -> Either String (Located Component)
parseOne sourceText = do
  parsed <- mapLeft show (parseSurfaceFile "call019-authority-possession" sourceText)
  case surfaceComponents parsed of
    [component] -> Right component
    components -> Left ("expected one component, got " <> show (length components))

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
