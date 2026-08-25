{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Callable
import Phil.Core.CallableRecursion
import Phil.Core.CallableRefinement
import Phil.Core.Static (DefinitionRevision (..), InterfaceRevision (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-013 self recursion resolves stabilized public contract" selfRecursionUsesPublicContract
    , test "CALL-013 mutual recursion sees whole stabilized group" mutualRecursionUsesPublicContracts
    , test "CALL-013 declaration order is nonsemantic" groupOrderingIsCanonical
    , test "CALL-013 body revision is absent from recursive hypothesis" bodyRevisionDoesNotChangeHypothesis
    , test "CALL-013 narrower current body does not narrow recursive effects" bodyEffectsDoNotNarrowPublicHypothesis
    , test "CALL-013 stale recursive interface revision rejects" staleRecursiveRevisionRejects
    , test "unknown recursive target rejects" unknownRecursiveTargetRejects
    , test "duplicate named callable identity rejects" duplicateNamedCallableRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

selfRecursionUsesPublicContract :: Either String ()
selfRecursionUsesPublicContract = do
  environment <- mapLeft show (stabilizeRecursiveCallableGroup [readerDefinition])
  surface <- mapLeft show
    (lookupRecursiveCallableSurface readerKey readerInterface environment)
  assert (surface == readerSurface)
    "self-recursive lookup did not return exact stabilized public surface"

mutualRecursionUsesPublicContracts :: Either String ()
mutualRecursionUsesPublicContracts = do
  environment <- mapLeft show
    (stabilizeRecursiveCallableGroup [readerDefinition, auditDefinition])
  reader <- mapLeft show
    (lookupRecursiveCallableSurface readerKey readerInterface environment)
  audit <- mapLeft show
    (lookupRecursiveCallableSurface auditKey auditInterface environment)
  assert (reader == readerSurface) "mutual group lost reader contract"
  assert (audit == auditSurface) "mutual group lost audit contract"

groupOrderingIsCanonical :: Either String ()
groupOrderingIsCanonical = do
  left <- mapLeft show
    (stabilizeRecursiveCallableGroup [readerDefinition, auditDefinition])
  right <- mapLeft show
    (stabilizeRecursiveCallableGroup [auditDefinition, readerDefinition])
  assert (left == right) "recursive declaration order changed stabilized environment"

bodyRevisionDoesNotChangeHypothesis :: Either String ()
bodyRevisionDoesNotChangeHypothesis = do
  first <- mapLeft show (stabilizeRecursiveCallableGroup [readerDefinition])
  second <- mapLeft show (stabilizeRecursiveCallableGroup
    [ readerDefinition
        { namedCallableDefinitionRevision = DefinitionRevision "reader.definition.v2"
        , namedCallableCurrentBodyEffects = Set.empty
        }
    ])
  assert (first == second)
    "current implementation revision/effect summary leaked into recursive hypothesis"

bodyEffectsDoNotNarrowPublicHypothesis :: Either String ()
bodyEffectsDoNotNarrowPublicHypothesis = do
  environment <- mapLeft show (stabilizeRecursiveCallableGroup
    [readerDefinition { namedCallableCurrentBodyEffects = Set.empty }])
  surface <- mapLeft show
    (lookupRecursiveCallableSurface readerKey readerInterface environment)
  assert
    (callableContractEffectBound (callableRefinementContract surface)
      == Set.singleton readEffect)
    "recursive call observed narrower current-body effects instead of public bound"

staleRecursiveRevisionRejects :: Either String ()
staleRecursiveRevisionRejects = do
  environment <- mapLeft show (stabilizeRecursiveCallableGroup [readerDefinition])
  case lookupRecursiveCallableSurface
      readerKey
      (InterfaceRevision "reader.interface.old")
      environment of
    Left (RecursiveCallableInterfaceRevisionMismatch key expected actual) -> do
      assert (key == readerKey) "stale-revision diagnostic named wrong callable"
      assert (expected == InterfaceRevision "reader.interface.old")
        "stale-revision diagnostic lost requested revision"
      assert (actual == readerInterface)
        "stale-revision diagnostic lost stabilized revision"
    other -> Left ("stale recursive interface unexpectedly accepted: " <> show other)

unknownRecursiveTargetRejects :: Either String ()
unknownRecursiveTargetRejects = do
  environment <- mapLeft show (stabilizeRecursiveCallableGroup [readerDefinition])
  let missing = NamedCallableKey "callable.missing"
  case lookupRecursiveCallableSurface missing readerInterface environment of
    Left (UnknownRecursiveCallable key) ->
      assert (key == missing) "unknown-recursive diagnostic named wrong target"
    other -> Left ("unknown recursive target unexpectedly accepted: " <> show other)

duplicateNamedCallableRejects :: Either String ()
duplicateNamedCallableRejects =
  case stabilizeRecursiveCallableGroup [readerDefinition, readerDefinition] of
    Left (DuplicateNamedCallableDefinition key) ->
      assert (key == readerKey) "duplicate diagnostic named wrong callable"
    other -> Left ("duplicate recursive declaration unexpectedly accepted: " <> show other)

readerKey, auditKey :: NamedCallableKey
readerKey = NamedCallableKey "callable.reader"
auditKey = NamedCallableKey "callable.audit"

readerInterface, auditInterface :: InterfaceRevision
readerInterface = InterfaceRevision "reader.interface.v1"
auditInterface = InterfaceRevision "audit.interface.v1"

readEffect, auditEffect :: SemanticEffect
readEffect = SemanticEffect "read"
auditEffect = SemanticEffect "audit"

readerDefinition, auditDefinition :: NamedCallableDefinition
readerDefinition = NamedCallableDefinition
  { namedCallableKey = readerKey
  , namedCallablePublicSurface = readerSurface
  , namedCallableDefinitionRevision = DefinitionRevision "reader.definition.v1"
  , namedCallableCurrentBodyEffects = Set.empty
  }

auditDefinition = NamedCallableDefinition
  { namedCallableKey = auditKey
  , namedCallablePublicSurface = auditSurface
  , namedCallableDefinitionRevision = DefinitionRevision "audit.definition.v1"
  , namedCallableCurrentBodyEffects = Set.singleton auditEffect
  }

readerSurface, auditSurface :: CallableRefinementSurface
readerSurface = CallableRefinementSurface
  { callableRefinementMachineShape = CallableMachineShape "unit->unit"
  , callableRefinementContract = CallableContract
      { callableContractInterfaceRevision = readerInterface
      , callableContractCalleeTransition = PreserveCallee
      , callableContractEffectBound = Set.singleton readEffect
      }
  , callableRefinementCallerAuthority = Set.empty
  , callableRefinementFailures = Set.empty
  }

auditSurface = CallableRefinementSurface
  { callableRefinementMachineShape = CallableMachineShape "unit->unit"
  , callableRefinementContract = CallableContract
      { callableContractInterfaceRevision = auditInterface
      , callableContractCalleeTransition = PreserveCallee
      , callableContractEffectBound = Set.singleton auditEffect
      }
  , callableRefinementCallerAuthority = Set.empty
  , callableRefinementFailures = Set.empty
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
