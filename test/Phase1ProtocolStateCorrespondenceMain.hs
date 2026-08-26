{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Examples.Phase1.ProtocolStateWitnesses
import Phil.Systems.IR (BlockId (..))
import Phil.Systems.ProtocolStateCorrespondence
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SYS-009 upload protocol lineage accepts" uploadLineageAccepts
    , test "SYS-009 one physical handle may realize many endpoint occurrences" sameHandleDistinctOccurrences
    , test "SYS-009 equal local session cannot cross protocol instance" equalSessionDifferentInstanceRejected
    , test "SYS-009 successor role drift rejects" successorRoleMismatchRejected
    , test "SYS-009 stale predecessor cannot be its own successor" staleSelfSuccessorRejected
    , test "SYS-009 consumed endpoint occurrence cannot drive a second transition" duplicateConsumptionRejected
    , test "SYS-009 cyclic endpoint lineage rejects resurrection" lineageCycleRejected
    , test "SYS-009 transport coincidence is not protocol correspondence" transportCoincidenceRejected
    , test "SYS-009 legacy runtime protocol call needs explicit opaque bridge" opaqueBridgeRequired
    , test "SYS-009 typed protocol construct rejects opaque bridge" typedBasisRequired
    , test "SYS-009 typed receive commit preserves exact message state" receiveCommitMessageMismatchRejected
    , test "SYS-009 exact receive must account for success and failure" exactReceiveOutcomeDomainRejected
    , test "SYS-009 protocol state stage identity is deterministic" deterministicIdentity
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

uploadLineageAccepts :: Either String ()
uploadLineageAccepts = uploadBundle >>= mapLeft show . verifyProtocolStateStageBundle

sameHandleDistinctOccurrences :: Either String ()
sameHandleDistinctOccurrences = do
  bundle <- uploadBundle
  let transitions = Map.elems (protocolStateStageTransitions bundle)
      transports = Set.fromList (map protocolTransitionTransport transitions)
      predecessors = Set.fromList (map protocolTransitionPredecessor transitions)
  assert (transports == Set.singleton uploadServerTransport)
    "upload protocol transitions did not share the one physical transport"
  assert (Set.size predecessors == length transitions)
    "distinct semantic transitions reused an endpoint occurrence"
  assert (Set.size (Map.keysSet (protocolStateStageEndpoints bundle)) == 7)
    "unexpected endpoint occurrence count"
  mapLeft show (verifyProtocolStateStageBundle bundle)

equalSessionDifferentInstanceRejected :: Either String ()
equalSessionDifferentInstanceRejected = do
  bundle <- uploadBundle
  predecessor <- lookupEndpoint serverEp5 bundle
  successor <- lookupEndpoint serverEp6 bundle
  let successor' = successor
        { protocolEndpointInstance = ProtocolInstanceRevision "protocol.other.instance.v1"
        , protocolEndpointSession = protocolEndpointSession predecessor
        }
      mutated = replaceEndpoint serverEp6 successor' bundle
  case verifyProtocolStateStageBundle mutated of
    Left (ProtocolTransitionInstanceMismatch key occurrence expected actual) -> do
      assert (key == protocolTransitionKey receivePayloadTransition)
        "wrong transition reported for instance mismatch"
      assert (occurrence == serverEp6) "wrong successor occurrence"
      assert (expected == uploadProtocolInstance) "wrong expected protocol instance"
      assert (actual == ProtocolInstanceRevision "protocol.other.instance.v1")
        "wrong substituted protocol instance"
    other -> Left ("equal local session repaired protocol-instance mismatch: " <> show other)

successorRoleMismatchRejected :: Either String ()
successorRoleMismatchRejected = do
  bundle <- uploadBundle
  successor <- lookupEndpoint serverEp6 bundle
  let successor' = successor { protocolEndpointRole = ProtocolRoleKey "client" }
      mutated = replaceEndpoint serverEp6 successor' bundle
  case verifyProtocolStateStageBundle mutated of
    Left (ProtocolTransitionRoleMismatch key occurrence expected actual) -> do
      assert (key == protocolTransitionKey receivePayloadTransition)
        "wrong transition reported for role mismatch"
      assert (occurrence == serverEp6) "wrong role-mismatch successor"
      assert (expected == uploadServerRole) "wrong expected role"
      assert (actual == ProtocolRoleKey "client") "wrong substituted role"
    other -> Left ("role mismatch was accepted: " <> show other)

staleSelfSuccessorRejected :: Either String ()
staleSelfSuccessorRejected = do
  bundle <- uploadBundle
  let changed = receivePayloadTransition
        { protocolTransitionOutcomes = Map.fromList
            [ ("success", ProtocolSuccessor serverEp5)
            , ("failure", ProtocolTerminal "EarlyEOF")
            ]
        }
      mutated = replaceTransition changed bundle
  case verifyProtocolStateStageBundle mutated of
    Left (ProtocolTransitionReusesPredecessorAsSuccessor key occurrence) -> do
      assert (key == protocolTransitionKey receivePayloadTransition)
        "wrong stale-self transition"
      assert (occurrence == serverEp5) "wrong resurrected predecessor"
    other -> Left ("consumed predecessor survived as its own successor: " <> show other)

duplicateConsumptionRejected :: Either String ()
duplicateConsumptionRejected = do
  bundle <- uploadBundle
  let stale = ProtocolTransitionBinding
        { protocolTransitionKey = ProtocolTransitionKey "upload.server.stale-second-use"
        , protocolTransitionPredecessor = serverEp5
        , protocolTransitionAction = ProtocolOpaqueAction "upload.server.stale-second-use"
        , protocolTransitionTargetSite = ProtocolOperationSite
            "UploadServer" (BlockId "server.digest_mismatch") 1
        , protocolTransitionTransport = uploadServerTransport
        , protocolTransitionOutcomes = Map.singleton "terminal" (ProtocolTerminal "failure")
        , protocolTransitionBasis = CheckedLegacyOpaqueProtocolBridge
            "phase0.endpoint.typestate.stale-use-negative.v1"
        }
      mutated = addTransition stale bundle
  case verifyProtocolStateStageBundle mutated of
    Left (ProtocolEndpointConsumedMoreThanOnce occurrence keys) -> do
      assert (occurrence == serverEp5) "wrong multiply consumed endpoint"
      assert (keys == Set.fromList
        [ protocolTransitionKey receivePayloadTransition
        , protocolTransitionKey stale
        ]) "wrong duplicate-consumer set"
    other -> Left ("consumed endpoint drove a second transition: " <> show other)

lineageCycleRejected :: Either String ()
lineageCycleRejected = do
  bundle <- uploadBundle
  let endpointA = EndpointOccurrenceKey "cycle.endpoint.a"
      endpointB = EndpointOccurrenceKey "cycle.endpoint.b"
      state occurrence = ProtocolEndpointState
        { protocolEndpointOccurrence = occurrence
        , protocolEndpointInstance = uploadProtocolInstance
        , protocolEndpointRole = uploadServerRole
        , protocolEndpointSession = LocalSessionRevision "cycle.session"
        }
      transitionA = cycleTransition
        "cycle.transition.a" endpointA endpointB
        (ProtocolOperationSite "UploadServer" (BlockId "server.reject") 0)
      transitionB = cycleTransition
        "cycle.transition.b" endpointB endpointA
        (ProtocolOperationSite "UploadServer" (BlockId "server.digest_mismatch") 1)
      cycleBundle = makeProtocolStateStageBundle
        (protocolStateStageBase bundle)
        (Map.fromList [(endpointA, state endpointA), (endpointB, state endpointB)])
        (Map.fromList
          [ (protocolTransitionKey transitionA, transitionA)
          , (protocolTransitionKey transitionB, transitionB)
          ])
  case verifyProtocolStateStageBundle cycleBundle of
    Left (ProtocolEndpointLineageCycle occurrence) ->
      assert (occurrence == endpointA || occurrence == endpointB)
        "cycle diagnostic named an unrelated endpoint"
    other -> Left ("cyclic endpoint lineage was accepted: " <> show other)

cycleTransition
  :: Text
  -> EndpointOccurrenceKey
  -> EndpointOccurrenceKey
  -> ProtocolTargetSite
  -> ProtocolTransitionBinding
cycleTransition key predecessor successor site = ProtocolTransitionBinding
  { protocolTransitionKey = ProtocolTransitionKey key
  , protocolTransitionPredecessor = predecessor
  , protocolTransitionAction = ProtocolOpaqueAction key
  , protocolTransitionTargetSite = site
  , protocolTransitionTransport = uploadServerTransport
  , protocolTransitionOutcomes = Map.singleton "success" (ProtocolSuccessor successor)
  , protocolTransitionBasis = CheckedLegacyOpaqueProtocolBridge
      "phase0.endpoint.typestate.cycle-negative.v1"
  }

transportCoincidenceRejected :: Either String ()
transportCoincidenceRejected = do
  bundle <- uploadBundle
  let changed = receiveHelloTransition
        { protocolTransitionBasis = RuntimeTransportCoincidence "same server.transport handle" }
      mutated = replaceTransition changed bundle
  case verifyProtocolStateStageBundle mutated of
    Left (ProtocolTransitionRuntimeCoincidenceRejected key _) ->
      assert (key == protocolTransitionKey receiveHelloTransition)
        "wrong runtime-coincidence transition"
    other -> Left ("transport coincidence was accepted as protocol identity: " <> show other)

opaqueBridgeRequired :: Either String ()
opaqueBridgeRequired = do
  bundle <- uploadBundle
  let changed = selectVersionTransition
        { protocolTransitionBasis = CheckedProtocolCorrespondence
            "incorrectly-typed-legacy-site.v1" }
      mutated = replaceTransition changed bundle
  case verifyProtocolStateStageBundle mutated of
    Left (ProtocolTransitionOpaqueBridgeRequired key) ->
      assert (key == protocolTransitionKey selectVersionTransition)
        "wrong opaque-bridge transition"
    other -> Left ("legacy runtime call acquired protocol semantics without bridge: " <> show other)

typedBasisRequired :: Either String ()
typedBasisRequired = do
  bundle <- uploadBundle
  let changed = receiveHelloTransition
        { protocolTransitionBasis = CheckedLegacyOpaqueProtocolBridge
            "opaque-bridge-on-typed-site.v1" }
      mutated = replaceTransition changed bundle
  case verifyProtocolStateStageBundle mutated of
    Left (ProtocolTransitionTypedBasisRequired key) ->
      assert (key == protocolTransitionKey receiveHelloTransition)
        "wrong typed-basis transition"
    other -> Left ("typed protocol construct accepted opaque bridge: " <> show other)

receiveCommitMessageMismatchRejected :: Either String ()
receiveCommitMessageMismatchRejected = do
  bundle <- uploadBundle
  let changed = receiveHelloTransition
        { protocolTransitionAction = ProtocolReceiveCommit "Begin" }
      mutated = replaceTransition changed bundle
  case verifyProtocolStateStageBundle mutated of
    Left (ProtocolTransitionActionMismatch key action) -> do
      assert (key == protocolTransitionKey receiveHelloTransition)
        "wrong receive-message transition"
      assert (action == ProtocolReceiveCommit "Begin") "wrong mismatched action"
    other -> Left ("receive commit changed message state silently: " <> show other)

exactReceiveOutcomeDomainRejected :: Either String ()
exactReceiveOutcomeDomainRejected = do
  bundle <- uploadBundle
  let changed = receivePayloadTransition
        { protocolTransitionOutcomes = Map.singleton
            "success" (ProtocolSuccessor serverEp6) }
      mutated = replaceTransition changed bundle
  case verifyProtocolStateStageBundle mutated of
    Left (ProtocolTransitionOutcomeDomainMismatch key expected actual) -> do
      assert (key == protocolTransitionKey receivePayloadTransition)
        "wrong exact-receive transition"
      assert (expected == Set.fromList ["success", "failure"])
        "wrong exact receive target outcome domain"
      assert (actual == Set.singleton "success") "failure outcome was not removed"
    other -> Left ("incomplete exact receive outcome domain was accepted: " <> show other)

deterministicIdentity :: Either String ()
deterministicIdentity = do
  bundle <- uploadBundle
  let endpoints = Map.fromList (reverse (Map.toAscList (protocolStateStageEndpoints bundle)))
      transitions = Map.fromList (reverse (Map.toAscList (protocolStateStageTransitions bundle)))
      rebuilt = makeProtocolStateStageBundle (protocolStateStageBase bundle) endpoints transitions
  assert (protocolStateStageRevision rebuilt == protocolStateStageRevision bundle)
    "protocol state stage revision changed with map ordering"
  mapLeft show (verifyProtocolStateStageBundle rebuilt)

uploadBundle :: Either String ProtocolStateStageBundle
uploadBundle = uploadProtocolStateStageBundle

lookupEndpoint
  :: EndpointOccurrenceKey
  -> ProtocolStateStageBundle
  -> Either String ProtocolEndpointState
lookupEndpoint key bundle = maybe
  (Left ("missing endpoint: " <> show key))
  Right
  (Map.lookup key (protocolStateStageEndpoints bundle))

replaceEndpoint
  :: EndpointOccurrenceKey
  -> ProtocolEndpointState
  -> ProtocolStateStageBundle
  -> ProtocolStateStageBundle
replaceEndpoint key endpoint bundle = makeProtocolStateStageBundle
  (protocolStateStageBase bundle)
  (Map.insert key endpoint (protocolStateStageEndpoints bundle))
  (protocolStateStageTransitions bundle)

replaceTransition
  :: ProtocolTransitionBinding
  -> ProtocolStateStageBundle
  -> ProtocolStateStageBundle
replaceTransition transition bundle = makeProtocolStateStageBundle
  (protocolStateStageBase bundle)
  (protocolStateStageEndpoints bundle)
  (Map.insert (protocolTransitionKey transition) transition
    (protocolStateStageTransitions bundle))

addTransition
  :: ProtocolTransitionBinding
  -> ProtocolStateStageBundle
  -> ProtocolStateStageBundle
addTransition = replaceTransition

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
