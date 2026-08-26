{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Phil.Examples.Phase1.BoundaryCommitWitnesses
import Phil.Examples.Phase1.ProtocolStateWitnesses
  ( receivePayloadTransition
  , serverEp6
  )
import Phil.Examples.Phase1.SubjectWitnesses
  ( uploadPayloadSubject
  )
import Phil.Systems.BoundaryCommitCorrespondence
import Phil.Systems.IR (BlockId (..), ValueId (..))
import Phil.Systems.ProtocolStateCorrespondence
import Phil.Systems.SubjectCorrespondence (SystemsValueRef (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SYS-010 upload receive/send boundary correspondence accepts" baselineAccepts
    , test "SYS-010 borrowed receive view cannot replace exact owner" borrowedReceiveOwnerRejected
    , test "SYS-010 receive must use exact length value" wrongReceiveLengthRejected
    , test "SYS-010 send owner must denote exact byte subject" wrongSendSubjectRejected
    , test "SYS-010 send length must match owner index" wrongSendLengthIndexRejected
    , test "SYS-010 send runtime site must bind exact source fact" wrongSendSourceFactRejected
    , test "SYS-010 send successor cannot commit before complete emission" earlySendSuccessorRejected
    , test "SYS-010 send commit outcome must produce successor" sendTerminalCommitRejected
    , test "SYS-010 receive failure must remain terminal" receiveFailureSuccessorRejected
    , test "SYS-010 boundary stage identity is deterministic" deterministicIdentity
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

baselineAccepts :: Either String ()
baselineAccepts = bundle >>= mapLeft show . verifyBoundaryCommitStageBundle

borrowedReceiveOwnerRejected :: Either String ()
borrowedReceiveOwnerRejected = do
  original <- bundle
  let borrowed = SystemsValueRef "UploadServer" (ValueId "server.payload_view")
      changed = uploadReceiveTransfer { boundaryTransferOwner = borrowed }
      mutated = replaceTransfer changed original
  case verifyBoundaryCommitStageBundle mutated of
    Left (BoundaryTransferValueNotOwner key ref _) -> do
      assert (key == boundaryTransferKey uploadReceiveTransfer) "wrong receive transfer"
      assert (ref == borrowed) "wrong borrowed receive value"
    other -> Left ("borrowed receive view was accepted as owner: " <> show other)

wrongReceiveLengthRejected :: Either String ()
wrongReceiveLengthRejected = do
  original <- bundle
  let wrongLength = SystemsValueRef "UploadServer" (ValueId "server.has_version")
      changed = uploadReceiveTransfer
        { boundaryTransferLength = ExplicitBoundaryLength "begin.length" wrongLength }
      mutated = replaceTransfer changed original
  case verifyBoundaryCommitStageBundle mutated of
    Left (BoundaryTransferLengthValueMismatch key expected actual) -> do
      assert (key == boundaryTransferKey uploadReceiveTransfer) "wrong receive length transfer"
      assert (expected == wrongLength) "wrong expected substituted length"
      assert (actual == SystemsValueRef "UploadServer" (ValueId "server.begin_length"))
        "wrong actual exact receive length"
    other -> Left ("wrong receive length was accepted: " <> show other)

wrongSendSubjectRejected :: Either String ()
wrongSendSubjectRejected = do
  original <- bundle
  let changed = uploadSendTransfer { boundaryTransferSubject = uploadPayloadSubject }
      mutated = replaceTransfer changed original
  case verifyBoundaryCommitStageBundle mutated of
    Left (BoundaryTransferSubjectMismatch key subject ref) -> do
      assert (key == boundaryTransferKey uploadSendTransfer) "wrong send subject transfer"
      assert (subject == uploadPayloadSubject) "wrong substituted send subject"
      assert (ref == SystemsValueRef "UploadClient" (ValueId "client.payload"))
        "wrong send owner in subject mismatch"
    other -> Left ("server payload subject was accepted for client send: " <> show other)

wrongSendLengthIndexRejected :: Either String ()
wrongSendLengthIndexRejected = do
  original <- bundle
  let changed = uploadSendTransfer
        { boundaryTransferLength = OwnerIndexedBoundaryLength
            "other.length" "Bytes[other.length]" }
      mutated = replaceTransfer changed original
  case verifyBoundaryCommitStageBundle mutated of
    Left (BoundaryTransferLengthModeMismatch key BoundarySendExact _) ->
      assert (key == boundaryTransferKey uploadSendTransfer) "wrong send length transfer"
    other -> Left ("wrong owner-indexed send length was accepted: " <> show other)

wrongSendSourceFactRejected :: Either String ()
wrongSendSourceFactRejected = do
  original <- bundle
  let changed = uploadSendTransfer
        { boundaryTransferSourceFact = "payload.exact_receive" }
      mutated = replaceTransfer changed original
  case verifyBoundaryCommitStageBundle mutated of
    Left (BoundaryTransferRuntimeRevisionMismatch key _ _) ->
      assert (key == boundaryTransferKey uploadSendTransfer) "wrong send source-fact transfer"
    other -> Left ("receive boundary evidence justified send boundary: " <> show other)

earlySendSuccessorRejected :: Either String ()
earlySendSuccessorRejected = do
  original <- bundle
  let base = boundaryCommitStageBase original
      early = uploadClientSendTransition
        { protocolTransitionTargetSite = ProtocolOperationSite
            "UploadClient" (BlockId "client.payload") 0 }
      changedBase = replaceProtocolTransition early base
      mutated = makeBoundaryCommitStageBundle changedBase
        (boundaryCommitStageTransfers original)
  case verifyBoundaryCommitStageBundle mutated of
    Left (BoundaryTransferProtocolTargetMismatch key expected actual) -> do
      assert (key == boundaryTransferKey uploadSendTransfer) "wrong early-send transfer"
      assert (expected == boundaryTransferTargetSite uploadSendTransfer)
        "wrong exact send commit site"
      assert (actual == protocolTransitionTargetSite early)
        "wrong premature protocol commit site"
    other -> Left ("send successor existed before complete emission: " <> show other)

sendTerminalCommitRejected :: Either String ()
sendTerminalCommitRejected = do
  original <- bundle
  let base = boundaryCommitStageBase original
      changedTransition = uploadClientSendTransition
        { protocolTransitionOutcomes = Map.singleton
            "success" (ProtocolTerminal "sent-without-successor") }
      changedBase = replaceProtocolTransition changedTransition base
      mutated = makeBoundaryCommitStageBundle changedBase
        (boundaryCommitStageTransfers original)
  case verifyBoundaryCommitStageBundle mutated of
    Left (BoundaryTransferCommitOutcomeNotSuccessor key "success" _) ->
      assert (key == boundaryTransferKey uploadSendTransfer) "wrong send commit transfer"
    other -> Left ("terminal send commit was accepted without successor endpoint: " <> show other)

receiveFailureSuccessorRejected :: Either String ()
receiveFailureSuccessorRejected = do
  original <- bundle
  let base = boundaryCommitStageBase original
      changedTransition = receivePayloadTransition
        { protocolTransitionOutcomes = Map.fromList
            [ ("success", ProtocolSuccessor serverEp6)
            , ("failure", ProtocolSuccessor serverEp6)
            ] }
      changedBase = replaceProtocolTransition changedTransition base
      mutated = makeBoundaryCommitStageBundle changedBase
        (boundaryCommitStageTransfers original)
  case verifyBoundaryCommitStageBundle mutated of
    Left (BoundaryTransferFailureOutcomeNotTerminal key "failure" _) ->
      assert (key == boundaryTransferKey uploadReceiveTransfer) "wrong receive failure transfer"
    other -> Left ("receive failure fabricated a live successor: " <> show other)

deterministicIdentity :: Either String ()
deterministicIdentity = do
  original <- bundle
  let reversed = Map.fromList
        (reverse (Map.toAscList (boundaryCommitStageTransfers original)))
      rebuilt = makeBoundaryCommitStageBundle
        (boundaryCommitStageBase original) reversed
  assert (boundaryCommitStageRevision rebuilt == boundaryCommitStageRevision original)
    "boundary commit revision changed with map ordering"
  mapLeft show (verifyBoundaryCommitStageBundle rebuilt)

replaceTransfer
  :: BoundaryTransferContract
  -> BoundaryCommitStageBundle
  -> BoundaryCommitStageBundle
replaceTransfer transfer original = makeBoundaryCommitStageBundle
  (boundaryCommitStageBase original)
  (Map.insert (boundaryTransferKey transfer) transfer
    (boundaryCommitStageTransfers original))

replaceProtocolTransition
  :: ProtocolTransitionBinding
  -> ProtocolStateStageBundle
  -> ProtocolStateStageBundle
replaceProtocolTransition transition base = makeProtocolStateStageBundle
  (protocolStateStageBase base)
  (protocolStateStageEndpoints base)
  (Map.insert (protocolTransitionKey transition) transition
    (protocolStateStageTransitions base))

bundle :: Either String BoundaryCommitStageBundle
bundle = uploadBoundaryCommitStageBundle

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
