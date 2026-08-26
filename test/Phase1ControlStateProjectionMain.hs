{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Callable (CaptureOccurrenceKey (..))
import Phil.Core.Syntax (Mode (..))
import Phil.Examples.Phase1.ControlStateWitnesses
import Phil.Systems.CallableLowering (CallableCaptureSemantic (..))
import Phil.Systems.ControlStateProjection
import Phil.Systems.IR
import Phil.Systems.SubjectCorrespondence
  ( SourceSubjectKey (..)
  , SystemsValueRef (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SYS-008 Steve ordinary join preserves exact candidate owner" steveJoinAccepts
    , test "SYS-008 loop initial entry and backedge use one projection checker" loopProjectionAccepts
    , test "SYS-008 resource-mismatched backedge missing slot rejects" loopMissingSlotRejected
    , test "SYS-008 equal-role owner cannot replace fixed loop subject" loopWrongSubjectRejected
    , test "SYS-008 live linear owner cannot disappear on backedge" loopLinearLeakRejected
    , test "SYS-008 scoped borrowed view cannot cross loop state" loopLoanEscapeRejected
    , test "SYS-008 restricted closure capture has exactly one carrier" closureCaptureAccepts
    , test "SYS-008 duplicated restricted closure capture rejects" closureCaptureDuplicationRejected
    , test "SYS-008 one carrier cannot stand for two restricted captures" closureCarrierSharingRejected
    , test "SYS-008 unrestricted closure capture may have multiple carriers" unrestrictedCaptureMultiplicityAccepted
    , test "SYS-008 control-state stage identity is deterministic" deterministicIdentity
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

steveJoinAccepts :: Either String ()
steveJoinAccepts = do
  bundle <- steveControlStateStageBundle
  mapLeft show (verifyControlStateStageBundle bundle)

loopProjectionAccepts :: Either String ()
loopProjectionAccepts = mapLeft show $
  checkStateBoundaryProjections loopProgram loopSubjectIndex loopBoundary
    [loopInitialProjection, loopBackedgeProjection]

loopMissingSlotRejected :: Either String ()
loopMissingSlotRejected =
  let bad = loopBackedgeProjection { stateProjectionBindings = Map.empty }
  in case checkStateBoundaryProjections loopProgram loopSubjectIndex loopBoundary
      [loopInitialProjection, bad] of
    Left (StateProjectionBindingDomainMismatch key expected actual) -> do
      assert (key == stateProjectionKey bad) "wrong missing-slot projection"
      assert (expected == Set.singleton loopOwnerSlot) "wrong expected loop slot set"
      assert (Set.null actual) "missing-slot mutation retained a slot"
    other -> Left ("missing loop slot was accepted: " <> show other)

loopWrongSubjectRejected :: Either String ()
loopWrongSubjectRejected =
  let bad = loopBackedgeProjection
        { stateProjectionIncomingRestricted = Map.singleton loopOtherOwnerRef Linear
        , stateProjectionBindings = Map.singleton loopOwnerSlot loopOtherOwnerRef
        }
  in case checkStateBoundaryProjections loopProgram loopSubjectIndex loopBoundary
      [loopInitialProjection, bad] of
    Left (StateProjectionFixedSubjectMismatch key slot subject ref) -> do
      assert (key == stateProjectionKey bad) "wrong subject-mismatch projection"
      assert (slot == loopOwnerSlot) "wrong subject-mismatch slot"
      assert (subject == loopSubject) "wrong fixed loop subject"
      assert (ref == loopOtherOwnerRef) "wrong substituted loop owner"
    other -> Left ("wrong fixed loop subject was accepted: " <> show other)

loopLinearLeakRejected :: Either String ()
loopLinearLeakRejected =
  let bad = loopBackedgeProjection
        { stateProjectionIncomingRestricted = Map.fromList
            [ (loopOwnerRef, Linear)
            , (loopOtherOwnerRef, Linear)
            ]
        }
  in case checkStateBoundaryProjections loopProgram loopSubjectIndex loopBoundary
      [loopInitialProjection, bad] of
    Left (StateProjectionUnaccountedLinearOwners key owners) -> do
      assert (key == stateProjectionKey bad) "wrong linear-leak projection"
      assert (owners == Set.singleton loopOtherOwnerRef) "wrong leaked owner set"
    other -> Left ("unaccounted linear owner was accepted: " <> show other)

loopLoanEscapeRejected :: Either String ()
loopLoanEscapeRejected =
  let bad = loopBackedgeProjection
        { stateProjectionIncomingRestricted = Map.singleton loopViewRef Linear
        , stateProjectionBindings = Map.singleton loopOwnerSlot loopViewRef
        }
  in case checkStateBoundaryProjections loopProgram loopSubjectIndex loopBoundary
      [loopInitialProjection, bad] of
    Left (StateProjectionScopedLoanEscape key ref) -> do
      assert (key == stateProjectionKey bad) "wrong loan-escape projection"
      assert (ref == loopViewRef) "wrong escaped loan"
    other -> Left ("scoped loop loan was accepted: " <> show other)

closureCaptureAccepts :: Either String ()
closureCaptureAccepts = mapLeft show (checkClosureCaptureProjection linearClosureProjection)

closureCaptureDuplicationRejected :: Either String ()
closureCaptureDuplicationRejected =
  let bad = linearClosureProjection
        { closureCaptureProjectionCarriers = Map.singleton captureA
            [CaptureCarrierKey "env.slot.0", CaptureCarrierKey "env.slot.1"] }
  in case checkClosureCaptureProjection bad of
    Left (ClosureRestrictedCaptureCardinality key capture count) -> do
      assert (key == "closure.linear") "wrong duplicate-capture closure"
      assert (capture == captureA) "wrong duplicated capture"
      assert (count == 2) "wrong duplicate carrier count"
    other -> Left ("duplicated restricted capture was accepted: " <> show other)

closureCarrierSharingRejected :: Either String ()
closureCarrierSharingRejected =
  let carrier = CaptureCarrierKey "env.shared"
      bad = ClosureCaptureProjection
        { closureCaptureProjectionKey = "closure.shared-carrier"
        , closureCaptureProjectionCaptures = Map.fromList
            [ (captureA, linearCapture "subject.a")
            , (captureB, linearCapture "subject.b")
            ]
        , closureCaptureProjectionCarriers = Map.fromList
            [ (captureA, [carrier])
            , (captureB, [carrier])
            ]
        }
  in case checkClosureCaptureProjection bad of
    Left (ClosureRestrictedCarrierShared key actualCarrier captures) -> do
      assert (key == "closure.shared-carrier") "wrong shared-carrier closure"
      assert (actualCarrier == carrier) "wrong shared carrier"
      assert (captures == Set.fromList [captureA, captureB]) "wrong shared capture set"
    other -> Left ("shared restricted capture carrier was accepted: " <> show other)

unrestrictedCaptureMultiplicityAccepted :: Either String ()
unrestrictedCaptureMultiplicityAccepted =
  let projection = ClosureCaptureProjection
        { closureCaptureProjectionKey = "closure.unrestricted"
        , closureCaptureProjectionCaptures = Map.singleton captureA
            (CallableCaptureSemantic Unrestricted Nothing Set.empty)
        , closureCaptureProjectionCarriers = Map.singleton captureA
            [CaptureCarrierKey "copy.0", CaptureCarrierKey "copy.1"]
        }
  in mapLeft show (checkClosureCaptureProjection projection)

deterministicIdentity :: Either String ()
deterministicIdentity = do
  bundle <- steveControlStateStageBundle
  let boundaries = Map.fromList
        (reverse (Map.toAscList (controlStateStageBoundaries bundle)))
      projections = Map.fromList
        (reverse (Map.toAscList (controlStateStageProjections bundle)))
      rebuilt = makeControlStateStageBundle
        (controlStateStageBase bundle) boundaries projections
        (controlStateStageClosureCaptures bundle)
  assert
    (controlStateStageRevision rebuilt == controlStateStageRevision bundle)
    "control-state stage revision changed with map order"
  mapLeft show (verifyControlStateStageBundle rebuilt)

loopSubject :: SourceSubjectKey
loopSubject = SourceSubjectKey "loop.subject.owner"

loopOwnerSlot :: StateSlotKey
loopOwnerSlot = StateSlotKey "loop-owner"

loopBoundary :: StateBoundaryContract
loopBoundary = StateBoundaryContract
  { stateBoundaryKey = StateBoundaryKey "loop.header.state.v1"
  , stateBoundaryKind = LoopStateBoundary
  , stateBoundaryFunction = "LoopWorker"
  , stateBoundaryTargetBlock = BlockId "loop.header"
  , stateBoundarySlots = Map.singleton loopOwnerSlot StateSlotContract
      { stateSlotKey = loopOwnerSlot
      , stateSlotMode = Linear
      , stateSlotSubjectRequirement = FixedStateSubject loopSubject
      }
  }

loopInitialProjection, loopBackedgeProjection :: StateProjection
loopInitialProjection = loopProjection
  "loop.initial" LoopInitialEntry (BlockId "loop.entry")
loopBackedgeProjection = loopProjection
  "loop.backedge" LoopBackedge (BlockId "loop.body")

loopProjection :: String -> StateProjectionKind -> BlockId -> StateProjection
loopProjection key kind fromBlock = StateProjection
  { stateProjectionKey = StateProjectionKey (text key)
  , stateProjectionKind = kind
  , stateProjectionBoundary = stateBoundaryKey loopBoundary
  , stateProjectionFromBlock = fromBlock
  , stateProjectionEdgeLabel = "jump"
  , stateProjectionIncomingRestricted = Map.singleton loopOwnerRef Linear
  , stateProjectionBindings = Map.singleton loopOwnerSlot loopOwnerRef
  }

loopOwnerRef, loopOtherOwnerRef, loopViewRef :: SystemsValueRef
loopOwnerRef = SystemsValueRef "LoopWorker" (ValueId "loop.owner")
loopOtherOwnerRef = SystemsValueRef "LoopWorker" (ValueId "loop.other-owner")
loopViewRef = SystemsValueRef "LoopWorker" (ValueId "loop.view")

loopSubjectIndex :: Map.Map SourceSubjectKey (Set.Set SystemsValueRef)
loopSubjectIndex = Map.singleton loopSubject (Set.singleton loopOwnerRef)

loopProgram :: SystemsProgram
loopProgram = SystemsProgram
  { systemsProgramName = "sys008-loop-fixture"
  , systemsProgramProfile = CheckedRuntime
  , systemsProgramFunctions = Map.singleton "LoopWorker" loopFunction
  }

loopFunction :: SystemsFunction
loopFunction = SystemsFunction
  { systemsFunctionName = "LoopWorker"
  , systemsFunctionEntry = BlockId "loop.entry"
  , systemsFunctionValues = Map.fromList
      [ valueEntry "loop.owner" (OwnedBuffer "LoopOwner")
      , valueEntry "loop.other-owner" (OwnedBuffer "LoopOwner")
      , valueEntry "loop.view" (BorrowedSlice (ValueId "loop.owner"))
      , valueEntry "loop.cond" (RuntimeInput "Bool")
      ]
  , systemsFunctionBlocks = Map.fromList
      [ blockEntry "loop.entry" (TermJump (BlockId "loop.header"))
      , blockEntry "loop.header"
          (TermBranch (ValueId "loop.cond") (BlockId "loop.body") (BlockId "loop.exit"))
      , blockEntry "loop.body" (TermJump (BlockId "loop.header"))
      , blockEntry "loop.exit" (TermEnd "done")
      ]
  }

valueEntry :: String -> SystemsValueRole -> (ValueId, SystemsValue)
valueEntry key role =
  let valueId = ValueId (text key)
  in (valueId, SystemsValue valueId role Nothing)

blockEntry :: String -> SystemsTerminator -> (BlockId, SystemsBlock)
blockEntry key terminator =
  let blockId = BlockId (text key)
  in (blockId, SystemsBlock blockId [] terminator)

captureA, captureB :: CaptureOccurrenceKey
captureA = CaptureOccurrenceKey "capture.a"
captureB = CaptureOccurrenceKey "capture.b"

linearClosureProjection :: ClosureCaptureProjection
linearClosureProjection = ClosureCaptureProjection
  { closureCaptureProjectionKey = "closure.linear"
  , closureCaptureProjectionCaptures = Map.singleton captureA
      (linearCapture "subject.a")
  , closureCaptureProjectionCarriers = Map.singleton captureA
      [CaptureCarrierKey "env.slot.0"]
  }

linearCapture :: String -> CallableCaptureSemantic
linearCapture subject = CallableCaptureSemantic
  { callableCaptureSemanticMode = Linear
  , callableCaptureSemanticSubject = Just (text subject)
  , callableCaptureSemanticAuthority = Set.empty
  }

text :: String -> Data.Text.Text
text = Data.Text.pack

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
