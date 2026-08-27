{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Syntax (Mode (..))
import Phil.Systems.ControlStateProjection
import Phil.Systems.IR
import Phil.Systems.SubjectCorrespondence (SourceSubjectKey (..), SystemsValueRef (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "RES-009 loop initial entry and backedge reuse state projection" exactReentryAccepts
    , test "RES-009 loop backedge state mismatch rejects" mismatchedBackedgeRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactReentryAccepts :: Either String ()
exactReentryAccepts = mapLeft show $
  checkStateBoundaryProjections program subjectIndex boundary
    [initialProjection, backedgeProjection]

mismatchedBackedgeRejects :: Either String ()
mismatchedBackedgeRejects =
  let bad = backedgeProjection
        { stateProjectionIncomingRestricted = Map.singleton otherOwnerRef Linear
        , stateProjectionBindings = Map.singleton ownerSlot otherOwnerRef
        }
  in case checkStateBoundaryProjections program subjectIndex boundary [initialProjection, bad] of
    Left (StateProjectionFixedSubjectMismatch key slot subject ref) -> do
      assert (key == stateProjectionKey bad) "wrong backedge projection"
      assert (slot == ownerSlot) "wrong loop state slot"
      assert (subject == ownerSubject) "wrong fixed subject"
      assert (ref == otherOwnerRef) "wrong mismatched owner"
    other -> Left ("mismatched loop backedge was accepted: " <> show other)

ownerSubject :: SourceSubjectKey
ownerSubject = SourceSubjectKey "loop.subject.owner"

ownerSlot :: StateSlotKey
ownerSlot = StateSlotKey "loop-owner"

boundary :: StateBoundaryContract
boundary = StateBoundaryContract
  { stateBoundaryKey = StateBoundaryKey "res009.loop.state"
  , stateBoundaryKind = LoopStateBoundary
  , stateBoundaryFunction = "Res009Worker"
  , stateBoundaryTargetBlock = BlockId "loop.header"
  , stateBoundarySlots = Map.singleton ownerSlot StateSlotContract
      { stateSlotKey = ownerSlot
      , stateSlotMode = Linear
      , stateSlotSubjectRequirement = FixedStateSubject ownerSubject
      }
  }

initialProjection, backedgeProjection :: StateProjection
initialProjection = projection (StateProjectionKey "loop.initial") LoopInitialEntry (BlockId "loop.entry") ownerRef
backedgeProjection = projection (StateProjectionKey "loop.backedge") LoopBackedge (BlockId "loop.body") ownerRef

projection :: StateProjectionKey -> StateProjectionKind -> BlockId -> SystemsValueRef -> StateProjection
projection key kind fromBlock ref = StateProjection
  { stateProjectionKey = key
  , stateProjectionKind = kind
  , stateProjectionBoundary = stateBoundaryKey boundary
  , stateProjectionFromBlock = fromBlock
  , stateProjectionEdgeLabel = "jump"
  , stateProjectionIncomingRestricted = Map.singleton ref Linear
  , stateProjectionBindings = Map.singleton ownerSlot ref
  }

ownerRef, otherOwnerRef :: SystemsValueRef
ownerRef = SystemsValueRef "Res009Worker" (ValueId "loop.owner")
otherOwnerRef = SystemsValueRef "Res009Worker" (ValueId "loop.other-owner")

subjectIndex :: Map.Map SourceSubjectKey (Set.Set SystemsValueRef)
subjectIndex = Map.singleton ownerSubject (Set.singleton ownerRef)

program :: SystemsProgram
program = SystemsProgram
  { systemsProgramName = "res009-loop-state-projection"
  , systemsProgramProfile = CheckedRuntime
  , systemsProgramFunctions = Map.singleton "Res009Worker" function
  }

function :: SystemsFunction
function = SystemsFunction
  { systemsFunctionName = "Res009Worker"
  , systemsFunctionEntry = BlockId "loop.entry"
  , systemsFunctionValues = Map.fromList
      [ valueEntry "loop.owner" (OwnedBuffer "LoopOwner")
      , valueEntry "loop.other-owner" (OwnedBuffer "LoopOwner")
      , valueEntry "loop.cond" (RuntimeInput "Bool")
      ]
  , systemsFunctionBlocks = Map.fromList
      [ blockEntry "loop.entry" (TermJump (BlockId "loop.header"))
      , blockEntry "loop.header" (TermBranch (ValueId "loop.cond") (BlockId "loop.body") (BlockId "loop.exit"))
      , blockEntry "loop.body" (TermJump (BlockId "loop.header"))
      , blockEntry "loop.exit" (TermEnd "done")
      ]
  }

valueEntry :: Text -> SystemsValueRole -> (ValueId, SystemsValue)
valueEntry key role = let valueId = ValueId key in (valueId, SystemsValue valueId role Nothing)

blockEntry :: Text -> SystemsTerminator -> (BlockId, SystemsBlock)
blockEntry key terminator = let blockId = BlockId key in (blockId, SystemsBlock blockId [] terminator)

assert :: Bool -> String -> Either String ()
assert condition detail | condition = Right () | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
