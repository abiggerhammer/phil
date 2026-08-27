{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Syntax (Mode (..))
import Phil.Systems.ControlStateProjection
import Phil.Systems.IR
import Phil.Systems.SubjectCorrespondence (SystemsValueRef (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "RES-007 scoped loan cannot cross ordinary join" joinLoanEscapeRejects
    , test "RES-007 scoped loan cannot cross loop backedge" backedgeLoanEscapeRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

joinLoanEscapeRejects :: Either String ()
joinLoanEscapeRejects =
  case checkStateBoundaryProjections program Map.empty joinBoundary
      [joinProjection "join.left" (BlockId "join.left") ownerRef,
       joinProjection "join.right" (BlockId "join.right") loanRef] of
    Left (StateProjectionScopedLoanEscape key ref) -> do
      assert (key == StateProjectionKey "join.right") "wrong join predecessor"
      assert (ref == loanRef) "wrong escaped join loan"
    other -> Left ("scoped loan crossed ordinary join: " <> show other)

backedgeLoanEscapeRejects :: Either String ()
backedgeLoanEscapeRejects =
  case checkStateBoundaryProjections program Map.empty loopBoundary
      [loopProjection "loop.initial" LoopInitialEntry (BlockId "loop.entry") ownerRef,
       loopProjection "loop.backedge" LoopBackedge (BlockId "loop.body") loanRef] of
    Left (StateProjectionScopedLoanEscape key ref) -> do
      assert (key == StateProjectionKey "loop.backedge") "wrong loop predecessor"
      assert (ref == loanRef) "wrong escaped backedge loan"
    other -> Left ("scoped loan crossed loop backedge: " <> show other)

slot :: StateSlotKey
slot = StateSlotKey "owner"

joinBoundary, loopBoundary :: StateBoundaryContract
joinBoundary = mkBoundary "res007.join" OrdinaryJoinBoundary (BlockId "join")
loopBoundary = mkBoundary "res007.loop" LoopStateBoundary (BlockId "loop.header")

mkBoundary :: Text -> StateBoundaryKind -> BlockId -> StateBoundaryContract
mkBoundary key kind target = StateBoundaryContract
  { stateBoundaryKey = StateBoundaryKey key
  , stateBoundaryKind = kind
  , stateBoundaryFunction = "Res007Worker"
  , stateBoundaryTargetBlock = target
  , stateBoundarySlots = Map.singleton slot StateSlotContract
      { stateSlotKey = slot
      , stateSlotMode = Linear
      , stateSlotSubjectRequirement = AnyStateSubject
      }
  }

joinProjection :: Text -> BlockId -> SystemsValueRef -> StateProjection
joinProjection key fromBlock ref = mkProjection key OrdinaryJoinPredecessor joinBoundary fromBlock ref

loopProjection :: Text -> StateProjectionKind -> BlockId -> SystemsValueRef -> StateProjection
loopProjection key kind fromBlock ref = mkProjection key kind loopBoundary fromBlock ref

mkProjection :: Text -> StateProjectionKind -> StateBoundaryContract -> BlockId -> SystemsValueRef -> StateProjection
mkProjection key kind boundary fromBlock ref = StateProjection
  { stateProjectionKey = StateProjectionKey key
  , stateProjectionKind = kind
  , stateProjectionBoundary = stateBoundaryKey boundary
  , stateProjectionFromBlock = fromBlock
  , stateProjectionEdgeLabel = "jump"
  , stateProjectionIncomingRestricted = Map.singleton ref Linear
  , stateProjectionBindings = Map.singleton slot ref
  }

ownerRef, loanRef :: SystemsValueRef
ownerRef = SystemsValueRef "Res007Worker" (ValueId "owner")
loanRef = SystemsValueRef "Res007Worker" (ValueId "loan")

program :: SystemsProgram
program = SystemsProgram
  { systemsProgramName = "res007-scoped-loans"
  , systemsProgramProfile = CheckedRuntime
  , systemsProgramFunctions = Map.singleton "Res007Worker" function
  }

function :: SystemsFunction
function = SystemsFunction
  { systemsFunctionName = "Res007Worker"
  , systemsFunctionEntry = BlockId "entry"
  , systemsFunctionValues = Map.fromList
      [ valueEntry "owner" (OwnedBuffer "Owner")
      , valueEntry "loan" (BorrowedSlice (ValueId "owner"))
      ]
  , systemsFunctionBlocks = Map.fromList
      [ blockEntry "entry" (TermJump (BlockId "join.left"))
      , blockEntry "join.left" (TermJump (BlockId "join"))
      , blockEntry "join.right" (TermJump (BlockId "join"))
      , blockEntry "join" (TermEnd "done")
      , blockEntry "loop.entry" (TermJump (BlockId "loop.header"))
      , blockEntry "loop.header" (TermJump (BlockId "loop.body"))
      , blockEntry "loop.body" (TermJump (BlockId "loop.header"))
      ]
  }

valueEntry :: Text -> SystemsValueRole -> (ValueId, SystemsValue)
valueEntry key role = let valueId = ValueId key in (valueId, SystemsValue valueId role Nothing)

blockEntry :: Text -> SystemsTerminator -> (BlockId, SystemsBlock)
blockEntry key terminator = let blockId = BlockId key in (blockId, SystemsBlock blockId [] terminator)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail
