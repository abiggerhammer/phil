{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Syntax (Mode (..))
import Phil.Systems.ControlStateProjection
import Phil.Systems.IR
import Phil.Systems.SubjectCorrespondence (SystemsValueRef (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "RES-008 terminal arm contributes no join predecessor" terminalArmExcludedAccepts
    , test "RES-008 terminal arm cannot be forced into join projection" terminalArmProjectionRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

terminalArmExcludedAccepts :: Either String ()
terminalArmExcludedAccepts = mapLeft show $
  checkStateBoundaryProjections program Map.empty joinBoundary
    [ continuingProjection "join.left" (BlockId "left")
    , continuingProjection "join.right" (BlockId "right")
    ]

terminalArmProjectionRejects :: Either String ()
terminalArmProjectionRejects =
  let terminalProjection = StateProjection
        { stateProjectionKey = StateProjectionKey "join.terminal"
        , stateProjectionKind = OrdinaryJoinPredecessor
        , stateProjectionBoundary = stateBoundaryKey joinBoundary
        , stateProjectionFromBlock = BlockId "terminal"
        , stateProjectionEdgeLabel = "jump"
        , stateProjectionIncomingRestricted = Map.singleton ownerRef Linear
        , stateProjectionBindings = Map.singleton ownerSlot ownerRef
        }
  in case checkStateBoundaryProjections program Map.empty joinBoundary
      [ continuingProjection "join.left" (BlockId "left")
      , continuingProjection "join.right" (BlockId "right")
      , terminalProjection
      ] of
    Left (StateProjectionEdgeLabelUnknown key label) -> do
      assert (key == stateProjectionKey terminalProjection) "wrong terminal projection"
      assert (label == "jump") "wrong terminal-edge label"
    other -> Left ("terminal arm was treated as a continuing join predecessor: " <> show other)

ownerSlot :: StateSlotKey
ownerSlot = StateSlotKey "owner"

joinBoundary :: StateBoundaryContract
joinBoundary = StateBoundaryContract
  { stateBoundaryKey = StateBoundaryKey "res008.join"
  , stateBoundaryKind = OrdinaryJoinBoundary
  , stateBoundaryFunction = "Res008Worker"
  , stateBoundaryTargetBlock = BlockId "join"
  , stateBoundarySlots = Map.singleton ownerSlot StateSlotContract
      { stateSlotKey = ownerSlot
      , stateSlotMode = Linear
      , stateSlotSubjectRequirement = AnyStateSubject
      }
  }

continuingProjection :: Text -> BlockId -> StateProjection
continuingProjection key fromBlock = StateProjection
  { stateProjectionKey = StateProjectionKey key
  , stateProjectionKind = OrdinaryJoinPredecessor
  , stateProjectionBoundary = stateBoundaryKey joinBoundary
  , stateProjectionFromBlock = fromBlock
  , stateProjectionEdgeLabel = "jump"
  , stateProjectionIncomingRestricted = Map.singleton ownerRef Linear
  , stateProjectionBindings = Map.singleton ownerSlot ownerRef
  }

ownerRef :: SystemsValueRef
ownerRef = SystemsValueRef "Res008Worker" (ValueId "owner")

program :: SystemsProgram
program = SystemsProgram
  { systemsProgramName = "res008-terminal-arm-exclusion"
  , systemsProgramProfile = CheckedRuntime
  , systemsProgramFunctions = Map.singleton "Res008Worker" function
  }

function :: SystemsFunction
function = SystemsFunction
  { systemsFunctionName = "Res008Worker"
  , systemsFunctionEntry = BlockId "entry"
  , systemsFunctionValues = Map.fromList
      [ valueEntry "owner" (OwnedBuffer "Owner")
      , valueEntry "condition" (RuntimeInput "Bool")
      ]
  , systemsFunctionBlocks = Map.fromList
      [ blockEntry "entry"
          (TermBranch (ValueId "condition") (BlockId "left") (BlockId "terminal"))
      , blockEntry "left" (TermJump (BlockId "join"))
      , blockEntry "right" (TermJump (BlockId "join"))
      , blockEntry "terminal" (TermEnd "done")
      , blockEntry "join" (TermEnd "joined")
      ]
  }

valueEntry :: Text -> SystemsValueRole -> (ValueId, SystemsValue)
valueEntry key role =
  let valueId = ValueId key
  in (valueId, SystemsValue valueId role Nothing)

blockEntry :: Text -> SystemsTerminator -> (BlockId, SystemsBlock)
blockEntry key terminator =
  let blockId = BlockId key
  in (blockId, SystemsBlock blockId [] terminator)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
