{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Syntax (Mode (..))
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
    [ test "RES-005 branch-local linear owner absent after prior disposition may join" disposedBeforeJoinAccepts
    , test "RES-005 live branch-local linear owner cannot disappear at join" liveBranchLocalLeakRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

disposedBeforeJoinAccepts :: Either String ()
disposedBeforeJoinAccepts = mapLeft show $
  checkStateBoundaryProjections program subjectIndex boundary
    [leftProjection, rightProjection]

liveBranchLocalLeakRejects :: Either String ()
liveBranchLocalLeakRejects =
  let badRight = rightProjection
        { stateProjectionIncomingRestricted = Map.fromList
            [ (continuingOwnerRef, Linear)
            , (branchLocalOwnerRef, Linear)
            ]
        }
  in case checkStateBoundaryProjections program subjectIndex boundary
      [leftProjection, badRight] of
    Left (StateProjectionUnaccountedLinearOwners key owners) -> do
      assert (key == stateProjectionKey badRight)
        "branch-local leak rejection named the wrong predecessor"
      assert (owners == Set.singleton branchLocalOwnerRef)
        "branch-local leak rejection named the wrong live owner set"
    other -> Left
      ("live branch-local linear owner reached reconvergence without disposition: "
        <> show other)

subject :: SourceSubjectKey
subject = SourceSubjectKey "res005.subject.owner"

ownerSlot :: StateSlotKey
ownerSlot = StateSlotKey "owner"

boundary :: StateBoundaryContract
boundary = StateBoundaryContract
  { stateBoundaryKey = StateBoundaryKey "res005.join"
  , stateBoundaryKind = OrdinaryJoinBoundary
  , stateBoundaryFunction = "Res005Worker"
  , stateBoundaryTargetBlock = BlockId "join"
  , stateBoundarySlots = Map.singleton ownerSlot StateSlotContract
      { stateSlotKey = ownerSlot
      , stateSlotMode = Linear
      , stateSlotSubjectRequirement = FixedStateSubject subject
      }
  }

leftProjection, rightProjection :: StateProjection
leftProjection = projection "res005.left" (BlockId "left")
rightProjection = projection "res005.right" (BlockId "right")

projection :: Text -> BlockId -> StateProjection
projection key fromBlock = StateProjection
  { stateProjectionKey = StateProjectionKey key
  , stateProjectionKind = OrdinaryJoinPredecessor
  , stateProjectionBoundary = stateBoundaryKey boundary
  , stateProjectionFromBlock = fromBlock
  , stateProjectionEdgeLabel = "jump"
  , stateProjectionIncomingRestricted = Map.singleton continuingOwnerRef Linear
  , stateProjectionBindings = Map.singleton ownerSlot continuingOwnerRef
  }

continuingOwnerRef, branchLocalOwnerRef :: SystemsValueRef
continuingOwnerRef = SystemsValueRef "Res005Worker" (ValueId "owner")
branchLocalOwnerRef = SystemsValueRef "Res005Worker" (ValueId "branch.local")

subjectIndex :: Map.Map SourceSubjectKey (Set.Set SystemsValueRef)
subjectIndex = Map.singleton subject (Set.singleton continuingOwnerRef)

program :: SystemsProgram
program = SystemsProgram
  { systemsProgramName = "res005-branch-local-linear-leak"
  , systemsProgramProfile = CheckedRuntime
  , systemsProgramFunctions = Map.singleton "Res005Worker" function
  }

function :: SystemsFunction
function = SystemsFunction
  { systemsFunctionName = "Res005Worker"
  , systemsFunctionEntry = BlockId "entry"
  , systemsFunctionValues = Map.fromList
      [ valueEntry "owner" (OwnedBuffer "Owner")
      , valueEntry "branch.local" (OwnedBuffer "BranchLocal")
      , valueEntry "condition" (RuntimeInput "Bool")
      ]
  , systemsFunctionBlocks = Map.fromList
      [ blockEntry "entry"
          (TermBranch (ValueId "condition") (BlockId "left") (BlockId "right"))
      , blockEntry "left" (TermJump (BlockId "join"))
      , blockEntry "right" (TermJump (BlockId "join"))
      , blockEntry "join" (TermEnd "done")
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
