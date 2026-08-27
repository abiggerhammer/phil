{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Syntax (Mode (..))
import Phil.Systems.ControlStateProjection
import Phil.Systems.IR
import Phil.Systems.SubjectCorrespondence (SourceSubjectKey, SystemsValueRef (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "RES-006 hidden affine maybe-possession rejects" hiddenMaybePossessionRejects
    , test "RES-006 explicit option carrier joins" explicitOptionCarrierAccepts
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

hiddenMaybePossessionRejects :: Either String ()
hiddenMaybePossessionRejects =
  let right = affineProjection "affine.right" (BlockId "right")
        { stateProjectionBindings = Map.empty
        , stateProjectionIncomingRestricted = Map.empty
        }
  in case checkStateBoundaryProjections program Map.empty affineBoundary
      [affineProjection "affine.left" (BlockId "left"), right] of
    Left (StateProjectionBindingDomainMismatch key expected actual) -> do
      assert (key == stateProjectionKey right) "wrong asymmetric predecessor"
      assert (expected == Set.singleton affineSlot) "wrong expected affine slot set"
      assert (Set.null actual) "hidden maybe-possession unexpectedly retained a slot"
    other -> Left ("hidden affine maybe-possession was accepted: " <> show other)

explicitOptionCarrierAccepts :: Either String ()
explicitOptionCarrierAccepts = mapLeft show $
  checkStateBoundaryProjections program Map.empty optionBoundary
    [ optionProjection "option.left" (BlockId "option.left") leftOptionRef
    , optionProjection "option.right" (BlockId "option.right") rightOptionRef
    ]

affineSlot, optionSlot :: StateSlotKey
affineSlot = StateSlotKey "affine-owner"
optionSlot = StateSlotKey "explicit-option"

affineBoundary, optionBoundary :: StateBoundaryContract
affineBoundary = boundary "res006.affine.join" (BlockId "join") affineSlot Affine
optionBoundary = boundary "res006.option.join" (BlockId "option.join") optionSlot Unrestricted

boundary :: Text -> BlockId -> StateSlotKey -> Mode -> StateBoundaryContract
boundary key target slot mode = StateBoundaryContract
  { stateBoundaryKey = StateBoundaryKey key
  , stateBoundaryKind = OrdinaryJoinBoundary
  , stateBoundaryFunction = "Res006Worker"
  , stateBoundaryTargetBlock = target
  , stateBoundarySlots = Map.singleton slot StateSlotContract
      { stateSlotKey = slot
      , stateSlotMode = mode
      , stateSlotSubjectRequirement = AnyStateSubject
      }
  }

affineProjection :: Text -> BlockId -> StateProjection
affineProjection key fromBlock = StateProjection
  { stateProjectionKey = StateProjectionKey key
  , stateProjectionKind = OrdinaryJoinPredecessor
  , stateProjectionBoundary = stateBoundaryKey affineBoundary
  , stateProjectionFromBlock = fromBlock
  , stateProjectionEdgeLabel = "jump"
  , stateProjectionIncomingRestricted = Map.singleton affineOwnerRef Affine
  , stateProjectionBindings = Map.singleton affineSlot affineOwnerRef
  }

optionProjection :: Text -> BlockId -> SystemsValueRef -> StateProjection
optionProjection key fromBlock ref = StateProjection
  { stateProjectionKey = StateProjectionKey key
  , stateProjectionKind = OrdinaryJoinPredecessor
  , stateProjectionBoundary = stateBoundaryKey optionBoundary
  , stateProjectionFromBlock = fromBlock
  , stateProjectionEdgeLabel = "jump"
  , stateProjectionIncomingRestricted = Map.empty
  , stateProjectionBindings = Map.singleton optionSlot ref
  }

affineOwnerRef, leftOptionRef, rightOptionRef :: SystemsValueRef
affineOwnerRef = SystemsValueRef "Res006Worker" (ValueId "affine.owner")
leftOptionRef = SystemsValueRef "Res006Worker" (ValueId "option.some")
rightOptionRef = SystemsValueRef "Res006Worker" (ValueId "option.none")

program :: SystemsProgram
program = SystemsProgram
  { systemsProgramName = "res006-affine-asymmetry"
  , systemsProgramProfile = CheckedRuntime
  , systemsProgramFunctions = Map.singleton "Res006Worker" function
  }

function :: SystemsFunction
function = SystemsFunction
  { systemsFunctionName = "Res006Worker"
  , systemsFunctionEntry = BlockId "entry"
  , systemsFunctionValues = Map.fromList
      [ valueEntry "affine.owner" (OwnedBuffer "AffineOwner")
      , valueEntry "option.some" (RuntimeInput "OptionOwner")
      , valueEntry "option.none" (RuntimeInput "OptionOwner")
      , valueEntry "condition" (RuntimeInput "Bool")
      ]
  , systemsFunctionBlocks = Map.fromList
      [ blockEntry "entry" (TermBranch (ValueId "condition") (BlockId "left") (BlockId "right"))
      , blockEntry "left" (TermJump (BlockId "join"))
      , blockEntry "right" (TermJump (BlockId "join"))
      , blockEntry "join" (TermEnd "done")
      , blockEntry "option.left" (TermJump (BlockId "option.join"))
      , blockEntry "option.right" (TermJump (BlockId "option.join"))
      , blockEntry "option.join" (TermEnd "done")
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
