{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (insertBinding)
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Systems.ControlStateInvariant
import Phil.Systems.ControlStateProjection
import Phil.Systems.IR
import Phil.Systems.SubjectCorrespondence (SystemsValueRef (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "RES-013 every join predecessor establishes exact invariant" joinInvariantAccepts
    , test "RES-013 structural join alone does not establish invariant" missingJoinEvidenceRejects
    , test "RES-013 path-local join evidence does not leak across predecessors" pathLocalJoinEvidenceRejects
    , test "RES-013 loop initial entry and backedge establish exact invariant" loopInvariantAccepts
    , test "RES-013 structurally valid loop backedge without invariant rejects" missingBackedgeEvidenceRejects
    , test "RES-013 trivial invariant needs no fabricated evidence" trivialInvariantAccepts
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

joinInvariantAccepts :: Either String ()
joinInvariantAccepts = do
  leftState <- proofState (Name "left-proof") leftInvariant
  rightState <- proofState (Name "right-proof") rightInvariant
  mapLeft show $ checkStateBoundaryInvariant
    emptyStaticContext
    program
    Map.empty
    joinBoundary
    joinProjections
    (invariantContract joinBoundary joinInvariant)
    (Map.fromList
      [ (stateProjectionKey joinLeftProjection,
          predecessor joinLeftProjection joinLeftCursorRef leftCursorTerm leftState)
      , (stateProjectionKey joinRightProjection,
          predecessor joinRightProjection joinRightCursorRef rightCursorTerm rightState)
      ])

missingJoinEvidenceRejects :: Either String ()
missingJoinEvidenceRejects = do
  leftState <- proofState (Name "left-proof") leftInvariant
  let rightKey = stateProjectionKey joinRightProjection
      witnesses = Map.fromList
        [ (stateProjectionKey joinLeftProjection,
            predecessor joinLeftProjection joinLeftCursorRef leftCursorTerm leftState)
        , (rightKey,
            predecessor joinRightProjection joinRightCursorRef rightCursorTerm emptyCheckState)
        ]
  case checkStateBoundaryInvariant
      emptyStaticContext program Map.empty joinBoundary joinProjections
      (invariantContract joinBoundary joinInvariant) witnesses of
    Left (StateInvariantDecisionUnavailable key proposition) -> do
      assert (key == rightKey) "missing-evidence diagnostic named wrong join predecessor"
      assert (proposition == rightInvariant) "missing-evidence diagnostic changed instantiated invariant"
    other -> Left ("structural join established a logical invariant without evidence: " <> show other)

pathLocalJoinEvidenceRejects :: Either String ()
pathLocalJoinEvidenceRejects = do
  leftState <- proofState (Name "left-proof") leftInvariant
  wrongRightState <- proofState (Name "left-proof-reused") leftInvariant
  let rightKey = stateProjectionKey joinRightProjection
      witnesses = Map.fromList
        [ (stateProjectionKey joinLeftProjection,
            predecessor joinLeftProjection joinLeftCursorRef leftCursorTerm leftState)
        , (rightKey,
            predecessor joinRightProjection joinRightCursorRef rightCursorTerm wrongRightState)
        ]
  case checkStateBoundaryInvariant
      emptyStaticContext program Map.empty joinBoundary joinProjections
      (invariantContract joinBoundary joinInvariant) witnesses of
    Left (StateInvariantDecisionUnavailable key proposition) -> do
      assert (key == rightKey) "path-local diagnostic named wrong join predecessor"
      assert (proposition == rightInvariant) "path-local diagnostic changed right invariant"
    other -> Left ("evidence from one predecessor became unconditional after join: " <> show other)

loopInvariantAccepts :: Either String ()
loopInvariantAccepts = do
  initialState <- proofState (Name "initial-proof") initialInvariant
  backedgeState <- proofState (Name "backedge-proof") backedgeInvariant
  mapLeft show $ checkStateBoundaryInvariant
    emptyStaticContext
    program
    Map.empty
    loopBoundary
    loopProjections
    (invariantContract loopBoundary loopInvariant)
    (Map.fromList
      [ (stateProjectionKey loopInitialProjection,
          predecessor loopInitialProjection loopInitialCursorRef initialCursorTerm initialState)
      , (stateProjectionKey loopBackedgeProjection,
          predecessor loopBackedgeProjection loopBackedgeCursorRef backedgeCursorTerm backedgeState)
      ])

missingBackedgeEvidenceRejects :: Either String ()
missingBackedgeEvidenceRejects = do
  initialState <- proofState (Name "initial-proof") initialInvariant
  let backedgeKey = stateProjectionKey loopBackedgeProjection
      witnesses = Map.fromList
        [ (stateProjectionKey loopInitialProjection,
            predecessor loopInitialProjection loopInitialCursorRef initialCursorTerm initialState)
        , (backedgeKey,
            predecessor loopBackedgeProjection loopBackedgeCursorRef backedgeCursorTerm emptyCheckState)
        ]
  case checkStateBoundaryInvariant
      emptyStaticContext program Map.empty loopBoundary loopProjections
      (invariantContract loopBoundary loopInvariant) witnesses of
    Left (StateInvariantDecisionUnavailable key proposition) -> do
      assert (key == backedgeKey) "missing-backedge diagnostic named wrong predecessor"
      assert (proposition == backedgeInvariant) "missing-backedge diagnostic changed invariant"
    other -> Left ("structurally valid loop backedge bypassed invariant establishment: " <> show other)

trivialInvariantAccepts :: Either String ()
trivialInvariantAccepts = mapLeft show $ checkStateBoundaryInvariant
  emptyStaticContext
  program
  Map.empty
  joinBoundary
  joinProjections
  (invariantContract joinBoundary Truth)
  (Map.fromList
    [ (stateProjectionKey joinLeftProjection,
        predecessor joinLeftProjection joinLeftCursorRef leftCursorTerm emptyCheckState)
    , (stateProjectionKey joinRightProjection,
        predecessor joinRightProjection joinRightCursorRef rightCursorTerm emptyCheckState)
    ])

invariantContract :: StateBoundaryContract -> Proposition -> StateInvariantContract
invariantContract boundaryContract proposition = StateInvariantContract
  { stateInvariantBoundary = stateBoundaryKey boundaryContract
  , stateInvariantBinders = Map.fromList
      [ (cursorSlot, cursorName)
      , (limitSlot, limitName)
      ]
  , stateInvariantProposition = proposition
  }

predecessor
  :: StateProjection
  -> SystemsValueRef
  -> RefTerm
  -> CheckState
  -> StateInvariantPredecessor
predecessor stateProjection cursorRef cursorTerm state = StateInvariantPredecessor
  { stateInvariantPredecessorProjection = stateProjectionKey stateProjection
  , stateInvariantPredecessorSlots = Map.fromList
      [ (cursorSlot, StateInvariantSlotWitness cursorRef cursorTerm)
      , (limitSlot, StateInvariantSlotWitness limitRef limitTerm)
      ]
  , stateInvariantPredecessorState = state
  }

proofState :: Name -> Proposition -> Either String CheckState
proofState proofName proposition = do
  context <- mapLeft show $ insertBinding
    Unrestricted proofName (TyProof proposition) (resourceContext emptyCheckState)
  Right emptyCheckState { resourceContext = context }

cursorName, limitName :: Name
cursorName = Name "cursor"
limitName = Name "limit"

cursorSlot, limitSlot :: StateSlotKey
cursorSlot = StateSlotKey "cursor"
limitSlot = StateSlotKey "limit"

joinInvariant, loopInvariant :: Proposition
joinInvariant = LessEqual (RefVar cursorName) (RefVar limitName)
loopInvariant = joinInvariant

leftInvariant, rightInvariant, initialInvariant, backedgeInvariant :: Proposition
leftInvariant = LessEqual leftCursorTerm limitTerm
rightInvariant = LessEqual rightCursorTerm limitTerm
initialInvariant = LessEqual initialCursorTerm limitTerm
backedgeInvariant = LessEqual backedgeCursorTerm limitTerm

leftCursorTerm, rightCursorTerm, initialCursorTerm, backedgeCursorTerm, limitTerm :: RefTerm
leftCursorTerm = RefOpaque SortNat "join.left.cursor"
rightCursorTerm = RefOpaque SortNat "join.right.cursor"
initialCursorTerm = RefOpaque SortNat "loop.initial.cursor"
backedgeCursorTerm = RefOpaque SortNat "loop.backedge.cursor"
limitTerm = RefOpaque SortNat "state.limit"

joinBoundary, loopBoundary :: StateBoundaryContract
joinBoundary = boundary (StateBoundaryKey "res013.join") OrdinaryJoinBoundary (BlockId "join")
loopBoundary = boundary (StateBoundaryKey "res013.loop") LoopStateBoundary (BlockId "loop.header")

boundary :: StateBoundaryKey -> StateBoundaryKind -> BlockId -> StateBoundaryContract
boundary key kind target = StateBoundaryContract
  { stateBoundaryKey = key
  , stateBoundaryKind = kind
  , stateBoundaryFunction = "InvariantWorker"
  , stateBoundaryTargetBlock = target
  , stateBoundarySlots = Map.fromList
      [ (cursorSlot, StateSlotContract cursorSlot Unrestricted AnyStateSubject)
      , (limitSlot, StateSlotContract limitSlot Unrestricted AnyStateSubject)
      ]
  }

joinProjections, loopProjections :: [StateProjection]
joinProjections = [joinLeftProjection, joinRightProjection]
loopProjections = [loopInitialProjection, loopBackedgeProjection]

joinLeftProjection, joinRightProjection, loopInitialProjection, loopBackedgeProjection :: StateProjection
joinLeftProjection = projection
  (StateProjectionKey "join.left") OrdinaryJoinPredecessor joinBoundary
  (BlockId "join.left") joinLeftCursorRef
joinRightProjection = projection
  (StateProjectionKey "join.right") OrdinaryJoinPredecessor joinBoundary
  (BlockId "join.right") joinRightCursorRef
loopInitialProjection = projection
  (StateProjectionKey "loop.initial") LoopInitialEntry loopBoundary
  (BlockId "loop.entry") loopInitialCursorRef
loopBackedgeProjection = projection
  (StateProjectionKey "loop.backedge") LoopBackedge loopBoundary
  (BlockId "loop.body") loopBackedgeCursorRef

projection
  :: StateProjectionKey
  -> StateProjectionKind
  -> StateBoundaryContract
  -> BlockId
  -> SystemsValueRef
  -> StateProjection
projection key kind stateBoundary fromBlock cursorRef = StateProjection
  { stateProjectionKey = key
  , stateProjectionKind = kind
  , stateProjectionBoundary = stateBoundaryKey stateBoundary
  , stateProjectionFromBlock = fromBlock
  , stateProjectionEdgeLabel = "jump"
  , stateProjectionIncomingRestricted = Map.empty
  , stateProjectionBindings = Map.fromList
      [ (cursorSlot, cursorRef)
      , (limitSlot, limitRef)
      ]
  }

joinLeftCursorRef, joinRightCursorRef, loopInitialCursorRef, loopBackedgeCursorRef, limitRef :: SystemsValueRef
joinLeftCursorRef = ref "join.left.cursor"
joinRightCursorRef = ref "join.right.cursor"
loopInitialCursorRef = ref "loop.initial.cursor"
loopBackedgeCursorRef = ref "loop.backedge.cursor"
limitRef = ref "state.limit"

ref :: Text -> SystemsValueRef
ref name = SystemsValueRef "InvariantWorker" (ValueId name)

program :: SystemsProgram
program = SystemsProgram
  { systemsProgramName = "res013-join-loop-invariant"
  , systemsProgramProfile = CheckedRuntime
  , systemsProgramFunctions = Map.singleton "InvariantWorker" function
  }

function :: SystemsFunction
function = SystemsFunction
  { systemsFunctionName = "InvariantWorker"
  , systemsFunctionEntry = BlockId "join.left"
  , systemsFunctionValues = Map.fromList
      [ valueEntry "join.left.cursor" (RuntimeInput "Nat")
      , valueEntry "join.right.cursor" (RuntimeInput "Nat")
      , valueEntry "loop.initial.cursor" (RuntimeInput "Nat")
      , valueEntry "loop.backedge.cursor" (RuntimeInput "Nat")
      , valueEntry "state.limit" (RuntimeInput "Nat")
      , valueEntry "loop.cond" (RuntimeInput "Bool")
      ]
  , systemsFunctionBlocks = Map.fromList
      [ blockEntry "join.left" (TermJump (BlockId "join"))
      , blockEntry "join.right" (TermJump (BlockId "join"))
      , blockEntry "join" (TermEnd "join-done")
      , blockEntry "loop.entry" (TermJump (BlockId "loop.header"))
      , blockEntry "loop.header"
          (TermBranch (ValueId "loop.cond") (BlockId "loop.body") (BlockId "loop.exit"))
      , blockEntry "loop.body" (TermJump (BlockId "loop.header"))
      , blockEntry "loop.exit" (TermEnd "loop-done")
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
