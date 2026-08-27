{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (ResourceContext (..), insertBinding)
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Ty (..)
  , Value (..)
  )
import Phil.Core.Value (ValueResult (..), synthValue)
import Phil.Systems.ControlStateProjection
import Phil.Systems.IR
import Phil.Systems.SubjectCorrespondence (SourceSubjectKey (..), SystemsValueRef (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "RES-010 implicit state rewrite rejects" implicitRewriteRejects
    , test "RES-010 explicit proof transport admits state projection" explicitTransportAccepts
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

implicitRewriteRejects :: Either String ()
implicitRewriteRejects =
  let badLeft = projection (StateProjectionKey "join.left") (BlockId "left") sourceRef
  in case checkStateBoundaryProjections systemsProgram subjectIndex boundary
      [badLeft, projection (StateProjectionKey "join.right") (BlockId "right") transportedRef] of
    Left (StateProjectionFixedSubjectMismatch key slot subject ref) -> do
      assert (key == stateProjectionKey badLeft) "wrong implicit-rewrite projection"
      assert (slot == ownerSlot) "wrong implicit-rewrite slot"
      assert (subject == targetSubject) "wrong implicit-rewrite subject"
      assert (ref == sourceRef) "wrong implicit-rewrite owner"
    other -> Left ("implicit propositional rewrite was accepted: " <> show other)

explicitTransportAccepts :: Either String ()
explicitTransportAccepts = do
  transported <- checkedCoreTransport
  assert (valueResultType transported == targetTy) "core transport produced the wrong target type"
  assert (valueResultMode transported == Just Linear) "core transport lost linear ownership mode"
  let residual = resourceContext (valueResultState transported)
  assert (Map.notMember payloadName (linearBindings residual)) "core transport duplicated the source owner"
  assert (Map.member equalityName (unrestrictedBindings residual)) "core transport consumed reusable equality evidence"
  mapLeft show $
    checkStateBoundaryProjections systemsProgram subjectIndex boundary
      [ projection (StateProjectionKey "join.left") (BlockId "left") transportedRef
      , projection (StateProjectionKey "join.right") (BlockId "right") transportedRef
      ]

checkedCoreTransport :: Either String ValueResult
checkedCoreTransport = do
  context0 <- mapLeft show $ insertBinding Linear payloadName sourceTy (resourceContext emptyCheckState)
  context1 <- mapLeft show $ insertBinding Unrestricted equalityName equalityTy context0
  let state = emptyCheckState { resourceContext = context1 }
  mapLeft show $ synthValue (VTransport (VVar payloadName) equalityName targetTy) state

payloadName, equalityName :: Name
payloadName = Name "payload"
equalityName = Name "lengthEq"

sourceIndex, targetIndex :: RefTerm
sourceIndex = RefNat 4096
targetIndex = RefOpaque SortNat "payload.length"

sourceTy, targetTy, equalityTy :: Ty
sourceTy = TyBytes sourceIndex
targetTy = TyBytes targetIndex
equalityTy = TyProof (Equal sourceIndex targetIndex)

targetSubject :: SourceSubjectKey
targetSubject = SourceSubjectKey "payload.after-transport"

ownerSlot :: StateSlotKey
ownerSlot = StateSlotKey "payload-owner"

boundary :: StateBoundaryContract
boundary = StateBoundaryContract
  { stateBoundaryKey = StateBoundaryKey "res010.join.state"
  , stateBoundaryKind = OrdinaryJoinBoundary
  , stateBoundaryFunction = "Res010Worker"
  , stateBoundaryTargetBlock = BlockId "join"
  , stateBoundarySlots = Map.singleton ownerSlot StateSlotContract
      { stateSlotKey = ownerSlot
      , stateSlotMode = Linear
      , stateSlotSubjectRequirement = FixedStateSubject targetSubject
      }
  }

projection :: StateProjectionKey -> BlockId -> SystemsValueRef -> StateProjection
projection key fromBlock ref = StateProjection
  { stateProjectionKey = key
  , stateProjectionKind = OrdinaryJoinPredecessor
  , stateProjectionBoundary = stateBoundaryKey boundary
  , stateProjectionFromBlock = fromBlock
  , stateProjectionEdgeLabel = "jump"
  , stateProjectionIncomingRestricted = Map.singleton ref Linear
  , stateProjectionBindings = Map.singleton ownerSlot ref
  }

sourceRef, transportedRef :: SystemsValueRef
sourceRef = SystemsValueRef "Res010Worker" (ValueId "payload.source")
transportedRef = SystemsValueRef "Res010Worker" (ValueId "payload.transported")

subjectIndex :: Map.Map SourceSubjectKey (Set.Set SystemsValueRef)
subjectIndex = Map.singleton targetSubject (Set.singleton transportedRef)

systemsProgram :: SystemsProgram
systemsProgram = SystemsProgram
  { systemsProgramName = "res010-propositional-state-transport"
  , systemsProgramProfile = CheckedRuntime
  , systemsProgramFunctions = Map.singleton "Res010Worker" systemsFunction
  }

systemsFunction :: SystemsFunction
systemsFunction = SystemsFunction
  { systemsFunctionName = "Res010Worker"
  , systemsFunctionEntry = BlockId "left"
  , systemsFunctionValues = Map.fromList
      [ valueEntry "payload.source" (OwnedBuffer "Bytes4096")
      , valueEntry "payload.transported" (OwnedBuffer "BytesPayloadLength")
      ]
  , systemsFunctionBlocks = Map.fromList
      [ blockEntry "left" (TermJump (BlockId "join"))
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
