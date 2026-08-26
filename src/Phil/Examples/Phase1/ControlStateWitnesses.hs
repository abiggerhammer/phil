{-# LANGUAGE OverloadedStrings #-}

module Phil.Examples.Phase1.ControlStateWitnesses
  ( steveControlStateStageBundle
  , stevePutOkBoundary
  , stevePutInstalledProjection
  , stevePutAlreadyExistsProjection
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Syntax (Mode (..))
import Phil.Examples.Phase1.BranchResourceWitnesses
  ( steveBranchResourceStageBundle
  )
import Phil.Examples.Phase1.SubjectWitnesses
  ( steveCandidateSubject
  )
import Phil.Systems.ControlStateProjection
import Phil.Systems.IR (BlockId (..), ValueId (..))
import Phil.Systems.SubjectCorrespondence (SystemsValueRef (..))

steveControlStateStageBundle :: Either String ControlStateStageBundle
steveControlStateStageBundle = do
  base <- steveBranchResourceStageBundle
  pure (makeControlStateStageBundle
    base
    (Map.singleton stevePutOkBoundaryKey stevePutOkBoundary)
    (Map.fromList
      [ (stateProjectionKey stevePutInstalledProjection, stevePutInstalledProjection)
      , (stateProjectionKey stevePutAlreadyExistsProjection, stevePutAlreadyExistsProjection)
      ])
    Map.empty)

stevePutOkBoundaryKey :: StateBoundaryKey
stevePutOkBoundaryKey = StateBoundaryKey "steve.put.ok.join.v1"

steveCandidateSlot :: StateSlotKey
steveCandidateSlot = StateSlotKey "candidate-owner"

steveCandidateRef :: SystemsValueRef
steveCandidateRef = SystemsValueRef "StevePut" (ValueId "put.candidate")

stevePutOkBoundary :: StateBoundaryContract
stevePutOkBoundary = StateBoundaryContract
  { stateBoundaryKey = stevePutOkBoundaryKey
  , stateBoundaryKind = OrdinaryJoinBoundary
  , stateBoundaryFunction = "StevePut"
  , stateBoundaryTargetBlock = BlockId "put.ok"
  , stateBoundarySlots = Map.singleton steveCandidateSlot StateSlotContract
      { stateSlotKey = steveCandidateSlot
      , stateSlotMode = Linear
      , stateSlotSubjectRequirement = FixedStateSubject steveCandidateSubject
      }
  }

stevePutInstalledProjection :: StateProjection
stevePutInstalledProjection = putOkProjection
  "steve.put.ok.installed" "installed"

stevePutAlreadyExistsProjection :: StateProjection
stevePutAlreadyExistsProjection = putOkProjection
  "steve.put.ok.already-exists" "already-exists"

putOkProjection :: Text -> Text -> StateProjection
putOkProjection projectionName edgeLabel = StateProjection
  { stateProjectionKey = StateProjectionKey projectionName
  , stateProjectionKind = OrdinaryJoinPredecessor
  , stateProjectionBoundary = stevePutOkBoundaryKey
  , stateProjectionFromBlock = BlockId "put.install"
  , stateProjectionEdgeLabel = edgeLabel
  , stateProjectionIncomingRestricted = Map.singleton steveCandidateRef Linear
  , stateProjectionBindings = Map.singleton steveCandidateSlot steveCandidateRef
  }
