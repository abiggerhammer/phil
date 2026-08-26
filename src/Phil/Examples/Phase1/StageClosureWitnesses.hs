module Phil.Examples.Phase1.StageClosureWitnesses
  ( uploadStageClosureBundle
  , steveStageClosureBundle
  ) where

import Phil.Examples.Phase1.BoundaryCommitWitnesses
  ( uploadBoundaryCommitStageBundle
  )
import Phil.Examples.Phase1.BranchResourceWitnesses
  ( steveBranchResourceStageBundle
  )
import Phil.Examples.Phase1.NextStageRequirementWitnesses
  ( steveNextStageRequirementStage
  , uploadNextStageRequirementStage
  )
import Phil.Systems.StageClosure

uploadStageClosureBundle :: Either String StageClosureBundle
uploadStageClosureBundle = do
  concrete <- uploadBoundaryCommitStageBundle
  nextStage <- uploadNextStageRequirementStage
  pure (makeStageClosureBundle
    (ConcreteThroughBoundary concrete)
    nextStage)

steveStageClosureBundle :: Either String StageClosureBundle
steveStageClosureBundle = do
  concrete <- steveBranchResourceStageBundle
  nextStage <- steveNextStageRequirementStage
  pure (makeStageClosureBundle
    (ConcreteThroughBranch concrete)
    nextStage)
