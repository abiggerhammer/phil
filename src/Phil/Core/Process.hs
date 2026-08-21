module Phil.Core.Process
  ( FlowPath
  , ProcessFlow
  , ProcessError (..)
  , flowPaths
  , pathControl
  , pathState
  , continueFlow
  , returnFlow
  , closedFlow
  , failedFlow
  , sequenceFlow
  , joinBranches
  ) where

import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Checker (CheckState (..))
import Phil.Core.Context
  ( CheckError (..)
  , ResourceContext (..)
  , ensureComplete
  , joinContinuing
  )
import Phil.Core.Syntax (Control (..), Outcome, Ty)

data FlowPath = FlowPath
  { pathControl :: Control
  , pathState :: CheckState
  }
  deriving (Eq, Show)

newtype ProcessFlow = ProcessFlow
  { unProcessFlow :: [FlowPath]
  }
  deriving (Eq, Show)

data ProcessError
  = InvalidReturnState CheckError
  | InvalidTerminalState Control CheckError
  | BranchJoinError CheckError
  | EmptyBranchSet
  deriving (Eq, Show)

flowPaths :: ProcessFlow -> [FlowPath]
flowPaths = unProcessFlow

continueFlow :: CheckState -> ProcessFlow
continueFlow state = ProcessFlow [FlowPath Continue state]

returnFlow :: Ty -> CheckState -> Either ProcessError ProcessFlow
returnFlow returnTy state = do
  ensureReturnable state
  pure (ProcessFlow [FlowPath (Return returnTy) state])

closedFlow :: Outcome -> CheckState -> Either ProcessError ProcessFlow
closedFlow outcome = terminalFlow (Closed outcome)

failedFlow :: Text -> Text -> CheckState -> Either ProcessError ProcessFlow
failedFlow failureClass detail = terminalFlow (Failed failureClass detail)

sequenceFlow
  :: ProcessFlow
  -> (CheckState -> Either ProcessError ProcessFlow)
  -> Either ProcessError ProcessFlow
sequenceFlow (ProcessFlow paths) continuation =
  ProcessFlow . concat <$> mapM advance paths
  where
    advance path =
      case pathControl path of
        Continue -> unProcessFlow <$> continuation (pathState path)
        Return _ -> pure [path]
        Closed _ -> pure [path]
        Failed _ _ -> pure [path]

joinBranches :: [ProcessFlow] -> Either ProcessError ProcessFlow
joinBranches [] = Left EmptyBranchSet
joinBranches flows = do
  let paths = concatMap unProcessFlow flows
      continuingPaths = filter ((== Continue) . pathControl) paths
  joinedContext <-
    case continuingPaths of
      [] -> pure Nothing
      _ -> Just <$> mapLeft BranchJoinError
        (joinContinuing (map (resourceContext . pathState) continuingPaths))
  pure (ProcessFlow (map (normalizeContinue joinedContext) paths))

normalizeContinue :: Maybe ResourceContext -> FlowPath -> FlowPath
normalizeContinue joinedContext path =
  case (pathControl path, joinedContext) of
    (Continue, Just context) ->
      path
        { pathState = (pathState path)
            { resourceContext = context
            }
        }
    _ -> path

terminalFlow :: Control -> CheckState -> Either ProcessError ProcessFlow
terminalFlow control state =
  case ensureComplete (resourceContext state) of
    Left err -> Left (InvalidTerminalState control err)
    Right () -> Right (ProcessFlow [FlowPath control state])

ensureReturnable :: CheckState -> Either ProcessError ()
ensureReturnable state
  | Set.null loans = Right ()
  | otherwise = Left (InvalidReturnState (EscapingLoans loans))
  where
    loans = sharedLoans (resourceContext state)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
