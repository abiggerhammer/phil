module Phil.Core.Checker
  ( CheckState (..)
  , CheckerError (..)
  , emptyCheckState
  , emitObligation
  , completeComponent
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Phil.Core.Context (CheckError, ResourceContext, emptyContext, ensureComplete)
import Phil.Core.Syntax (Obligation (..), ObligationId)

data CheckState = CheckState
  { resourceContext :: ResourceContext
  , residualObligations :: Map ObligationId Obligation
  }
  deriving (Eq, Show)

data CheckerError
  = ResourceError CheckError
  | ConflictingObligationId Obligation Obligation
  deriving (Eq, Show)

emptyCheckState :: CheckState
emptyCheckState = CheckState emptyContext Map.empty

emitObligation :: Obligation -> CheckState -> Either CheckerError CheckState
emitObligation obligation state =
  case Map.lookup (obligationId obligation) (residualObligations state) of
    Nothing -> Right (state
      { residualObligations = Map.insert (obligationId obligation) obligation (residualObligations state)
      })
    Just existing
      | existing == obligation -> Right state
      | otherwise -> Left (ConflictingObligationId existing obligation)

completeComponent :: CheckState -> Either CheckerError CheckState
completeComponent state =
  case ensureComplete (resourceContext state) of
    Left err -> Left (ResourceError err)
    Right () -> Right state
