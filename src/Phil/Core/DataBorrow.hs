module Phil.Core.DataBorrow
  ( BorrowedAggregateField (..)
  , DataBorrowError (..)
  , beginBorrowedAggregateField
  , endBorrowedAggregateField
  ) where

import Control.Monad (unless)
import Data.List (find)
import qualified Data.Set as Set
import Phil.Core.Context
  ( CheckError (..)
  , ResourceContext (..)
  , endSharedLoan
  , ensureComplete
  , startSharedLoan
  , useBinding
  )
import Phil.Core.DataDestruction
  ( OwnedField (..)
  )
import qualified Phil.Core.DataEliminationKernelBridge as KernelBridge
import Phil.Core.Syntax (Mode, Name, Ty)

-- | DATA-006 makes aggregate observation explicit without creating another
-- owning occurrence for the selected field.  The aggregate owner remains the
-- resource tracked by the ordinary ADR-002 shared-loan machinery.
data BorrowedAggregateField = BorrowedAggregateField
  { borrowedAggregateOwner :: Name
  , borrowedAggregateField :: Name
  , borrowedAggregateFieldMode :: Mode
  , borrowedAggregateFieldType :: Ty
  }
  deriving (Eq, Show)

data DataBorrowError
  = DataBorrowContextError CheckError
  | UnknownBorrowedAggregateField Name
  | CertifiedDataEliminationBorrowKernelDisagreement
  deriving (Eq, Show)

beginBorrowedAggregateField
  :: Name
  -> [OwnedField]
  -> Name
  -> ResourceContext
  -> Either DataBorrowError (BorrowedAggregateField, ResourceContext)
beginBorrowedAggregateField owner fields fieldName context = do
  field <- case find ((== fieldName) . ownedFieldName) fields of
    Nothing -> Left (UnknownBorrowedAggregateField fieldName)
    Just value -> Right value
  next <- mapLeft DataBorrowContextError (startSharedLoan owner context)
  let loanStarted = Set.member owner (sharedLoans next)
      ownerImmobilized = case useBinding owner next of
        Left (OwnerBorrowed actual) -> actual == owner
        _ -> False
      activeLoanRejectedAtBoundary = case ensureComplete next of
        Left (EscapingLoans loans) -> Set.member owner loans
        _ -> False
      loanEndPreservedOwner = case endSharedLoan owner next of
        Right restored -> restored == context
        Left _ -> False
  unless
    ( KernelBridge.borrowLifecycleAccepted
        True
        loanStarted
        ownerImmobilized
        activeLoanRejectedAtBoundary
        loanEndPreservedOwner
    ) $
    Left CertifiedDataEliminationBorrowKernelDisagreement
  Right
    ( BorrowedAggregateField
        { borrowedAggregateOwner = owner
        , borrowedAggregateField = fieldName
        , borrowedAggregateFieldMode = ownedFieldMode field
        , borrowedAggregateFieldType = ownedFieldType field
        }
    , next
    )

endBorrowedAggregateField
  :: BorrowedAggregateField
  -> ResourceContext
  -> Either DataBorrowError ResourceContext
endBorrowedAggregateField borrowed context =
  mapLeft DataBorrowContextError $
    endSharedLoan (borrowedAggregateOwner borrowed) context

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
