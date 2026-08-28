module Phil.Core.DataBorrow
  ( BorrowedAggregateField (..)
  , DataBorrowError (..)
  , beginBorrowedAggregateField
  , endBorrowedAggregateField
  ) where

import Data.List (find)
import Phil.Core.Context
  ( CheckError
  , ResourceContext
  , endSharedLoan
  , startSharedLoan
  )
import Phil.Core.DataDestruction
  ( OwnedField (..)
  )
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
