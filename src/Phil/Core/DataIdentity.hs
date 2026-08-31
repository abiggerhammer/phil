module Phil.Core.DataIdentity
  ( DataTypeRef (..)
  , resolveDataType
  , definitionallyEqualDataType
  ) where

import qualified DataIdentityKernel as Kernel

data DataTypeRef
  = NominalType String
  | TransparentAlias String DataTypeRef
  deriving (Eq, Show)

resolveDataType :: DataTypeRef -> DataTypeRef
resolveDataType ref = case ref of
  NominalType _ -> ref
  TransparentAlias _ target -> resolveDataType target

definitionallyEqualDataType :: DataTypeRef -> DataTypeRef -> Bool
definitionallyEqualDataType left right =
  case Kernel.decideDataIdentityByFact
      (resolveDataType left == resolveDataType right) of
    Kernel.DataIdentityAccepted -> True
    Kernel.DataIdentityRejected -> False
