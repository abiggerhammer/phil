module Phil.Core.DataIdentity
  ( DataTypeRef (..)
  , resolveDataType
  , definitionallyEqualDataType
  ) where

data DataTypeRef
  = NominalType String
  | TransparentAlias String DataTypeRef
  deriving (Eq, Show)

resolveDataType :: DataTypeRef -> DataTypeRef
resolveDataType ref = case ref of
  NominalType _ -> ref
  TransparentAlias _ target -> resolveDataType target

definitionallyEqualDataType :: DataTypeRef -> DataTypeRef -> Bool
definitionallyEqualDataType left right = resolveDataType left == resolveDataType right
