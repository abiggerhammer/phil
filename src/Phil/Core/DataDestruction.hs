module Phil.Core.DataDestruction
  ( OwnedField (..)
  , FieldDisposition (..)
  , DataDestructionError (..)
  , checkFieldDispositions
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Phil.Core.Syntax (Mode (..), Name, Ty)

data OwnedField = OwnedField
  { ownedFieldName :: Name
  , ownedFieldMode :: Mode
  , ownedFieldType :: Ty
  }
  deriving (Eq, Show)

data FieldDisposition
  = FieldBound
  | FieldOmitted
  deriving (Eq, Show)

data DataDestructionError
  = DuplicateFieldDisposition Name
  | UnknownFieldDisposition Name
  | MissingLinearFieldDisposition Name
  deriving (Eq, Show)

checkFieldDispositions
  :: [OwnedField]
  -> [(Name, FieldDisposition)]
  -> Either DataDestructionError ()
checkFieldDispositions fields dispositions = do
  dispositionMap <- buildDispositionMap dispositions
  mapM_ (checkField dispositionMap) fields
  mapM_ (checkKnownField fields) (Map.keys dispositionMap)

buildDispositionMap
  :: [(Name, FieldDisposition)]
  -> Either DataDestructionError (Map Name FieldDisposition)
buildDispositionMap = foldl insertOne (Right Map.empty)
  where
    insertOne accumulated (name, disposition) = do
      current <- accumulated
      if Map.member name current
        then Left (DuplicateFieldDisposition name)
        else Right (Map.insert name disposition current)

checkField
  :: Map Name FieldDisposition
  -> OwnedField
  -> Either DataDestructionError ()
checkField dispositions field =
  case Map.lookup (ownedFieldName field) dispositions of
    Just FieldBound -> Right ()
    Just FieldOmitted -> case ownedFieldMode field of
      Linear -> Left (MissingLinearFieldDisposition (ownedFieldName field))
      _ -> Right ()
    Nothing -> case ownedFieldMode field of
      Linear -> Left (MissingLinearFieldDisposition (ownedFieldName field))
      _ -> Right ()

checkKnownField
  :: [OwnedField]
  -> Name
  -> Either DataDestructionError ()
checkKnownField fields name
  | any ((== name) . ownedFieldName) fields = Right ()
  | otherwise = Left (UnknownFieldDisposition name)
