module Phil.Core.Generic
  ( GenericValueParameterKey (..)
  , StructuralPermission (..)
  , GenericStructuralUse (..)
  , GenericStructuralRequirements (..)
  , CheckedGenericStructuralInterface (..)
  , GenericStructuralError (..)
  , inferGenericStructuralRequirements
  , checkGenericStructuralInterface
  , modeAllowsStructuralPermission
  , checkGenericStructuralActual
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Syntax (Mode (..))

-- | Stable checked identity for one abstract value parameter in the bounded
-- Phase 1 generic structural checker. Surface spelling is deliberately absent.
newtype GenericValueParameterKey = GenericValueParameterKey
  { unGenericValueParameterKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | ADR-002 structural permissions induced by a generic body. These are not a
-- parallel Copy/Drop trait system: they are the existing structural rules made
-- explicit as generic requirements.
data StructuralPermission
  = WeakeningPermission
  | ContractionPermission
  deriving (Eq, Ord, Show)

-- | Checked semantic use events emitted by generic body checking. A transfer
-- moves the unique occurrence and needs no extra structural permission.
-- Discarding requires weakening; duplicating requires contraction.
data GenericStructuralUse
  = TransferGenericValue GenericValueParameterKey
  | DiscardGenericValue GenericValueParameterKey
  | DuplicateGenericValue GenericValueParameterKey
  deriving (Eq, Ord, Show)

newtype GenericStructuralRequirements = GenericStructuralRequirements
  { genericStructuralPermissions :: Set.Set StructuralPermission
  }
  deriving (Eq, Ord, Show)

-- | The two requirement views that Phase 1 must keep distinct. The induced set
-- is the minimum justified by the current checked body. The published set is
-- the stable interface contract callers must satisfy. Published requirements
-- may deliberately be stronger, but never weaker, than the induced set.
data CheckedGenericStructuralInterface = CheckedGenericStructuralInterface
  { genericInducedStructuralRequirements
      :: Map.Map GenericValueParameterKey GenericStructuralRequirements
  , genericPublishedStructuralRequirements
      :: Map.Map GenericValueParameterKey GenericStructuralRequirements
  }
  deriving (Eq, Ord, Show)

data GenericStructuralError
  = DuplicateGenericValueParameter GenericValueParameterKey
  | UnknownGenericValueParameter GenericValueParameterKey
  | DuplicatePublishedStructuralRequirement GenericValueParameterKey
  | UnknownPublishedGenericValueParameter GenericValueParameterKey
  | PublishedStructuralRequirementTooWeak
      GenericValueParameterKey
      StructuralPermission
  | MissingStructuralPermission
      GenericValueParameterKey
      StructuralPermission
      Mode
  deriving (Eq, Ord, Show)

-- | Infer the canonical minimum structural requirements induced by the checked
-- use events for every declared abstract value parameter. The resulting map
-- contains every parameter, including those with the empty requirement set.
inferGenericStructuralRequirements
  :: [GenericValueParameterKey]
  -> [GenericStructuralUse]
  -> Either GenericStructuralError
      (Map.Map GenericValueParameterKey GenericStructuralRequirements)
inferGenericStructuralRequirements parameters uses = do
  requirements <- initialRequirements parameters
  foldl addUse (Right requirements) uses
  where
    addUse accumulated use = do
      current <- accumulated
      let key = useParameter use
      existing <- maybe
        (Left (UnknownGenericValueParameter key))
        Right
        (Map.lookup key current)
      let permission = case use of
            TransferGenericValue _ -> Nothing
            DiscardGenericValue _ -> Just WeakeningPermission
            DuplicateGenericValue _ -> Just ContractionPermission
          updated = case permission of
            Nothing -> existing
            Just required -> GenericStructuralRequirements
              (Set.insert required (genericStructuralPermissions existing))
      Right (Map.insert key updated current)

-- | Check the current body-induced minimum against an optional explicitly
-- stabilized public contract. With no explicit declaration, the public
-- requirement set is exactly the inferred minimum. With an explicit contract,
-- omitted parameters mean an empty published set; declared requirements may be
-- stronger than the current body but cannot omit any induced permission.
checkGenericStructuralInterface
  :: [GenericValueParameterKey]
  -> [GenericStructuralUse]
  -> Maybe [(GenericValueParameterKey, GenericStructuralRequirements)]
  -> Either GenericStructuralError CheckedGenericStructuralInterface
checkGenericStructuralInterface parameters uses explicitPublished = do
  induced <- inferGenericStructuralRequirements parameters uses
  published <- case explicitPublished of
    Nothing -> Right induced
    Just declarations -> normalizePublishedRequirements parameters declarations
  ensurePublishedCoversInduced induced published
  Right CheckedGenericStructuralInterface
    { genericInducedStructuralRequirements = induced
    , genericPublishedStructuralRequirements = published
    }

-- | Structural mode satisfaction relation inherited directly from ADR-002:
-- unrestricted permits contraction and weakening, affine permits weakening,
-- and linear permits neither.
modeAllowsStructuralPermission :: Mode -> StructuralPermission -> Bool
modeAllowsStructuralPermission mode permission = case (mode, permission) of
  (Unrestricted, _) -> True
  (Affine, WeakeningPermission) -> True
  (Affine, ContractionPermission) -> False
  (Linear, _) -> False

-- | Check one concrete actual against the exact inferred or published
-- structural requirement set supplied by the caller. Failure identifies the
-- first missing canonical permission.
checkGenericStructuralActual
  :: GenericValueParameterKey
  -> Mode
  -> GenericStructuralRequirements
  -> Either GenericStructuralError ()
checkGenericStructuralActual key mode requirements =
  case
    [ permission
    | permission <- Set.toAscList (genericStructuralPermissions requirements)
    , not (modeAllowsStructuralPermission mode permission)
    ] of
      [] -> Right ()
      permission : _ -> Left (MissingStructuralPermission key permission mode)

initialRequirements
  :: [GenericValueParameterKey]
  -> Either GenericStructuralError
      (Map.Map GenericValueParameterKey GenericStructuralRequirements)
initialRequirements = go Set.empty Map.empty
  where
    go _ result [] = Right result
    go seen result (key : rest)
      | Set.member key seen = Left (DuplicateGenericValueParameter key)
      | otherwise = go
          (Set.insert key seen)
          (Map.insert key (GenericStructuralRequirements Set.empty) result)
          rest

normalizePublishedRequirements
  :: [GenericValueParameterKey]
  -> [(GenericValueParameterKey, GenericStructuralRequirements)]
  -> Either GenericStructuralError
      (Map.Map GenericValueParameterKey GenericStructuralRequirements)
normalizePublishedRequirements parameters declarations = do
  initial <- initialRequirements parameters
  go Set.empty initial declarations
  where
    go _ result [] = Right result
    go seen result ((key, requirements) : rest)
      | Set.member key seen = Left (DuplicatePublishedStructuralRequirement key)
      | not (Map.member key result) = Left (UnknownPublishedGenericValueParameter key)
      | otherwise = go
          (Set.insert key seen)
          (Map.insert key requirements result)
          rest

ensurePublishedCoversInduced
  :: Map.Map GenericValueParameterKey GenericStructuralRequirements
  -> Map.Map GenericValueParameterKey GenericStructuralRequirements
  -> Either GenericStructuralError ()
ensurePublishedCoversInduced induced published =
  mapM_ checkOne (Map.toAscList induced)
  where
    checkOne (key, inducedRequirements) =
      let publishedRequirements = Map.findWithDefault
            (GenericStructuralRequirements Set.empty)
            key
            published
          missing = Set.difference
            (genericStructuralPermissions inducedRequirements)
            (genericStructuralPermissions publishedRequirements)
      in case Set.toAscList missing of
          [] -> Right ()
          permission : _ -> Left
            (PublishedStructuralRequirementTooWeak key permission)

useParameter :: GenericStructuralUse -> GenericValueParameterKey
useParameter use = case use of
  TransferGenericValue key -> key
  DiscardGenericValue key -> key
  DuplicateGenericValue key -> key
