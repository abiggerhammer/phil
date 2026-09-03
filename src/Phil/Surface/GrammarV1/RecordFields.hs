module Phil.Surface.GrammarV1.RecordFields
  ( grammarV1CheckedRecordFields
  , grammarV1RecordModeFromCheckedFields
  ) where

import Data.Text (Text)
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.NominalDataMode
  ( NominalModeError
  , NominalRestrictionJustification
  , checkRecordMode
  )
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax
  ( Mode
  , Ty
  )
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.GrammarV1.CheckedType
  ( grammarV1CheckedType
  )
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1StructuralMode
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Field (..)
  , GrammarV1RecordDecl (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Project the field typing surface of one closed Grammar-v1 record into the
-- uniform checked type semantics. This is intentionally not a complete record
-- declaration elaborator: aggregate structural mode, nominal strengthening,
-- field-name uniqueness, construction/elimination behavior, and declaration
-- identity remain separate semantic obligations.
--
-- Generic and requirement-bearing records remain outside this first bounded
-- fragment. Each field target is checked under an empty top-level term scope,
-- so a record declaration cannot accidentally inherit caller-local bindings.
-- Field spelling and source order are preserved exactly, including duplicates;
-- this bridge does not invent a uniqueness rule whose authority is not present
-- here. Explicit record mode likewise has no effect on this field-only view.
grammarV1CheckedRecordFields
  :: StaticContext
  -> GrammarV1RecordDecl
  -> Maybe (Either FocusingError [(Text, Ty, [FocusStep])])
grammarV1CheckedRecordFields staticContext source
  | not (null (grammarV1RecordGenericParams source)) = Nothing
  | not (null (grammarV1RecordRequirements source)) = Nothing
  | otherwise = do
      checked <- mapM checkField (grammarV1RecordFields source)
      pure (sequence checked)
  where
    checkField (Located _ field) = do
      result <- grammarV1CheckedType
        staticContext
        emptySurfaceState
        (locatedValue (grammarV1FieldType field))
      pure $ fmap
        (\(ty, steps) ->
          ( locatedValue (grammarV1FieldName field)
          , ty
          , steps
          ))
        result

-- | Route one closed Grammar-v1 record's declaration-level structural mode
-- through Core's existing nominal data-mode authority once the exact checked
-- mode of every owned field has been supplied by a competent type/resource
-- checker. This bridge deliberately does not derive Mode from Ty: that general
-- correspondence remains a separate semantic authority wall.
--
-- Supplied field names must match the source field list exactly, including
-- order and duplicates, so an aggregate mode cannot silently be computed from
-- another record's field-mode set. Omitted source mode derives the ordinary
-- strongest-owned-field mode. An explicit source mode is only a strengthening
-- candidate; Core rejects weakening and requires an admitted nominal resource/
-- lifecycle justification for a strict strengthening. This surface bridge does
-- not manufacture that justification.
--
-- Generic and requirement-bearing records retain the same fail-closed boundary
-- as 'grammarV1CheckedRecordFields'.
grammarV1RecordModeFromCheckedFields
  :: [(Text, Mode)]
  -> Maybe NominalRestrictionJustification
  -> GrammarV1RecordDecl
  -> Maybe (Either NominalModeError Mode)
grammarV1RecordModeFromCheckedFields checkedFieldModes justification source
  | not (null (grammarV1RecordGenericParams source)) = Nothing
  | not (null (grammarV1RecordRequirements source)) = Nothing
  | map fst checkedFieldModes /= sourceFieldNames = Nothing
  | otherwise = Just $
      checkRecordMode
        (map snd checkedFieldModes)
        (grammarV1StructuralMode <$> grammarV1RecordMode source)
        justification
  where
    sourceFieldNames =
      map
        (locatedValue . grammarV1FieldName . locatedValue)
        (grammarV1RecordFields source)
