module Phil.Surface.GrammarV1.ResolvedAggregateMode
  ( GrammarV1CheckedResolvedRecordMode (..)
  , GrammarV1CheckedResolvedRecordModeError (..)
  , GrammarV1CheckedResolvedVariantModePayload (..)
  , GrammarV1CheckedResolvedVariantMode (..)
  , GrammarV1CheckedResolvedDataMode (..)
  , GrammarV1CheckedResolvedDataModeError (..)
  , grammarV1CheckedClosedRecordModeWithNamedResolutions
  , grammarV1CheckedClosedDataModeWithNamedResolutions
  ) where

import Data.Text (Text)
import Phil.Core.CheckedBindingMode
  ( CheckedTypeMode (..)
  )
import Phil.Core.Focusing (FocusStep)
import Phil.Core.NominalDataMode
  ( NominalModeError
  , NominalRestrictionJustification
  )
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax (Mode)
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.GrammarV1.CheckedType
  ( GrammarV1CheckedResolvedTypeMode (..)
  , GrammarV1CheckedTypeModeResolutionError
  , GrammarV1ResolvedNamedTypeMode
  , grammarV1CheckedTypeModeWithNamedResolutions
  )
import Phil.Surface.GrammarV1.DataVariants
  ( GrammarV1VariantModeEvidence (..)
  , GrammarV1VariantPayloadModeEvidence (..)
  , grammarV1DataModeFromCheckedVariants
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1DataDecl (..)
  , GrammarV1Field (..)
  , GrammarV1RecordDecl (..)
  , GrammarV1VariantDecl (..)
  , GrammarV1VariantPayload (..)
  )
import Phil.Surface.GrammarV1.RecordFields
  ( grammarV1RecordModeFromCheckedFields
  )
import Phil.Surface.Syntax (Located (..))

data GrammarV1CheckedResolvedRecordMode = GrammarV1CheckedResolvedRecordMode
  { checkedResolvedRecordModeFields
      :: [(Text, GrammarV1CheckedResolvedTypeMode, [FocusStep])]
  , checkedResolvedRecordStructuralMode :: Mode
  }
  deriving (Eq, Show)

data GrammarV1CheckedResolvedRecordModeError
  = GrammarV1ResolvedRecordModeTypeError GrammarV1CheckedTypeModeResolutionError
  | GrammarV1ResolvedRecordModeNominalError NominalModeError
  deriving (Eq, Show)

-- | Compose #616 named-type resolution into the already-authoritative closed
-- record nominal-mode bridge. Each field is checked exactly once through the
-- resolution-aware type-mode path. Stable named declaration provenance remains
-- attached to the field result; only its exact Mode is projected into Core's
-- existing nominal record-mode checker.
--
-- Generic and requirement-bearing records remain outside this closed fragment.
-- Missing/ambiguous/wrong-kind named evidence remains a type-resolution error;
-- nominal strengthening/weakening remains a distinct Core nominal-mode error.
grammarV1CheckedClosedRecordModeWithNamedResolutions
  :: StaticContext
  -> [GrammarV1ResolvedNamedTypeMode]
  -> Maybe NominalRestrictionJustification
  -> GrammarV1RecordDecl
  -> Maybe
      (Either
        GrammarV1CheckedResolvedRecordModeError
        GrammarV1CheckedResolvedRecordMode)
grammarV1CheckedClosedRecordModeWithNamedResolutions
    staticContext resolutions justification source
  | not (null (grammarV1RecordGenericParams source)) = Nothing
  | not (null (grammarV1RecordRequirements source)) = Nothing
  | otherwise = do
      checkedResults <- mapM checkField (grammarV1RecordFields source)
      case sequence checkedResults of
        Left err -> Just (Left (GrammarV1ResolvedRecordModeTypeError err))
        Right checkedFields -> do
          nominalResult <- grammarV1RecordModeFromCheckedFields
            [ (name, checkedBindingMode (checkedResolvedTypeMode resolved))
            | (name, resolved, _) <- checkedFields
            ]
            justification
            source
          pure $ case nominalResult of
            Left err -> Left (GrammarV1ResolvedRecordModeNominalError err)
            Right mode -> Right GrammarV1CheckedResolvedRecordMode
              { checkedResolvedRecordModeFields = checkedFields
              , checkedResolvedRecordStructuralMode = mode
              }
  where
    checkField (Located _ field) = do
      result <- grammarV1CheckedTypeModeWithNamedResolutions
        staticContext
        emptySurfaceState
        resolutions
        (locatedValue (grammarV1FieldType field))
      pure $ fmap
        (\(resolved, steps) ->
          ( locatedValue (grammarV1FieldName field)
          , resolved
          , steps
          ))
        result

data GrammarV1CheckedResolvedVariantModePayload
  = GrammarV1CheckedResolvedVariantModeRecord
      [(Text, GrammarV1CheckedResolvedTypeMode, [FocusStep])]
  | GrammarV1CheckedResolvedVariantModeTuple
      [(GrammarV1CheckedResolvedTypeMode, [FocusStep])]
  deriving (Eq, Show)

data GrammarV1CheckedResolvedVariantMode = GrammarV1CheckedResolvedVariantMode
  { checkedResolvedVariantModeName :: Text
  , checkedResolvedVariantModePayload
      :: Maybe GrammarV1CheckedResolvedVariantModePayload
  }
  deriving (Eq, Show)

data GrammarV1CheckedResolvedDataMode = GrammarV1CheckedResolvedDataMode
  { checkedResolvedDataModeVariants :: [GrammarV1CheckedResolvedVariantMode]
  , checkedResolvedDataStructuralMode :: Mode
  }
  deriving (Eq, Show)

data GrammarV1CheckedResolvedDataModeError
  = GrammarV1ResolvedDataModeTypeError GrammarV1CheckedTypeModeResolutionError
  | GrammarV1ResolvedDataModeNominalError NominalModeError
  deriving (Eq, Show)

-- | Symmetric resolution-aware composition for closed data/sum declarations.
-- Variant order, names, nullary-vs-explicit-empty payload shape, record field
-- order, tuple arity, exact CheckedTypeMode values, focus traces, and named
-- declaration provenance are retained before the exact mode-only projection into
-- the existing sum-mode correspondence and Core nominal authority.
grammarV1CheckedClosedDataModeWithNamedResolutions
  :: StaticContext
  -> [GrammarV1ResolvedNamedTypeMode]
  -> Maybe NominalRestrictionJustification
  -> GrammarV1DataDecl
  -> Maybe
      (Either
        GrammarV1CheckedResolvedDataModeError
        GrammarV1CheckedResolvedDataMode)
grammarV1CheckedClosedDataModeWithNamedResolutions
    staticContext resolutions justification declaration
  | not (null (grammarV1DataGenericParams declaration)) = Nothing
  | not (null (grammarV1DataRequirements declaration)) = Nothing
  | otherwise = do
      checkedResults <- mapM checkVariant (grammarV1DataVariants declaration)
      case sequence checkedResults of
        Left err -> Just (Left (GrammarV1ResolvedDataModeTypeError err))
        Right checkedVariants -> do
          nominalResult <- grammarV1DataModeFromCheckedVariants
            (map checkedVariantEvidence checkedVariants)
            justification
            declaration
          pure $ case nominalResult of
            Left err -> Left (GrammarV1ResolvedDataModeNominalError err)
            Right mode -> Right GrammarV1CheckedResolvedDataMode
              { checkedResolvedDataModeVariants = checkedVariants
              , checkedResolvedDataStructuralMode = mode
              }
  where
    checkVariant (Located _ variant) = do
      payload <- checkPayload (grammarV1VariantPayload variant)
      pure $ fmap
        (GrammarV1CheckedResolvedVariantMode
          (locatedValue (grammarV1VariantName variant)))
        payload

    checkPayload Nothing = Just (Right Nothing)
    checkPayload (Just payload) = case payload of
      GrammarV1VariantRecord fields -> do
        checked <- collect (map checkField fields)
        pure (fmap (Just . GrammarV1CheckedResolvedVariantModeRecord) checked)
      GrammarV1VariantTuple types -> do
        checked <- collect (map checkType types)
        pure (fmap (Just . GrammarV1CheckedResolvedVariantModeTuple) checked)

    checkField (Located _ field) = do
      checked <- grammarV1CheckedTypeModeWithNamedResolutions
        staticContext
        emptySurfaceState
        resolutions
        (locatedValue (grammarV1FieldType field))
      pure $ fmap
        (\(resolved, steps) ->
          (locatedValue (grammarV1FieldName field), resolved, steps))
        checked

    checkType (Located _ sourceType) =
      grammarV1CheckedTypeModeWithNamedResolutions
        staticContext emptySurfaceState resolutions sourceType

checkedVariantEvidence
  :: GrammarV1CheckedResolvedVariantMode
  -> GrammarV1VariantModeEvidence
checkedVariantEvidence checked = GrammarV1VariantModeEvidence
  { grammarV1VariantModeName = checkedResolvedVariantModeName checked
  , grammarV1VariantModePayload =
      payloadEvidence <$> checkedResolvedVariantModePayload checked
  }

payloadEvidence
  :: GrammarV1CheckedResolvedVariantModePayload
  -> GrammarV1VariantPayloadModeEvidence
payloadEvidence payload = case payload of
  GrammarV1CheckedResolvedVariantModeRecord fields ->
    GrammarV1VariantRecordModeEvidence
      [ (name, checkedBindingMode (checkedResolvedTypeMode resolved))
      | (name, resolved, _) <- fields
      ]
  GrammarV1CheckedResolvedVariantModeTuple values ->
    GrammarV1VariantTupleModeEvidence
      [ checkedBindingMode (checkedResolvedTypeMode resolved)
      | (resolved, _) <- values
      ]

collect :: [Maybe (Either e a)] -> Maybe (Either e [a])
collect [] = Just (Right [])
collect (candidate : rest) = do
  value <- candidate
  case value of
    Left err -> pure (Left err)
    Right accepted -> do
      remaining <- collect rest
      pure ((accepted :) <$> remaining)
