module Phil.Surface.GrammarV1.DataVariants
  ( GrammarV1CheckedVariantPayload (..)
  , GrammarV1CheckedVariant (..)
  , GrammarV1VariantPayloadModeEvidence (..)
  , GrammarV1VariantModeEvidence (..)
  , grammarV1CheckedDataVariants
  , grammarV1DataModeFromCheckedVariants
  ) where

import Data.Text (Text)
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.NominalDataMode
  ( NominalModeError
  , NominalRestrictionJustification
  , checkSumMode
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
  ( GrammarV1DataDecl (..)
  , GrammarV1Field (..)
  , GrammarV1VariantDecl (..)
  , GrammarV1VariantPayload (..)
  )
import Phil.Surface.Syntax (Located (..))

data GrammarV1CheckedVariantPayload
  = GrammarV1CheckedVariantRecord [(Text, Ty, [FocusStep])]
  | GrammarV1CheckedVariantTuple [(Ty, [FocusStep])]
  deriving (Eq, Show)

data GrammarV1CheckedVariant = GrammarV1CheckedVariant
  { grammarV1CheckedVariantName :: Text
  , grammarV1CheckedVariantPayload :: Maybe GrammarV1CheckedVariantPayload
  }
  deriving (Eq, Show)

-- | Exact checked structural-mode evidence for one source variant payload.
-- Record evidence retains field identity/order; tuple evidence retains arity/order.
-- The outer Maybe remains significant so a nullary variant stays distinct from an
-- explicitly empty tuple or record payload before aggregate mode is computed.
data GrammarV1VariantPayloadModeEvidence
  = GrammarV1VariantRecordModeEvidence [(Text, Mode)]
  | GrammarV1VariantTupleModeEvidence [Mode]
  deriving (Eq, Show)

data GrammarV1VariantModeEvidence = GrammarV1VariantModeEvidence
  { grammarV1VariantModeName :: Text
  , grammarV1VariantModePayload :: Maybe GrammarV1VariantPayloadModeEvidence
  }
  deriving (Eq, Show)

-- | Project the closed Grammar-v1 sum/data variant surface without inventing
-- aggregate structural-mode or constructor-identity semantics. Variant names,
-- source order, and nullary/record/tuple payload shape are preserved exactly.
-- Every payload type delegates once to the uniform checked-type path under an
-- empty top-level term scope. Core focusing errors remain distinct from source
-- non-competence; one unsupported payload type rejects the whole projection.
-- Generic parameters and generic requirements remain outside this first bounded
-- data-declaration fragment.
grammarV1CheckedDataVariants
  :: StaticContext
  -> GrammarV1DataDecl
  -> Maybe (Either FocusingError [GrammarV1CheckedVariant])
grammarV1CheckedDataVariants staticContext declaration
  | not (null (grammarV1DataGenericParams declaration)) = Nothing
  | not (null (grammarV1DataRequirements declaration)) = Nothing
  | otherwise = collect (map elaborateVariant (grammarV1DataVariants declaration))
  where
    elaborateVariant (Located _ variant) = do
      payload <- elaboratePayload (grammarV1VariantPayload variant)
      pure $ fmap
        (GrammarV1CheckedVariant (locatedValue (grammarV1VariantName variant)))
        payload

    elaboratePayload Nothing = Just (Right Nothing)
    elaboratePayload (Just payload) = case payload of
      GrammarV1VariantRecord fields -> do
        checked <- collect (map elaborateField fields)
        pure (fmap (Just . GrammarV1CheckedVariantRecord) checked)
      GrammarV1VariantTuple types -> do
        checked <- collect (map elaborateType types)
        pure (fmap (Just . GrammarV1CheckedVariantTuple) checked)

    elaborateField (Located _ field) = do
      checked <- grammarV1CheckedType
        staticContext
        emptySurfaceState
        (locatedValue (grammarV1FieldType field))
      pure $ fmap
        (\(ty, steps) -> (locatedValue (grammarV1FieldName field), ty, steps))
        checked

    elaborateType (Located _ sourceType) =
      grammarV1CheckedType staticContext emptySurfaceState sourceType

-- | Route one closed Grammar-v1 data/sum declaration's structural mode through
-- Core's existing nominal data-mode authority once exact checked structural-mode
-- evidence for every constructor payload has been supplied by a competent type/
-- resource checker. This bridge deliberately does not derive Mode from Ty.
--
-- Variant identity/order and payload shape must match the source declaration
-- exactly before any modes are folded. Nullary, explicit empty tuple, and
-- explicit empty record payloads remain distinct at this correspondence seam;
-- record field identity/order and tuple arity/order are checked as well. Once
-- correspondence is established, Core 'checkSumMode' exclusively owns
-- conservative aggregate derivation, no-weakening, and justified nominal
-- strengthening. Source spelling never manufactures strengthening evidence.
--
-- Generic and requirement-bearing data declarations retain the same fail-closed
-- boundary as 'grammarV1CheckedDataVariants'.
grammarV1DataModeFromCheckedVariants
  :: [GrammarV1VariantModeEvidence]
  -> Maybe NominalRestrictionJustification
  -> GrammarV1DataDecl
  -> Maybe (Either NominalModeError Mode)
grammarV1DataModeFromCheckedVariants checkedVariants justification declaration
  | not (null (grammarV1DataGenericParams declaration)) = Nothing
  | not (null (grammarV1DataRequirements declaration)) = Nothing
  | otherwise = do
      constructorPayloadModes <-
        matchVariants (grammarV1DataVariants declaration) checkedVariants
      pure $
        checkSumMode
          constructorPayloadModes
          (grammarV1StructuralMode <$> grammarV1DataMode declaration)
          justification

matchVariants
  :: [Located GrammarV1VariantDecl]
  -> [GrammarV1VariantModeEvidence]
  -> Maybe [[Mode]]
matchVariants [] [] = Just []
matchVariants (Located _ source : sources) (checked : checkedRest)
  | locatedValue (grammarV1VariantName source) /= grammarV1VariantModeName checked = Nothing
  | otherwise = do
      payloadModes <-
        matchPayload
          (grammarV1VariantPayload source)
          (grammarV1VariantModePayload checked)
      remaining <- matchVariants sources checkedRest
      pure (payloadModes : remaining)
matchVariants _ _ = Nothing

matchPayload
  :: Maybe GrammarV1VariantPayload
  -> Maybe GrammarV1VariantPayloadModeEvidence
  -> Maybe [Mode]
matchPayload Nothing Nothing = Just []
matchPayload
  (Just (GrammarV1VariantRecord sourceFields))
  (Just (GrammarV1VariantRecordModeEvidence checkedFields))
  | sourceFieldNames == map fst checkedFields = Just (map snd checkedFields)
  | otherwise = Nothing
  where
    sourceFieldNames =
      map
        (locatedValue . grammarV1FieldName . locatedValue)
        sourceFields
matchPayload
  (Just (GrammarV1VariantTuple sourceTypes))
  (Just (GrammarV1VariantTupleModeEvidence checkedModes))
  | length sourceTypes == length checkedModes = Just checkedModes
  | otherwise = Nothing
matchPayload _ _ = Nothing

collect :: [Maybe (Either e a)] -> Maybe (Either e [a])
collect [] = Just (Right [])
collect (candidate : rest) = do
  value <- candidate
  case value of
    Left err -> pure (Left err)
    Right accepted -> do
      remaining <- collect rest
      pure ((accepted :) <$> remaining)
