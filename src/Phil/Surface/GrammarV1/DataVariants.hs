module Phil.Surface.GrammarV1.DataVariants
  ( GrammarV1CheckedVariantPayload (..)
  , GrammarV1CheckedVariant (..)
  , grammarV1CheckedDataVariants
  ) where

import Data.Text (Text)
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax (Ty)
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.GrammarV1.CheckedType
  ( grammarV1CheckedType
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

collect :: [Maybe (Either e a)] -> Maybe (Either e [a])
collect [] = Just (Right [])
collect (candidate : rest) = do
  value <- candidate
  case value of
    Left err -> pure (Left err)
    Right accepted -> do
      remaining <- collect rest
      pure ((accepted :) <$> remaining)
