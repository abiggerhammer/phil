module Phil.Surface.GrammarV1.RecordFields
  ( grammarV1CheckedRecordFields
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
