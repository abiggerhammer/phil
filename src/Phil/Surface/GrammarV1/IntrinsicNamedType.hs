module Phil.Surface.GrammarV1.IntrinsicNamedType
  ( grammarV1BareNamedType
  ) where

import qualified Data.Text as Text
import Phil.Core.Syntax (Ty (..))
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1QualifiedName (..)
  , GrammarV1StaticReference (..)
  , GrammarV1Type (..)
  )

-- | Preserve an unspecialized Grammar-v1 named type exactly as Core opaque type
-- identity. Qualified source name parts are joined without reinterpretation.
-- Specialized named references remain fail-closed because flattening their
-- static arguments into Text would erase semantically relevant structure before
-- the competent generic/static elaboration boundary has interpreted it.
grammarV1BareNamedType :: GrammarV1Type -> Maybe Ty
grammarV1BareNamedType sourceType = case sourceType of
  GrammarV1NamedType reference
    | null (grammarV1StaticReferenceArguments reference) ->
        case grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) of
          [] -> Nothing
          parts ->
            Just (TyOpaque (Text.intercalate (Text.singleton '.') parts))
  _ -> Nothing
