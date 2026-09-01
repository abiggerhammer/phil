module Phil.Surface.GrammarV1.IntrinsicValidatedType
  ( grammarV1BareValidatedType
  ) where

import qualified Data.Text as Text
import Phil.Core.Syntax (Name (..), Ty (..))
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Expression (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1StaticReference (..)
  , GrammarV1Type (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Preserve a Grammar-v1 Validated[...] type exactly only when every identity
-- already has a lossless Core carrier: an unspecialized validator reference and
-- two simple unqualified term names. Qualified validator spelling is preserved
-- verbatim as Text. Specialized validators, qualified/called/projected term
-- identities, and other forms remain unresolved rather than being flattened or
-- reinterpreted merely to construct TyValidated.
grammarV1BareValidatedType :: GrammarV1Type -> Maybe Ty
grammarV1BareValidatedType sourceType = case sourceType of
  GrammarV1ValidatedType (Located _ validator) input evidence
    | null (grammarV1StaticReferenceArguments validator) -> do
        validatorName <- qualifiedReferenceText validator
        inputName <- simpleTermIdentity input
        evidenceName <- simpleTermIdentity evidence
        Just (TyValidated validatorName (Name inputName) (Name evidenceName))
  _ -> Nothing

qualifiedReferenceText :: GrammarV1StaticReference -> Maybe Text.Text
qualifiedReferenceText reference =
  case grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) of
    [] -> Nothing
    parts -> Just (Text.intercalate (Text.singleton '.') parts)

simpleTermIdentity :: Located GrammarV1Expression -> Maybe Text.Text
simpleTermIdentity (Located _ expression) = case expression of
  GrammarV1NameExpression reference arguments
    | null arguments
    , null (grammarV1StaticReferenceArguments reference) ->
        case grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) of
          [name] -> Just name
          _ -> Nothing
  _ -> Nothing
