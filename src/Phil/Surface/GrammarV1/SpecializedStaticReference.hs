module Phil.Surface.GrammarV1.SpecializedStaticReference
  ( GrammarV1ResolvedDirectStaticArgument (..)
  , GrammarV1CheckedSpecializedStaticReference (..)
  , GrammarV1SpecializedStaticReferenceError (..)
  , grammarV1CheckedSpecializedStaticReference
  ) where

import qualified Data.Text as Text
import Data.Text (Text)
import Phil.Core.Generic
  ( GenericApplicationIdentity
  , GenericApplicationIdentityError
  , deriveGenericApplicationIdentity
  )
import Phil.Core.Generic.StaticActual
  ( CheckedGenericStaticActual (..)
  , GenericStaticActual (..)
  , GenericStaticKind
  , GenericStaticKindError
  , GenericStaticParameter
  , GenericStaticReferenceCandidate
  , checkGenericStaticActuals
  )
import Phil.Core.Static
  ( DeclarationKey
  , InterfaceRevision
  , SemanticForm
  )
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1BareStaticReferenceActual
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1QualifiedName (..)
  , GrammarV1StaticArgument
  , GrammarV1StaticReference (..)
  )

-- | Exact semantic evidence for one source static argument whose meaning is not
-- a bare name-shaped reference. The source argument is repeated deliberately so
-- this boundary can verify correspondence rather than accepting a positional
-- semantic form detached from the syntax that produced it. The semantic form is
-- supplied by the competent kind-specific checker; this bridge does not serialize
-- Grammar-v1 syntax into semantic identity.
data GrammarV1ResolvedDirectStaticArgument = GrammarV1ResolvedDirectStaticArgument
  { resolvedDirectStaticSourceArgument :: GrammarV1StaticArgument
  , resolvedDirectStaticKind :: GenericStaticKind
  , resolvedDirectStaticSemanticForm :: SemanticForm
  }
  deriving (Eq, Show)

-- | One exact specialized source reference after Core has checked all static
-- actual kinds and derived the generic application identity from stable target
-- declaration/interface identity plus checked semantic arguments.
data GrammarV1CheckedSpecializedStaticReference =
  GrammarV1CheckedSpecializedStaticReference
    { checkedSpecializedStaticReferenceName :: Text
    , checkedSpecializedStaticArguments :: [CheckedGenericStaticActual]
    , checkedSpecializedStaticApplicationIdentity :: GenericApplicationIdentity
    }
  deriving (Eq, Show)

data GrammarV1SpecializedStaticReferenceError
  = GrammarV1MissingDirectStaticArgumentEvidence GrammarV1StaticArgument
  | GrammarV1DuplicateDirectStaticArgumentEvidence GrammarV1StaticArgument
  | GrammarV1UnexpectedDirectEvidenceForBareReference GrammarV1StaticArgument
  | GrammarV1SpecializedStaticKindError GenericStaticKindError
  | GrammarV1SpecializedApplicationIdentityError GenericApplicationIdentityError
  deriving (Eq, Show)

-- | Check one specialized Grammar-v1 static reference without letting source
-- spelling manufacture semantic arguments or target identity.
--
-- Bare name-shaped arguments stay unresolved references and are interpreted only
-- under the declaration-supplied parameter kind by 'checkGenericStaticActuals'.
-- Every other source argument requires exactly one caller-supplied semantic form
-- tied to that exact source argument; nested specializations therefore require
-- prior competent elaboration rather than being flattened into text. Stable
-- DeclarationKey/InterfaceRevision and the target parameter schema are supplied
-- by the declaration-resolution layer. Core then owns exact kind checking and
-- GenericApplicationIdentity construction.
--
-- Bare target references are outside this function because their existing
-- unresolved-reference bridge remains authoritative. This function also does not
-- discharge generic requirements, select implementations, construct occurrences,
-- or infer structural modes from semantic-form spelling.
grammarV1CheckedSpecializedStaticReference
  :: DeclarationKey
  -> InterfaceRevision
  -> [GenericStaticParameter]
  -> [GrammarV1ResolvedDirectStaticArgument]
  -> [GenericStaticReferenceCandidate]
  -> GrammarV1StaticReference
  -> Maybe
      (Either
        GrammarV1SpecializedStaticReferenceError
        GrammarV1CheckedSpecializedStaticReference)
grammarV1CheckedSpecializedStaticReference
    declarationKey interfaceRevision parameters directEvidence references source
  | null sourceArguments = Nothing
  | otherwise = do
      sourceName <- qualifiedNameText (grammarV1StaticReferenceName source)
      pure $ do
        actuals <- mapM sourceActual sourceArguments
        checked <- mapLeft GrammarV1SpecializedStaticKindError
          (checkGenericStaticActuals parameters actuals references)
        identity <- mapLeft GrammarV1SpecializedApplicationIdentityError
          (deriveGenericApplicationIdentity
            declarationKey
            interfaceRevision
            [ (checkedGenericStaticParameterKey actual, checkedGenericStaticSemanticForm actual)
            | actual <- checked
            ])
        Right GrammarV1CheckedSpecializedStaticReference
          { checkedSpecializedStaticReferenceName = sourceName
          , checkedSpecializedStaticArguments = checked
          , checkedSpecializedStaticApplicationIdentity = identity
          }
  where
    sourceArguments = grammarV1StaticReferenceArguments source

    sourceActual argument =
      case grammarV1BareStaticReferenceActual argument of
        Just bareReference ->
          case matchingDirectEvidence argument of
            [] -> Right bareReference
            _ -> Left (GrammarV1UnexpectedDirectEvidenceForBareReference argument)
        Nothing ->
          case matchingDirectEvidence argument of
            [] -> Left (GrammarV1MissingDirectStaticArgumentEvidence argument)
            [resolved] -> Right
              (DirectGenericStaticActual
                (resolvedDirectStaticKind resolved)
                (resolvedDirectStaticSemanticForm resolved))
            _ -> Left (GrammarV1DuplicateDirectStaticArgumentEvidence argument)

    matchingDirectEvidence argument =
      [ resolved
      | resolved <- directEvidence
      , resolvedDirectStaticSourceArgument resolved == argument
      ]

qualifiedNameText :: GrammarV1QualifiedName -> Maybe Text
qualifiedNameText source =
  case grammarV1QualifiedNameParts source of
    [] -> Nothing
    parts -> Just (Text.intercalate (Text.singleton '.') parts)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
