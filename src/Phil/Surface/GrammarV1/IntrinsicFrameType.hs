module Phil.Surface.GrammarV1.IntrinsicFrameType
  ( grammarV1BareFrameType
  ) where

import qualified Data.Text as Text
import Phil.Core.Syntax (GrammarId (..), Ty (..))
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1QualifiedName (..)
  , GrammarV1StaticReference (..)
  , GrammarV1Type (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Preserve an unspecialized Grammar-v1 Frame[...] reference exactly as the
-- Core GrammarId spelling selected by the source. Qualified name parts are
-- joined without reinterpretation. Specialized grammar references remain
-- fail-closed because Core GrammarId has no carrier for static arguments, so
-- flattening them would erase semantically relevant source information.
grammarV1BareFrameType :: GrammarV1Type -> Maybe Ty
grammarV1BareFrameType sourceType = case sourceType of
  GrammarV1FrameType (Located _ reference)
    | null (grammarV1StaticReferenceArguments reference) ->
        case grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) of
          [] -> Nothing
          parts ->
            Just
              (TyFrame
                (GrammarId
                  (Text.intercalate (Text.singleton '.') parts)))
  _ -> Nothing
