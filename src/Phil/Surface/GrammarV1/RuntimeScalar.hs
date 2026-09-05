module Phil.Surface.GrammarV1.RuntimeScalar
  ( GrammarV1RuntimeScalarError (..)
  , grammarV1ContextualUIntLiteral
  ) where

import qualified Data.Text as Text
import qualified Data.Text.Read as TextRead
import Phil.Core.Scalar
  ( ScalarLiteral (..)
  , scalarLiteralInRange
  )
import Phil.Core.Syntax (Ty (TyUInt))
import Phil.Surface.GrammarV1.Elaborate (grammarV1PrimitiveType)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Expression (..)
  , GrammarV1Type
  )

-- | Fail-closed contextual runtime-scalar elaboration errors.  Grammar-v1
-- integer literals are intentionally unsuffixed, so their runtime UInt identity
-- comes only from the competent contextual type judgment.
data GrammarV1RuntimeScalarError
  = GrammarV1RuntimeUIntContextRequired GrammarV1Type
  | GrammarV1RuntimeIntegerLiteralRequired GrammarV1Expression
  | GrammarV1RuntimeIntegerLiteralMalformed Text.Text
  | GrammarV1RuntimeUIntLiteralOutOfRange Int Integer
  deriving (Eq, Show)

-- | Elaborate one unsuffixed Grammar-v1 runtime integer literal under one exact
-- contextual UInt[w] type.  Width parsing is delegated to the canonical
-- Grammar-v1 primitive-type elaborator; mathematical range admission is
-- delegated to the already-certified Core scalar predicate.
--
-- No host/default width, truncation, wraparound, saturation, sign
-- reinterpretation, or target representation participates in this judgment.
grammarV1ContextualUIntLiteral
  :: GrammarV1Type
  -> GrammarV1Expression
  -> Either GrammarV1RuntimeScalarError ScalarLiteral
grammarV1ContextualUIntLiteral contextualType expression = do
  width <- case grammarV1PrimitiveType contextualType of
    Just (TyUInt exactWidth) -> Right exactWidth
    _ -> Left (GrammarV1RuntimeUIntContextRequired contextualType)
  literalText <- case expression of
    GrammarV1IntegerExpression text -> Right text
    _ -> Left (GrammarV1RuntimeIntegerLiteralRequired expression)
  value <- exactDecimal literalText
  let literal = ScalarUIntLiteral width value
  if scalarLiteralInRange literal
    then Right literal
    else Left (GrammarV1RuntimeUIntLiteralOutOfRange width value)

exactDecimal :: Text.Text -> Either GrammarV1RuntimeScalarError Integer
exactDecimal text =
  case TextRead.decimal text :: Either String (Integer, Text.Text) of
    Right (value, rest)
      | Text.null rest -> Right value
    _ -> Left (GrammarV1RuntimeIntegerLiteralMalformed text)
