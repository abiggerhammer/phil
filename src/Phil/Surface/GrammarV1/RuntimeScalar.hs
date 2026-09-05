module Phil.Surface.GrammarV1.RuntimeScalar
  ( GrammarV1RuntimeScalarError (..)
  , grammarV1ContextualUIntLiteral
  , grammarV1ContextualSIntLiteral
  ) where

import qualified Data.Text as Text
import qualified Data.Text.Read as TextRead
import Phil.Core.Scalar
  ( ScalarLiteral (..)
  , scalarLiteralInRange
  )
import Phil.Core.Syntax (Ty (..))
import Phil.Surface.GrammarV1.Elaborate (grammarV1PrimitiveType)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Expression (..)
  , GrammarV1Type
  )

-- | Fail-closed contextual runtime-scalar elaboration errors. Grammar-v1 integer
-- literals are intentionally unsuffixed; width and signedness come only from the
-- competent contextual type judgment.
data GrammarV1RuntimeScalarError
  = GrammarV1RuntimeUIntContextRequired GrammarV1Type
  | GrammarV1RuntimeSIntContextRequired GrammarV1Type
  | GrammarV1RuntimeIntegerLiteralRequired GrammarV1Expression
  | GrammarV1RuntimeIntegerLiteralMalformed Text.Text
  | GrammarV1RuntimeUIntLiteralOutOfRange Int Integer
  | GrammarV1RuntimeSIntLiteralOutOfRange Int Integer
  deriving (Eq, Show)

-- | Elaborate one unsuffixed Grammar-v1 integer literal under an exact UInt[w]
-- context. Signed source literals cannot be reinterpreted as unsigned values.
grammarV1ContextualUIntLiteral
  :: GrammarV1Type
  -> GrammarV1Expression
  -> Either GrammarV1RuntimeScalarError ScalarLiteral
grammarV1ContextualUIntLiteral contextualType expression = do
  width <- case grammarV1PrimitiveType contextualType of
    Just (TyUInt exactWidth) -> Right exactWidth
    _ -> Left (GrammarV1RuntimeUIntContextRequired contextualType)
  literalText <- integerLiteralText expression
  value <- exactUnsignedDecimal literalText
  let literal = ScalarUIntLiteral width value
  if scalarLiteralInRange literal
    then Right literal
    else Left (GrammarV1RuntimeUIntLiteralOutOfRange width value)

-- | Elaborate one unsuffixed Grammar-v1 integer literal under an exact I[w]
-- context. The negative sign is source-semantic data, not a target signedness
-- reinterpretation. Range admission is the exact mathematical interval
-- [-2^(w-1), 2^(w-1)-1].
grammarV1ContextualSIntLiteral
  :: GrammarV1Type
  -> GrammarV1Expression
  -> Either GrammarV1RuntimeScalarError ScalarLiteral
grammarV1ContextualSIntLiteral contextualType expression = do
  width <- case grammarV1PrimitiveType contextualType of
    Just (TySInt exactWidth) -> Right exactWidth
    _ -> Left (GrammarV1RuntimeSIntContextRequired contextualType)
  literalText <- integerLiteralText expression
  value <- exactSignedDecimal literalText
  let literal = ScalarSIntLiteral width value
  if scalarLiteralInRange literal
    then Right literal
    else Left (GrammarV1RuntimeSIntLiteralOutOfRange width value)

integerLiteralText
  :: GrammarV1Expression
  -> Either GrammarV1RuntimeScalarError Text.Text
integerLiteralText expression = case expression of
  GrammarV1IntegerExpression text -> Right text
  _ -> Left (GrammarV1RuntimeIntegerLiteralRequired expression)

exactUnsignedDecimal :: Text.Text -> Either GrammarV1RuntimeScalarError Integer
exactUnsignedDecimal text =
  case TextRead.decimal text :: Either String (Integer, Text.Text) of
    Right (value, rest)
      | Text.null rest -> Right value
    _ -> Left (GrammarV1RuntimeIntegerLiteralMalformed text)

exactSignedDecimal :: Text.Text -> Either GrammarV1RuntimeScalarError Integer
exactSignedDecimal text = case Text.stripPrefix (Text.singleton '-') text of
  Just digits
    | Text.null digits -> Left (GrammarV1RuntimeIntegerLiteralMalformed text)
    | otherwise -> negate <$> exactUnsignedDecimal digits
  Nothing -> exactUnsignedDecimal text
