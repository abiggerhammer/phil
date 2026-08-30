{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-002 Frame and Validated types preserve exact payloads" frameValidatedPreserved
    , test "SURF-002 static arithmetic preserves precedence and associativity" staticArithmeticPreserved
    , test "SURF-002 static postfix and parenthesized values stay distinct from tuple types" staticPostfixAndParenthesesPreserved
    , test "SURF-002 primitive static value leaves preserve canonical argument forms" staticLeavesPreserved
    , test "SURF-002 brace-led static actuals distinguish effect sets from refinements" braceStaticActualsPreserved
    , test "SURF-003 static additive expression requires a right operand" $
        expectReject "type Bad = Box[1 +];"
    , test "SURF-003 Validated requires both term expressions" $
        expectReject "type Bad = Validated[Check, payload];"
    , test "SURF-003 Frame admits a static reference, not a term call" $
        expectReject "type Bad = Frame[Codec(x)];"
    , test "SURF-003 effect-set static actual rejects a trailing comma" $
        expectReject "type Bad = Box[{IO,}];"
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

frameValidatedPreserved :: Either String ()
frameValidatedPreserved = do
  aliases <- parseAliases $ Text.unlines
    [ "type Framed = Frame[Wire.Codec[U32]];"
    , "type Checked = Validated[Check[U32], payload, evidence];"
    ]
  case aliases of
    [framed, checked] -> do
      case locatedValue (grammarV1TypeAliasTarget framed) of
        GrammarV1FrameType reference ->
          assertReferenceWithU32 "Wire.Codec" reference
        other -> Left ("expected Frame type, got " <> show other)
      case locatedValue (grammarV1TypeAliasTarget checked) of
        GrammarV1ValidatedType validator input evidence -> do
          assertReferenceWithU32 "Check" validator
          assertSimpleTermName "payload" input
          assertSimpleTermName "evidence" evidence
        other -> Left ("expected Validated type, got " <> show other)
    values -> Left ("expected two aliases, got " <> show (length values))

staticArithmeticPreserved :: Either String ()
staticArithmeticPreserved = do
  arguments <- namedAliasArguments "type Arithmetic = Box[1 + 2 * 3 - 4];"
  case arguments of
    [GrammarV1StaticValueArgument expression] ->
      case locatedValue expression of
        GrammarV1StaticValueBinary addSide subtractOperator four -> do
          assertStaticOperator GrammarV1StaticSubtract subtractOperator
          assertStaticInteger "4" four
          case locatedValue addSide of
            GrammarV1StaticValueBinary one addOperator multiplySide -> do
              assertStaticOperator GrammarV1StaticAdd addOperator
              assertStaticInteger "1" one
              case locatedValue multiplySide of
                GrammarV1StaticValueBinary two multiplyOperator three -> do
                  assertStaticOperator GrammarV1StaticMultiply multiplyOperator
                  assertStaticInteger "2" two
                  assertStaticInteger "3" three
                other -> Left ("expected 2 * 3, got " <> show other)
            other -> Left ("expected 1 + (2 * 3), got " <> show other)
        other -> Left ("expected top-level subtraction, got " <> show other)
    other -> Left ("expected one compound static value argument, got " <> show other)

staticPostfixAndParenthesesPreserved :: Either String ()
staticPostfixAndParenthesesPreserved = do
  aliases <- parseAliases $ Text.unlines
    [ "type Projected = Box[Cfg[N].field.more];"
    , "type Parenthesized = Pair[(1 + 2) * 3, (U32, Bool)];"
    ]
  case aliases of
    [projected, parenthesized] -> do
      projectedArgs <- namedTypeArguments projected
      case projectedArgs of
        [GrammarV1StaticValueArgument expression] ->
          assertProjectionChain expression
        other -> Left ("unexpected projected static arguments " <> show other)
      parenthesizedArgs <- namedTypeArguments parenthesized
      case parenthesizedArgs of
        [GrammarV1StaticValueArgument expression, GrammarV1StaticTypeArgument tupleType] -> do
          case locatedValue expression of
            GrammarV1StaticValueBinary grouped multiplyOperator three -> do
              assertStaticOperator GrammarV1StaticMultiply multiplyOperator
              assertStaticInteger "3" three
              case locatedValue grouped of
                GrammarV1StaticValueParenthesized inner ->
                  case locatedValue inner of
                    GrammarV1StaticValueBinary one addOperator two -> do
                      assertStaticOperator GrammarV1StaticAdd addOperator
                      assertStaticInteger "1" one
                      assertStaticInteger "2" two
                    other -> Left ("expected parenthesized 1 + 2, got " <> show other)
                other -> Left ("expected explicit parenthesized static value, got " <> show other)
            other -> Left ("expected (1 + 2) * 3, got " <> show other)
          case tupleType of
            GrammarV1TupleType [Located _ left, Located _ right] -> do
              assert (left == GrammarV1UnsignedType "U32") "tuple static type left side was not U32"
              assert (right == GrammarV1BoolType) "tuple static type right side was not Bool"
            other -> Left ("expected tuple type static argument, got " <> show other)
        other -> Left ("unexpected parenthesized static arguments " <> show other)
    values -> Left ("expected two aliases, got " <> show (length values))

staticLeavesPreserved :: Either String ()
staticLeavesPreserved = do
  arguments <- namedAliasArguments "type Leaves = Box[unit, true, false, 7];"
  assert
    (arguments ==
      [ GrammarV1StaticUnitArgument
      , GrammarV1StaticBoolArgument True
      , GrammarV1StaticBoolArgument False
      , GrammarV1StaticIntegerArgument "7"
      ])
    ("unexpected primitive static arguments " <> show arguments)

braceStaticActualsPreserved :: Either String ()
braceStaticActualsPreserved = do
  aliases <- parseAliases $ Text.unlines
    [ "type EffectActual = Box[{IO, Audit(x)}];"
    , "type RefinedActual = Box[{v : U32 | v > 0}];"
    ]
  case aliases of
    [effectActual, refinedActual] -> do
      effectArgs <- namedTypeArguments effectActual
      case effectArgs of
        [GrammarV1StaticEffectSetArgument (Located _ effectSet)] ->
          case effectSet of
            GrammarV1EffectSetLiteral [Located _ io, Located _ audit] -> do
              assertStaticReferenceName "IO" (grammarV1EffectReference io)
              assert (null (grammarV1EffectArguments io)) "IO effect unexpectedly had term arguments"
              assertStaticReferenceName "Audit" (grammarV1EffectReference audit)
              case grammarV1EffectArguments audit of
                [argument] -> assertSimpleTermName "x" argument
                arguments -> Left ("expected Audit(x), got " <> show arguments)
            other -> Left ("expected two-effect literal, got " <> show other)
        other -> Left ("expected effect-set static argument, got " <> show other)
      refinedArgs <- namedTypeArguments refinedActual
      case refinedArgs of
        [GrammarV1StaticTypeArgument (GrammarV1RefinementType binder baseType predicate)] -> do
          assert (locatedValue binder == "v") "refinement binder was not v"
          assert (locatedValue baseType == GrammarV1UnsignedType "U32") "refinement base type was not U32"
          case locatedValue predicate of
            GrammarV1RelationProposition left operator right -> do
              assertSimpleTermName "v" left
              assert (locatedValue operator == GrammarV1GreaterRelation) "refinement operator was not >"
              case locatedValue right of
                GrammarV1IntegerExpression "0" -> Right ()
                other -> Left ("expected refinement RHS 0, got " <> show other)
            other -> Left ("expected refinement relation, got " <> show other)
        other -> Left ("expected refinement type static argument, got " <> show other)
    values -> Left ("expected two aliases, got " <> show (length values))

assertProjectionChain :: Located GrammarV1StaticValueExpression -> Either String ()
assertProjectionChain expression =
  case locatedValue expression of
    GrammarV1StaticValueProjection beforeMore more -> do
      assert (locatedValue more == "more") "outer projection was not .more"
      case locatedValue beforeMore of
        GrammarV1StaticValueProjection base field -> do
          assert (locatedValue field == "field") "inner projection was not .field"
          case locatedValue base of
            GrammarV1StaticValueReference reference -> do
              assertStaticReferenceName "Cfg" reference
              case grammarV1StaticReferenceArguments (locatedValue reference) of
                [GrammarV1StaticReferenceArgument nested] ->
                  assert
                    (grammarV1QualifiedNameParts (grammarV1StaticReferenceName nested) == ["N"])
                    "Cfg static argument was not N"
                other -> Left ("unexpected Cfg static arguments " <> show other)
            other -> Left ("expected Cfg[N] static reference, got " <> show other)
        other -> Left ("expected .field projection, got " <> show other)
    other -> Left ("expected projection chain, got " <> show other)

assertStaticOperator
  :: GrammarV1StaticValueOperator
  -> Located GrammarV1StaticValueOperator
  -> Either String ()
assertStaticOperator expected actual =
  assert (locatedValue actual == expected) ("unexpected static operator " <> show (locatedValue actual))

assertStaticInteger :: Text.Text -> Located GrammarV1StaticValueExpression -> Either String ()
assertStaticInteger expected expression =
  case locatedValue expression of
    GrammarV1StaticValueInteger actual ->
      assert (actual == expected) ("expected static integer " <> Text.unpack expected <> ", got " <> Text.unpack actual)
    other -> Left ("expected static integer, got " <> show other)

assertReferenceWithU32 :: Text.Text -> Located GrammarV1StaticReference -> Either String ()
assertReferenceWithU32 expected reference = do
  assertStaticReferenceName expected reference
  assert
    (grammarV1StaticReferenceArguments (locatedValue reference) ==
      [GrammarV1StaticTypeArgument (GrammarV1UnsignedType "U32")])
    ("expected U32 static argument on " <> Text.unpack expected)

assertStaticReferenceName :: Text.Text -> Located GrammarV1StaticReference -> Either String ()
assertStaticReferenceName expected reference =
  assert
    (Text.intercalate "." (grammarV1QualifiedNameParts (grammarV1StaticReferenceName (locatedValue reference))) == expected)
    ("expected static reference " <> Text.unpack expected <> ", got " <> show (locatedValue reference))

assertSimpleTermName :: Text.Text -> Located GrammarV1Expression -> Either String ()
assertSimpleTermName expected expression =
  case locatedValue expression of
    GrammarV1NameExpression reference arguments -> do
      assert
        (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expected])
        ("expected term name " <> Text.unpack expected)
      assert (null (grammarV1StaticReferenceArguments reference)) "term name unexpectedly had static arguments"
      assert (null arguments) "term name unexpectedly had term arguments"
    other -> Left ("expected simple term name, got " <> show other)

namedAliasArguments :: Text.Text -> Either String [GrammarV1StaticArgument]
namedAliasArguments source = do
  aliases <- parseAliases source
  case aliases of
    [alias] -> namedTypeArguments alias
    values -> Left ("expected one alias, got " <> show (length values))

namedTypeArguments :: GrammarV1TypeAliasDecl -> Either String [GrammarV1StaticArgument]
namedTypeArguments alias =
  case locatedValue (grammarV1TypeAliasTarget alias) of
    GrammarV1NamedType reference -> Right (grammarV1StaticReferenceArguments reference)
    other -> Left ("expected named alias target, got " <> show other)

parseAliases :: Text.Text -> Either String [GrammarV1TypeAliasDecl]
parseAliases source = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "static-value-types" source
  traverse onlyAlias (grammarV1TopLevelDecls sourceFile)
  where
    onlyAlias (Located _ topLevel) =
      case locatedValue (grammarV1Declaration topLevel) of
        GrammarV1TypeAliasDeclaration alias -> Right alias
        other -> Left ("expected type alias declaration, got " <> show other)

expectReject :: Text.Text -> Either String ()
expectReject source =
  case parseGrammarV1StructuralSource "static-value-types-reject" source of
    Left _ -> Right ()
    Right value -> Left ("expected syntax rejection, parsed " <> show value)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
