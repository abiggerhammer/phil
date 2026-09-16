{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstStaticValue
  ( GrammarV1ReferenceStaticValueError (..)
  , GrammarV1ReferenceStaticValueOperator (..)
  , GrammarV1ReferenceStaticValue (..)
  , grammarV1ProductionStaticValue
  , grammarV1ReferenceStaticValue
  , grammarV1ProductionTypeAliasStaticValues
  , grammarV1ReferenceTypeAliasStaticValues
  ) where

import Control.Monad (foldM)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Declaration (..)
  , GrammarV1SourceFile (..)
  , GrammarV1StaticArgument (..)
  , GrammarV1StaticReference (..)
  , GrammarV1StaticValueExpression (..)
  , GrammarV1StaticValueOperator (..)
  , GrammarV1TopLevelDecl (..)
  , GrammarV1Type (..)
  , GrammarV1TypeAliasDecl (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstStaticReference
  ( GrammarV1ReferenceStaticReferenceError
  , GrammarV1ReferenceStaticReferenceSpine
  , grammarV1ProductionStaticReferenceSpine
  , grammarV1ReferenceStaticReferenceSpine
  )
import Phil.Surface.GrammarV1.ReferenceAstTopLevel
  ( GrammarV1ReferenceDeclarationTag (..)
  , grammarV1ReferenceDeclarationTag
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( GrammarV1ReferenceParseTree (..)
  )
import Phil.Surface.Syntax (Located (..))

newtype GrammarV1ReferenceStaticValueError =
  GrammarV1ReferenceStaticValueError Text
  deriving (Eq, Show)

data GrammarV1ReferenceStaticValueOperator
  = GrammarV1ReferenceStaticAdd
  | GrammarV1ReferenceStaticSubtract
  | GrammarV1ReferenceStaticMultiply
  deriving (Eq, Ord, Show)

data GrammarV1ReferenceStaticValue
  = GrammarV1ReferenceStaticBool Bool
  | GrammarV1ReferenceStaticUnit
  | GrammarV1ReferenceStaticInteger Text
  | GrammarV1ReferenceStaticReference GrammarV1ReferenceStaticReferenceSpine
  | GrammarV1ReferenceStaticParenthesized GrammarV1ReferenceStaticValue
  | GrammarV1ReferenceStaticProjection GrammarV1ReferenceStaticValue Text
  | GrammarV1ReferenceStaticBinary
      GrammarV1ReferenceStaticValue
      GrammarV1ReferenceStaticValueOperator
      GrammarV1ReferenceStaticValue
  deriving (Eq, Show)

grammarV1ProductionStaticValue
  :: GrammarV1StaticValueExpression
  -> GrammarV1ReferenceStaticValue
grammarV1ProductionStaticValue expression = case expression of
  GrammarV1StaticValueBool value -> GrammarV1ReferenceStaticBool value
  GrammarV1StaticValueUnit -> GrammarV1ReferenceStaticUnit
  GrammarV1StaticValueInteger value -> GrammarV1ReferenceStaticInteger value
  GrammarV1StaticValueReference reference ->
    GrammarV1ReferenceStaticReference
      (grammarV1ProductionStaticReferenceSpine (locatedValue reference))
  GrammarV1StaticValueParenthesized inner ->
    GrammarV1ReferenceStaticParenthesized
      (grammarV1ProductionStaticValue (locatedValue inner))
  GrammarV1StaticValueProjection receiver field ->
    GrammarV1ReferenceStaticProjection
      (grammarV1ProductionStaticValue (locatedValue receiver))
      (locatedValue field)
  GrammarV1StaticValueBinary left operator right ->
    GrammarV1ReferenceStaticBinary
      (grammarV1ProductionStaticValue (locatedValue left))
      (productionOperator (locatedValue operator))
      (grammarV1ProductionStaticValue (locatedValue right))

productionOperator
  :: GrammarV1StaticValueOperator
  -> GrammarV1ReferenceStaticValueOperator
productionOperator operator = case operator of
  GrammarV1StaticAdd -> GrammarV1ReferenceStaticAdd
  GrammarV1StaticSubtract -> GrammarV1ReferenceStaticSubtract
  GrammarV1StaticMultiply -> GrammarV1ReferenceStaticMultiply

grammarV1ReferenceStaticValue
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError GrammarV1ReferenceStaticValue
grammarV1ReferenceStaticValue tree = do
  body <- expectNonterminal "static_value_expression" tree
  additive <- expectNonterminal "static_additive_expression" body
  parseStaticAdditive additive

parseStaticAdditive
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError GrammarV1ReferenceStaticValue
parseStaticAdditive tree = do
  fields <- expectSequence "static_additive_expression" tree
  case fields of
    [firstTree, restTree] -> do
      first <- parseStaticMultiplicative firstTree
      rest <- expectRepetition "static additive suffix" restTree
      foldM applyStaticAdditiveSuffix first rest
    _ -> failStaticValue
      "static_additive_expression body is not a two-item sequence"

applyStaticAdditiveSuffix
  :: GrammarV1ReferenceStaticValue
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError GrammarV1ReferenceStaticValue
applyStaticAdditiveSuffix left tree = do
  fields <- expectSequence "static additive suffix item" tree
  case fields of
    [operatorTree, rightTree] -> do
      operator <- parseStaticAdditiveOperator operatorTree
      right <- parseStaticMultiplicative rightTree
      pure (GrammarV1ReferenceStaticBinary left operator right)
    _ -> failStaticValue "static additive suffix is not a two-item sequence"

parseStaticAdditiveOperator
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError GrammarV1ReferenceStaticValueOperator
parseStaticAdditiveOperator tree = case tree of
  GrammarV1ReferenceAlternative 0 selected -> do
    expectLiteral "+" selected
    pure GrammarV1ReferenceStaticAdd
  GrammarV1ReferenceAlternative 1 selected -> do
    expectLiteral "-" selected
    pure GrammarV1ReferenceStaticSubtract
  GrammarV1ReferenceAlternative index _ ->
    failStaticValue ("static additive operator alternative out of range: " <> showText index)
  _ -> failStaticValue "static additive operator is not an alternative node"

parseStaticMultiplicative
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError GrammarV1ReferenceStaticValue
parseStaticMultiplicative tree = do
  body <- expectNonterminal "static_multiplicative_expression" tree
  fields <- expectSequence "static_multiplicative_expression" body
  case fields of
    [firstTree, restTree] -> do
      first <- parseStaticPostfix firstTree
      rest <- expectRepetition "static multiplicative suffix" restTree
      foldM applyStaticMultiplicativeSuffix first rest
    _ -> failStaticValue
      "static_multiplicative_expression body is not a two-item sequence"

applyStaticMultiplicativeSuffix
  :: GrammarV1ReferenceStaticValue
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError GrammarV1ReferenceStaticValue
applyStaticMultiplicativeSuffix left tree = do
  fields <- expectSequence "static multiplicative suffix item" tree
  case fields of
    [operatorTree, rightTree] -> do
      expectLiteral "*" operatorTree
      right <- parseStaticPostfix rightTree
      pure
        (GrammarV1ReferenceStaticBinary
          left
          GrammarV1ReferenceStaticMultiply
          right)
    _ -> failStaticValue
      "static multiplicative suffix is not a two-item sequence"

parseStaticPostfix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError GrammarV1ReferenceStaticValue
parseStaticPostfix tree = do
  body <- expectNonterminal "static_postfix_expression" tree
  case body of
    GrammarV1ReferenceAlternative 0 selected -> parseNamedStaticPostfix selected
    GrammarV1ReferenceAlternative 1 selected -> parsePrimaryStaticPostfix selected
    GrammarV1ReferenceAlternative index _ ->
      failStaticValue ("static_postfix_expression alternative out of range: " <> showText index)
    _ -> failStaticValue "static_postfix_expression body is not an alternative node"

parseNamedStaticPostfix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError GrammarV1ReferenceStaticValue
parseNamedStaticPostfix tree = do
  fields <- expectSequence "named static postfix" tree
  case fields of
    [nameTree, optionalTail] -> do
      case optionalTail of
        GrammarV1ReferenceOptionalNone -> do
          reference <- mapStaticReferenceError
            (grammarV1ReferenceStaticReferenceSpine
              (GrammarV1ReferenceNonterminal
                "static_reference"
                (GrammarV1ReferenceSequence
                  [nameTree, GrammarV1ReferenceOptionalNone])))
          pure (GrammarV1ReferenceStaticReference reference)
        GrammarV1ReferenceOptionalSome tailTree -> do
          tailFields <- expectSequence "named static postfix tail" tailTree
          case tailFields of
            [argumentsTree, projectionsTree] -> do
              reference <- mapStaticReferenceError
                (grammarV1ReferenceStaticReferenceSpine
                  (GrammarV1ReferenceNonterminal
                    "static_reference"
                    (GrammarV1ReferenceSequence
                      [ nameTree
                      , GrammarV1ReferenceOptionalSome argumentsTree
                      ])))
              projections <- expectRepetition
                "named static postfix projections"
                projectionsTree
              foldM applyProjection
                (GrammarV1ReferenceStaticReference reference)
                projections
            _ -> failStaticValue
              "named static postfix tail is not a two-item sequence"
        _ -> failStaticValue "named static postfix tail is not optional"
    _ -> failStaticValue "named static postfix is not a two-item sequence"

parsePrimaryStaticPostfix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError GrammarV1ReferenceStaticValue
parsePrimaryStaticPostfix tree = do
  fields <- expectSequence "primary static postfix" tree
  case fields of
    [primaryTree, projectionsTree] -> do
      primary <- parseStaticPrimary primaryTree
      projections <- expectRepetition
        "primary static postfix projections"
        projectionsTree
      foldM applyProjection primary projections
    _ -> failStaticValue "primary static postfix is not a two-item sequence"

applyProjection
  :: GrammarV1ReferenceStaticValue
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError GrammarV1ReferenceStaticValue
applyProjection receiver tree = do
  fields <- expectSequence "static projection suffix" tree
  case fields of
    [dot, identifierTree] -> do
      expectLiteral "." dot
      field <- parseIdentifier identifierTree
      pure (GrammarV1ReferenceStaticProjection receiver field)
    _ -> failStaticValue "static projection suffix is not a two-item sequence"

parseStaticPrimary
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError GrammarV1ReferenceStaticValue
parseStaticPrimary tree = do
  body <- expectNonterminal "static_nonreference_primary_expression" tree
  case body of
    GrammarV1ReferenceAlternative 0 selected ->
      expectLiteral "true" selected >> pure (GrammarV1ReferenceStaticBool True)
    GrammarV1ReferenceAlternative 1 selected ->
      expectLiteral "false" selected >> pure (GrammarV1ReferenceStaticBool False)
    GrammarV1ReferenceAlternative 2 selected ->
      expectLiteral "unit" selected >> pure GrammarV1ReferenceStaticUnit
    GrammarV1ReferenceAlternative 3 selected ->
      GrammarV1ReferenceStaticInteger <$> parseIntegerLiteral selected
    GrammarV1ReferenceAlternative 4 selected -> do
      fields <- expectSequence "parenthesized static value" selected
      case fields of
        [openParen, innerTree, closeParen] -> do
          expectLiteral "(" openParen
          inner <- grammarV1ReferenceStaticValue innerTree
          expectLiteral ")" closeParen
          pure (GrammarV1ReferenceStaticParenthesized inner)
        _ -> failStaticValue
          "parenthesized static value is not a three-item sequence"
    GrammarV1ReferenceAlternative index _ ->
      failStaticValue ("static primary alternative out of range: " <> showText index)
    _ -> failStaticValue "static primary body is not an alternative node"

parseIntegerLiteral
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError Text
parseIntegerLiteral tree = do
  body <- expectNonterminal "integer_literal" tree
  case body of
    GrammarV1ReferenceLexical "DECIMAL_INTEGER" value -> Right value
    GrammarV1ReferenceLexical className _ ->
      failStaticValue ("integer_literal uses lexical class " <> className)
    _ -> failStaticValue "integer_literal body is not a DECIMAL_INTEGER lexical leaf"

parseIdentifier
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError Text
parseIdentifier tree = do
  body <- expectNonterminal "identifier" tree
  case body of
    GrammarV1ReferenceLexical "IDENTIFIER" value -> Right value
    GrammarV1ReferenceLexical className _ ->
      failStaticValue ("identifier uses lexical class " <> className)
    _ -> failStaticValue "identifier body is not an IDENTIFIER lexical leaf"

grammarV1ProductionTypeAliasStaticValues
  :: GrammarV1SourceFile
  -> [[GrammarV1ReferenceStaticValue]]
grammarV1ProductionTypeAliasStaticValues sourceFile =
  [ productionTargetValues (locatedValue (grammarV1TypeAliasTarget alias))
  | locatedTopLevel <- grammarV1TopLevelDecls sourceFile
  , let topLevel = locatedValue locatedTopLevel
  , GrammarV1TypeAliasDeclaration alias <-
      [locatedValue (grammarV1Declaration topLevel)]
  ]
  where
    productionTargetValues sourceType = case sourceType of
      GrammarV1NamedType reference -> productionReferenceValues reference
      GrammarV1FrameType reference -> productionReferenceValues (locatedValue reference)
      GrammarV1ValidatedType reference _ _ ->
        productionReferenceValues (locatedValue reference)
      _ -> []

productionReferenceValues
  :: GrammarV1StaticReference
  -> [GrammarV1ReferenceStaticValue]
productionReferenceValues reference =
  [ value
  | argument <- grammarV1StaticReferenceArguments reference
  , value <- case argument of
      GrammarV1StaticReferenceArgument nested ->
        [GrammarV1ReferenceStaticReference
          (grammarV1ProductionStaticReferenceSpine nested)]
      GrammarV1StaticBoolArgument boolean ->
        [GrammarV1ReferenceStaticBool boolean]
      GrammarV1StaticUnitArgument -> [GrammarV1ReferenceStaticUnit]
      GrammarV1StaticIntegerArgument integer ->
        [GrammarV1ReferenceStaticInteger integer]
      GrammarV1StaticValueArgument expression ->
        [grammarV1ProductionStaticValue (locatedValue expression)]
      _ -> []
  ]

grammarV1ReferenceTypeAliasStaticValues
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError [[GrammarV1ReferenceStaticValue]]
grammarV1ReferenceTypeAliasStaticValues tree = do
  sourceBody <- expectNonterminal "source_file" tree
  sourceFields <- expectSequence "source_file" sourceBody
  case sourceFields of
    [_moduleTree, _importTree, topLevelTree] -> do
      topLevels <- expectRepetition "source_file top levels" topLevelTree
      values <- traverse parseTopLevelTypeAliasValues topLevels
      pure [value | Just value <- values]
    _ -> failStaticValue "source_file body is not a three-item sequence"

parseTopLevelTypeAliasValues
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError (Maybe [GrammarV1ReferenceStaticValue])
parseTopLevelTypeAliasValues tree = do
  topLevelBody <- expectNonterminal "top_level_decl" tree
  fields <- expectSequence "top_level_decl" topLevelBody
  case fields of
    [_attributes, declarationTree] -> do
      tag <- mapTopLevelError (grammarV1ReferenceDeclarationTag declarationTree)
      case tag of
        GrammarV1ReferenceTypeAliasDeclaration -> do
          declarationBody <- expectNonterminal "declaration" declarationTree
          case declarationBody of
            GrammarV1ReferenceAlternative 2 selected ->
              Just <$> parseTypeAliasTargetValues selected
            _ -> failStaticValue
              "type-alias declaration does not occupy alternative 2"
        _ -> Right Nothing
    _ -> failStaticValue "top_level_decl body is not a two-item sequence"

parseTypeAliasTargetValues
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError [GrammarV1ReferenceStaticValue]
parseTypeAliasTargetValues tree = do
  body <- expectNonterminal "type_alias_decl" tree
  fields <- expectSequence "type_alias_decl" body
  case fields of
    [_keyword, _name, _generic, _requirements, _equals, targetTree, _terminator] ->
      parseTargetRootValues targetTree
    _ -> failStaticValue "type_alias_decl body is not a seven-item sequence"

parseTargetRootValues
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError [GrammarV1ReferenceStaticValue]
parseTargetRootValues tree = do
  body <- expectNonterminal "type_expression" tree
  case body of
    GrammarV1ReferenceAlternative 1 namedTree -> do
      namedBody <- expectNonterminal "named_type" namedTree
      parseReferenceValueArguments namedBody
    GrammarV1ReferenceAlternative 0 nonreferenceTree -> do
      nonreferenceBody <- expectNonterminal "nonreference_type_expression" nonreferenceTree
      case nonreferenceBody of
        GrammarV1ReferenceAlternative 8 selected ->
          bracketedReferenceValues "Frame" selected
        GrammarV1ReferenceAlternative 10 selected ->
          validatedReferenceValues selected
        GrammarV1ReferenceAlternative _ _ -> Right []
        _ -> failStaticValue
          "nonreference_type_expression body is not an alternative node"
    GrammarV1ReferenceAlternative index _ ->
      failStaticValue ("type_expression alternative out of range: " <> showText index)
    _ -> failStaticValue "type_expression body is not an alternative node"

bracketedReferenceValues
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError [GrammarV1ReferenceStaticValue]
bracketedReferenceValues keyword tree = do
  fields <- expectSequence (keyword <> " type") tree
  case fields of
    [keywordTree, openBracket, referenceTree, closeBracket] -> do
      expectLiteral keyword keywordTree
      expectLiteral "[" openBracket
      values <- parseReferenceValueArguments referenceTree
      expectLiteral "]" closeBracket
      pure values
    _ -> failStaticValue (keyword <> " type body is not a four-item sequence")

validatedReferenceValues
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError [GrammarV1ReferenceStaticValue]
validatedReferenceValues tree = do
  fields <- expectSequence "Validated type" tree
  case fields of
    [ keywordTree
      , openBracket
      , referenceTree
      , firstComma
      , firstExpression
      , secondComma
      , secondExpression
      , closeBracket
      ] -> do
        expectLiteral "Validated" keywordTree
        expectLiteral "[" openBracket
        values <- parseReferenceValueArguments referenceTree
        expectLiteral "," firstComma
        expectNamedNode "expression" firstExpression
        expectLiteral "," secondComma
        expectNamedNode "expression" secondExpression
        expectLiteral "]" closeBracket
        pure values
    _ -> failStaticValue "Validated type body is not an eight-item sequence"

parseReferenceValueArguments
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError [GrammarV1ReferenceStaticValue]
parseReferenceValueArguments tree = do
  body <- expectNonterminal "static_reference" tree
  fields <- expectSequence "static_reference" body
  case fields of
    [_nameTree, GrammarV1ReferenceOptionalNone] -> Right []
    [_nameTree, GrammarV1ReferenceOptionalSome argumentsTree] ->
      parseStaticArgumentsForValues argumentsTree
    [_nameTree, _] -> failStaticValue "static_reference argument slot is not optional"
    _ -> failStaticValue "static_reference body is not a two-item sequence"

parseStaticArgumentsForValues
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError [GrammarV1ReferenceStaticValue]
parseStaticArgumentsForValues tree = do
  body <- expectNonterminal "static_arguments" tree
  fields <- expectSequence "static_arguments" body
  case fields of
    [openBracket, optionalItems, closeBracket] -> do
      expectLiteral "[" openBracket
      values <- case optionalItems of
        GrammarV1ReferenceOptionalNone -> Right []
        GrammarV1ReferenceOptionalSome itemTree -> do
          itemFields <- expectSequence "static_arguments items" itemTree
          case itemFields of
            [firstTree, restTree] -> do
              first <- parseStaticArgumentValue firstTree
              restItems <- expectRepetition "static_arguments suffix" restTree
              rest <- traverse parseStaticArgumentValueSuffix restItems
              pure (maybeToList first <> concatMap maybeToList rest)
            _ -> failStaticValue
              "static_arguments item body is not a two-item sequence"
        _ -> failStaticValue "static_arguments items slot is not optional"
      expectLiteral "]" closeBracket
      pure values
    _ -> failStaticValue "static_arguments body is not a three-item sequence"

parseStaticArgumentValueSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError (Maybe GrammarV1ReferenceStaticValue)
parseStaticArgumentValueSuffix tree = do
  fields <- expectSequence "static_arguments suffix item" tree
  case fields of
    [comma, argumentTree] -> do
      expectLiteral "," comma
      parseStaticArgumentValue argumentTree
    _ -> failStaticValue "static_arguments suffix item is not a two-item sequence"

parseStaticArgumentValue
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError (Maybe GrammarV1ReferenceStaticValue)
parseStaticArgumentValue tree = do
  body <- expectNonterminal "static_argument" tree
  case body of
    GrammarV1ReferenceAlternative 2 selected ->
      Just <$> grammarV1ReferenceStaticValue selected
    GrammarV1ReferenceAlternative index _
      | index >= 0 && index <= 3 -> Right Nothing
      | otherwise -> failStaticValue
          ("static_argument alternative out of range: " <> showText index)
    _ -> failStaticValue "static_argument body is not an alternative node"

maybeToList :: Maybe a -> [a]
maybeToList value = case value of
  Nothing -> []
  Just item -> [item]

expectNamedNode
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError ()
expectNamedNode name tree = expectNonterminal name tree >> pure ()

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> Right body
    | otherwise -> failStaticValue
        ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failStaticValue ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence items -> Right items
  _ -> failStaticValue (label <> " is not a sequence node")

expectRepetition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError [GrammarV1ReferenceParseTree]
expectRepetition label tree = case tree of
  GrammarV1ReferenceRepetition items -> Right items
  _ -> failStaticValue (label <> " is not a repetition node")

expectLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticValueError ()
expectLiteral expected tree = case tree of
  GrammarV1ReferenceLiteral actual
    | actual == expected -> Right ()
    | otherwise -> failStaticValue
        ("expected literal " <> expected <> ", got " <> actual)
  _ -> failStaticValue ("expected literal " <> expected)

mapStaticReferenceError
  :: Either GrammarV1ReferenceStaticReferenceError a
  -> Either GrammarV1ReferenceStaticValueError a
mapStaticReferenceError =
  mapLeft (GrammarV1ReferenceStaticValueError . Text.pack . show)

mapTopLevelError
  :: Show e
  => Either e a
  -> Either GrammarV1ReferenceStaticValueError a
mapTopLevelError = mapLeft (GrammarV1ReferenceStaticValueError . Text.pack . show)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value

showText :: Show a => a -> Text
showText = Text.pack . show

failStaticValue
  :: Text
  -> Either GrammarV1ReferenceStaticValueError a
failStaticValue = Left . GrammarV1ReferenceStaticValueError
