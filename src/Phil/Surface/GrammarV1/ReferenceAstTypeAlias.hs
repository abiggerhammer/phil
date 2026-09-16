{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstTypeAlias
  ( GrammarV1ReferenceTypeAliasError (..)
  , GrammarV1ReferenceTypeAliasSpine (..)
  , GrammarV1ReferenceTypeTag (..)
  , grammarV1ProductionTypeAliasSpines
  , grammarV1ProductionTypeTag
  , grammarV1ReferenceTypeAliasSpines
  , grammarV1ReferenceTypeTag
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Declaration (..)
  , GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..)
  , GrammarV1Type (..)
  , GrammarV1TypeAliasDecl (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstTopLevel
  ( GrammarV1ReferenceDeclarationTag (..)
  , grammarV1ReferenceDeclarationTag
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( GrammarV1ReferenceParseTree (..)
  )
import Phil.Surface.Syntax (Located (..))

newtype GrammarV1ReferenceTypeAliasError = GrammarV1ReferenceTypeAliasError Text
  deriving (Eq, Show)

data GrammarV1ReferenceTypeTag
  = GrammarV1ReferenceUnitType
  | GrammarV1ReferenceBoolType
  | GrammarV1ReferencePrimitiveSpelling Text
  | GrammarV1ReferenceBytesType
  | GrammarV1ReferenceFrameType
  | GrammarV1ReferenceProofType
  | GrammarV1ReferenceValidatedType
  | GrammarV1ReferenceRefinementType
  | GrammarV1ReferenceTupleType
  | GrammarV1ReferenceNamedType
  deriving (Eq, Ord, Show)

data GrammarV1ReferenceTypeAliasSpine = GrammarV1ReferenceTypeAliasSpine
  { grammarV1ReferenceTypeAliasName :: Text
  , grammarV1ReferenceTypeAliasGenericParamCount :: Int
  , grammarV1ReferenceTypeAliasRequirementCount :: Int
  , grammarV1ReferenceTypeAliasTargetTag :: GrammarV1ReferenceTypeTag
  }
  deriving (Eq, Show)

grammarV1ProductionTypeAliasSpines
  :: GrammarV1SourceFile
  -> [GrammarV1ReferenceTypeAliasSpine]
grammarV1ProductionTypeAliasSpines sourceFile =
  [ productionTypeAlias alias
  | locatedTopLevel <- grammarV1TopLevelDecls sourceFile
  , let topLevel = locatedValue locatedTopLevel
  , GrammarV1TypeAliasDeclaration alias <-
      [locatedValue (grammarV1Declaration topLevel)]
  ]
  where
    productionTypeAlias alias = GrammarV1ReferenceTypeAliasSpine
      { grammarV1ReferenceTypeAliasName =
          locatedValue (grammarV1TypeAliasName alias)
      , grammarV1ReferenceTypeAliasGenericParamCount =
          length (grammarV1TypeAliasGenericParams alias)
      , grammarV1ReferenceTypeAliasRequirementCount =
          length (grammarV1TypeAliasRequirements alias)
      , grammarV1ReferenceTypeAliasTargetTag =
          grammarV1ProductionTypeTag (locatedValue (grammarV1TypeAliasTarget alias))
      }

grammarV1ProductionTypeTag :: GrammarV1Type -> GrammarV1ReferenceTypeTag
grammarV1ProductionTypeTag sourceType = case sourceType of
  GrammarV1UnitType -> GrammarV1ReferenceUnitType
  GrammarV1BoolType -> GrammarV1ReferenceBoolType
  GrammarV1UnsignedType spelling -> GrammarV1ReferencePrimitiveSpelling spelling
  GrammarV1BytesType _ -> GrammarV1ReferenceBytesType
  GrammarV1FrameType _ -> GrammarV1ReferenceFrameType
  GrammarV1ProofType _ -> GrammarV1ReferenceProofType
  GrammarV1ValidatedType _ _ _ -> GrammarV1ReferenceValidatedType
  GrammarV1RefinementType _ _ _ -> GrammarV1ReferenceRefinementType
  GrammarV1TupleType _ -> GrammarV1ReferenceTupleType
  GrammarV1NamedType _ -> GrammarV1ReferenceNamedType

grammarV1ReferenceTypeAliasSpines
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeAliasError [GrammarV1ReferenceTypeAliasSpine]
grammarV1ReferenceTypeAliasSpines tree = do
  sourceBody <- expectNonterminal "source_file" tree
  sourceFields <- expectSequence "source_file" sourceBody
  case sourceFields of
    [_moduleTree, _importTree, topLevelTree] -> do
      topLevels <- expectRepetition "source_file top levels" topLevelTree
      values <- traverse parseTopLevelTypeAlias topLevels
      pure [value | Just value <- values]
    _ -> failTypeAlias "source_file body is not a three-item sequence"

parseTopLevelTypeAlias
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeAliasError (Maybe GrammarV1ReferenceTypeAliasSpine)
parseTopLevelTypeAlias tree = do
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
              Just <$> parseTypeAliasDecl selected
            _ -> failTypeAlias "type-alias declaration does not occupy alternative 2"
        _ -> Right Nothing
    _ -> failTypeAlias "top_level_decl body is not a two-item sequence"

parseTypeAliasDecl
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeAliasError GrammarV1ReferenceTypeAliasSpine
parseTypeAliasDecl tree = do
  body <- expectNonterminal "type_alias_decl" tree
  fields <- expectSequence "type_alias_decl" body
  case fields of
    [typeKeyword, nameTree, genericTree, requirementTree, equalsSign, targetTree, terminator] -> do
      expectLiteral "type" typeKeyword
      name <- parseIdentifier nameTree
      genericCount <- parseOptionalGenericParams genericTree
      requirementCount <- parseOptionalGenericRequirements requirementTree
      expectLiteral "=" equalsSign
      targetTag <- grammarV1ReferenceTypeTag targetTree
      expectLiteral ";" terminator
      pure GrammarV1ReferenceTypeAliasSpine
        { grammarV1ReferenceTypeAliasName = name
        , grammarV1ReferenceTypeAliasGenericParamCount = genericCount
        , grammarV1ReferenceTypeAliasRequirementCount = requirementCount
        , grammarV1ReferenceTypeAliasTargetTag = targetTag
        }
    _ -> failTypeAlias "type_alias_decl body is not a seven-item sequence"

parseOptionalGenericParams
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeAliasError Int
parseOptionalGenericParams tree = case tree of
  GrammarV1ReferenceOptionalNone -> Right 0
  GrammarV1ReferenceOptionalSome paramsTree -> do
    body <- expectNonterminal "generic_params" paramsTree
    fields <- expectSequence "generic_params" body
    case fields of
      [openBracket, firstParam, restTree, closeBracket] -> do
        expectLiteral "[" openBracket
        expectNamedNode "generic_param" firstParam
        rest <- expectRepetition "generic_params suffix" restTree
        traverse_ validateGenericParamSuffix rest
        expectLiteral "]" closeBracket
        pure (1 + length rest)
      _ -> failTypeAlias "generic_params body is not a four-item sequence"
  _ -> failTypeAlias "type_alias_decl generic-parameter slot is not optional"

validateGenericParamSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeAliasError ()
validateGenericParamSuffix tree = do
  fields <- expectSequence "generic_params suffix item" tree
  case fields of
    [comma, param] -> do
      expectLiteral "," comma
      expectNamedNode "generic_param" param
    _ -> failTypeAlias "generic_params suffix item is not a two-item sequence"

parseOptionalGenericRequirements
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeAliasError Int
parseOptionalGenericRequirements tree = case tree of
  GrammarV1ReferenceOptionalNone -> Right 0
  GrammarV1ReferenceOptionalSome requirementsTree -> do
    body <- expectNonterminal "generic_requirements" requirementsTree
    fields <- expectSequence "generic_requirements" body
    case fields of
      [requiresKeyword, openBrace, entriesTree, closeBrace] -> do
        expectLiteral "requires" requiresKeyword
        expectLiteral "{" openBrace
        entries <- expectRepetition "generic_requirements entries" entriesTree
        traverse_ (expectNamedNode "generic_requirement") entries
        expectLiteral "}" closeBrace
        pure (length entries)
      _ -> failTypeAlias "generic_requirements body is not a four-item sequence"
  _ -> failTypeAlias "type_alias_decl requirement slot is not optional"

grammarV1ReferenceTypeTag
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeAliasError GrammarV1ReferenceTypeTag
grammarV1ReferenceTypeTag tree = do
  body <- expectNonterminal "type_expression" tree
  case body of
    GrammarV1ReferenceAlternative 0 nonreference ->
      parseNonreferenceTypeTag nonreference
    GrammarV1ReferenceAlternative 1 named -> do
      namedBody <- expectNonterminal "named_type" named
      expectNamedNode "static_reference" namedBody
      pure GrammarV1ReferenceNamedType
    GrammarV1ReferenceAlternative index _ ->
      failTypeAlias ("type_expression alternative out of range: " <> showText index)
    _ -> failTypeAlias "type_expression body is not an alternative node"

parseNonreferenceTypeTag
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeAliasError GrammarV1ReferenceTypeTag
parseNonreferenceTypeTag tree = do
  body <- expectNonterminal "nonreference_type_expression" tree
  case body of
    GrammarV1ReferenceAlternative index selected -> case index of
      0 -> expectLiteral "Unit" selected >> pure GrammarV1ReferenceUnitType
      1 -> expectLiteral "Bool" selected >> pure GrammarV1ReferenceBoolType
      2 -> expectLiteral "Char" selected >> pure (GrammarV1ReferencePrimitiveSpelling "Char")
      3 -> expectLiteral "String" selected >> pure (GrammarV1ReferencePrimitiveSpelling "String")
      4 -> GrammarV1ReferencePrimitiveSpelling <$> parseLexicalType "uint_type" "UINT_TYPE" selected
      5 -> GrammarV1ReferencePrimitiveSpelling <$> parseLexicalType "sint_type" "SINT_TYPE" selected
      6 -> GrammarV1ReferencePrimitiveSpelling <$> parseFloatType selected
      7 -> validateBytesType selected >> pure GrammarV1ReferenceBytesType
      8 -> validateBracketedOne "Frame" "static_reference" selected >> pure GrammarV1ReferenceFrameType
      9 -> validateBracketedOne "Proof" "proposition" selected >> pure GrammarV1ReferenceProofType
      10 -> validateValidatedType selected >> pure GrammarV1ReferenceValidatedType
      11 -> expectNamedNode "refinement_type" selected >> pure GrammarV1ReferenceRefinementType
      12 -> expectNamedNode "tuple_type" selected >> pure GrammarV1ReferenceTupleType
      _ -> failTypeAlias ("nonreference_type_expression alternative out of range: " <> showText index)
    _ -> failTypeAlias "nonreference_type_expression body is not an alternative node"

parseLexicalType
  :: Text
  -> Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeAliasError Text
parseLexicalType nonterminal className tree = do
  body <- expectNonterminal nonterminal tree
  case body of
    GrammarV1ReferenceLexical actualClass spelling
      | actualClass == className -> Right spelling
      | otherwise -> failTypeAlias
          (nonterminal <> " uses lexical class " <> actualClass)
    _ -> failTypeAlias (nonterminal <> " body is not a lexical leaf")

parseFloatType
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeAliasError Text
parseFloatType tree = do
  body <- expectNonterminal "float_type" tree
  case body of
    GrammarV1ReferenceAlternative 0 selected ->
      expectLiteral "F32" selected >> pure "F32"
    GrammarV1ReferenceAlternative 1 selected ->
      expectLiteral "F64" selected >> pure "F64"
    GrammarV1ReferenceAlternative index _ ->
      failTypeAlias ("float_type alternative out of range: " <> showText index)
    _ -> failTypeAlias "float_type body is not an alternative node"

validateBytesType
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeAliasError ()
validateBytesType tree = do
  fields <- expectSequence "Bytes type" tree
  case fields of
    [bytesKeyword, optionalIndex] -> do
      expectLiteral "Bytes" bytesKeyword
      case optionalIndex of
        GrammarV1ReferenceOptionalNone -> Right ()
        GrammarV1ReferenceOptionalSome indexTree -> do
          indexFields <- expectSequence "Bytes index" indexTree
          case indexFields of
            [openBracket, expressionTree, closeBracket] -> do
              expectLiteral "[" openBracket
              expectNamedNode "expression" expressionTree
              expectLiteral "]" closeBracket
            _ -> failTypeAlias "Bytes index is not a three-item sequence"
        _ -> failTypeAlias "Bytes index slot is not optional"
    _ -> failTypeAlias "Bytes type body is not a two-item sequence"

validateBracketedOne
  :: Text
  -> Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeAliasError ()
validateBracketedOne keyword childName tree = do
  fields <- expectSequence (keyword <> " type") tree
  case fields of
    [keywordTree, openBracket, childTree, closeBracket] -> do
      expectLiteral keyword keywordTree
      expectLiteral "[" openBracket
      expectNamedNode childName childTree
      expectLiteral "]" closeBracket
    _ -> failTypeAlias (keyword <> " type body is not a four-item sequence")

validateValidatedType
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeAliasError ()
validateValidatedType tree = do
  fields <- expectSequence "Validated type" tree
  case fields of
    [ validatedKeyword
      , openBracket
      , referenceTree
      , firstComma
      , firstExpression
      , secondComma
      , secondExpression
      , closeBracket
      ] -> do
        expectLiteral "Validated" validatedKeyword
        expectLiteral "[" openBracket
        expectNamedNode "static_reference" referenceTree
        expectLiteral "," firstComma
        expectNamedNode "expression" firstExpression
        expectLiteral "," secondComma
        expectNamedNode "expression" secondExpression
        expectLiteral "]" closeBracket
    _ -> failTypeAlias "Validated type body is not an eight-item sequence"

parseIdentifier
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeAliasError Text
parseIdentifier tree = do
  body <- expectNonterminal "identifier" tree
  case body of
    GrammarV1ReferenceLexical "IDENTIFIER" value -> Right value
    GrammarV1ReferenceLexical className _ ->
      failTypeAlias ("identifier uses lexical class " <> className)
    _ -> failTypeAlias "identifier body is not an IDENTIFIER lexical leaf"

expectNamedNode
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeAliasError ()
expectNamedNode name tree = expectNonterminal name tree >> pure ()

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeAliasError GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> Right body
    | otherwise -> failTypeAlias
        ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failTypeAlias ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeAliasError [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence items -> Right items
  _ -> failTypeAlias (label <> " is not a sequence node")

expectRepetition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeAliasError [GrammarV1ReferenceParseTree]
expectRepetition label tree = case tree of
  GrammarV1ReferenceRepetition items -> Right items
  _ -> failTypeAlias (label <> " is not a repetition node")

expectLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypeAliasError ()
expectLiteral expected tree = case tree of
  GrammarV1ReferenceLiteral actual
    | actual == expected -> Right ()
    | otherwise -> failTypeAlias
        ("expected literal " <> expected <> ", got " <> actual)
  _ -> failTypeAlias ("expected literal " <> expected)

traverse_
  :: (a -> Either e ())
  -> [a]
  -> Either e ()
traverse_ action values = case values of
  [] -> Right ()
  value : rest -> action value >> traverse_ action rest

mapTopLevelError
  :: Either a b
  -> Either GrammarV1ReferenceTypeAliasError b
mapTopLevelError result = case result of
  Left _ -> failTypeAlias "top-level declaration-choice validation failed"
  Right value -> Right value

showText :: Show a => a -> Text
showText = Text.pack . show

failTypeAlias :: Text -> Either GrammarV1ReferenceTypeAliasError a
failTypeAlias = Left . GrammarV1ReferenceTypeAliasError
