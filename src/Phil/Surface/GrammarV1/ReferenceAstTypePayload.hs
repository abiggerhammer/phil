{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstTypePayload
  ( GrammarV1ReferenceTypePayloadError (..)
  , GrammarV1ReferenceBytesPayload (..)
  , GrammarV1ReferenceTypePayload (..)
  , grammarV1ProductionTypePayload
  , grammarV1ReferenceTypePayload
  , grammarV1ProductionTypeAliasTypePayloads
  , grammarV1ReferenceTypeAliasTypePayloads
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Lexer (runtimeBytesLengthMarker)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Declaration (..)
  , GrammarV1Expression (..)
  , GrammarV1SourceFile (..)
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

newtype GrammarV1ReferenceTypePayloadError =
  GrammarV1ReferenceTypePayloadError Text
  deriving (Eq, Show)

data GrammarV1ReferenceBytesPayload
  = GrammarV1ReferenceRuntimeBytes
  | GrammarV1ReferenceIndexedBytes
  deriving (Eq, Ord, Show)

data GrammarV1ReferenceTypePayload
  = GrammarV1ReferencePayloadUnit
  | GrammarV1ReferencePayloadBool
  | GrammarV1ReferencePayloadPrimitive Text
  | GrammarV1ReferencePayloadBytes GrammarV1ReferenceBytesPayload
  | GrammarV1ReferencePayloadFrame GrammarV1ReferenceStaticReferenceSpine
  | GrammarV1ReferencePayloadProof
  | GrammarV1ReferencePayloadValidated GrammarV1ReferenceStaticReferenceSpine
  | GrammarV1ReferencePayloadRefinement Text GrammarV1ReferenceTypePayload
  | GrammarV1ReferencePayloadTuple [GrammarV1ReferenceTypePayload]
  | GrammarV1ReferencePayloadNamed GrammarV1ReferenceStaticReferenceSpine
  deriving (Eq, Show)

grammarV1ProductionTypePayload
  :: GrammarV1Type
  -> GrammarV1ReferenceTypePayload
grammarV1ProductionTypePayload sourceType = case sourceType of
  GrammarV1UnitType -> GrammarV1ReferencePayloadUnit
  GrammarV1BoolType -> GrammarV1ReferencePayloadBool
  GrammarV1UnsignedType spelling -> GrammarV1ReferencePayloadPrimitive spelling
  GrammarV1BytesType sizeExpression ->
    GrammarV1ReferencePayloadBytes
      (case locatedValue sizeExpression of
        GrammarV1IntegerExpression marker
          | marker == runtimeBytesLengthMarker -> GrammarV1ReferenceRuntimeBytes
        _ -> GrammarV1ReferenceIndexedBytes)
  GrammarV1FrameType reference ->
    GrammarV1ReferencePayloadFrame
      (grammarV1ProductionStaticReferenceSpine (locatedValue reference))
  GrammarV1ProofType _ -> GrammarV1ReferencePayloadProof
  GrammarV1ValidatedType reference _ _ ->
    GrammarV1ReferencePayloadValidated
      (grammarV1ProductionStaticReferenceSpine (locatedValue reference))
  GrammarV1RefinementType binder baseType _ ->
    GrammarV1ReferencePayloadRefinement
      (locatedValue binder)
      (grammarV1ProductionTypePayload (locatedValue baseType))
  GrammarV1TupleType elements ->
    GrammarV1ReferencePayloadTuple
      (map (grammarV1ProductionTypePayload . locatedValue) elements)
  GrammarV1NamedType reference ->
    GrammarV1ReferencePayloadNamed
      (grammarV1ProductionStaticReferenceSpine reference)

grammarV1ReferenceTypePayload
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypePayloadError GrammarV1ReferenceTypePayload
grammarV1ReferenceTypePayload tree = do
  body <- expectNonterminal "type_expression" tree
  case body of
    GrammarV1ReferenceAlternative 0 nonreference ->
      parseNonreferenceTypePayload nonreference
    GrammarV1ReferenceAlternative 1 named -> do
      namedBody <- expectNonterminal "named_type" named
      reference <- mapStaticReferenceError
        (grammarV1ReferenceStaticReferenceSpine namedBody)
      pure (GrammarV1ReferencePayloadNamed reference)
    GrammarV1ReferenceAlternative index _ ->
      failTypePayload ("type_expression alternative out of range: " <> showText index)
    _ -> failTypePayload "type_expression body is not an alternative node"

parseNonreferenceTypePayload
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypePayloadError GrammarV1ReferenceTypePayload
parseNonreferenceTypePayload tree = do
  body <- expectNonterminal "nonreference_type_expression" tree
  case body of
    GrammarV1ReferenceAlternative index selected -> case index of
      0 -> expectLiteral "Unit" selected >> pure GrammarV1ReferencePayloadUnit
      1 -> expectLiteral "Bool" selected >> pure GrammarV1ReferencePayloadBool
      2 -> expectLiteral "Char" selected >> pure (GrammarV1ReferencePayloadPrimitive "Char")
      3 -> expectLiteral "String" selected >> pure (GrammarV1ReferencePayloadPrimitive "String")
      4 -> GrammarV1ReferencePayloadPrimitive
        <$> parseLexicalType "uint_type" "UINT_TYPE" selected
      5 -> GrammarV1ReferencePayloadPrimitive
        <$> parseLexicalType "sint_type" "SINT_TYPE" selected
      6 -> GrammarV1ReferencePayloadPrimitive <$> parseFloatType selected
      7 -> GrammarV1ReferencePayloadBytes <$> parseBytesPayload selected
      8 -> GrammarV1ReferencePayloadFrame <$> parseBracketedReference "Frame" selected
      9 -> parseProofPayload selected
      10 -> parseValidatedPayload selected
      11 -> parseRefinementPayload selected
      12 -> parseTuplePayload selected
      _ -> failTypePayload
        ("nonreference_type_expression alternative out of range: " <> showText index)
    _ -> failTypePayload
      "nonreference_type_expression body is not an alternative node"

parseLexicalType
  :: Text
  -> Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypePayloadError Text
parseLexicalType nonterminal className tree = do
  body <- expectNonterminal nonterminal tree
  case body of
    GrammarV1ReferenceLexical actualClass spelling
      | actualClass == className -> Right spelling
      | otherwise -> failTypePayload
          (nonterminal <> " uses lexical class " <> actualClass)
    _ -> failTypePayload (nonterminal <> " body is not a lexical leaf")

parseFloatType
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypePayloadError Text
parseFloatType tree = do
  body <- expectNonterminal "float_type" tree
  case body of
    GrammarV1ReferenceAlternative 0 selected ->
      expectLiteral "F32" selected >> pure "F32"
    GrammarV1ReferenceAlternative 1 selected ->
      expectLiteral "F64" selected >> pure "F64"
    GrammarV1ReferenceAlternative index _ ->
      failTypePayload ("float_type alternative out of range: " <> showText index)
    _ -> failTypePayload "float_type body is not an alternative node"

parseBytesPayload
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypePayloadError GrammarV1ReferenceBytesPayload
parseBytesPayload tree = do
  fields <- expectSequence "Bytes type" tree
  case fields of
    [bytesKeyword, optionalIndex] -> do
      expectLiteral "Bytes" bytesKeyword
      case optionalIndex of
        GrammarV1ReferenceOptionalNone -> pure GrammarV1ReferenceRuntimeBytes
        GrammarV1ReferenceOptionalSome indexTree -> do
          indexFields <- expectSequence "Bytes index" indexTree
          case indexFields of
            [openBracket, expressionTree, closeBracket] -> do
              expectLiteral "[" openBracket
              expectNamedNode "expression" expressionTree
              expectLiteral "]" closeBracket
              pure GrammarV1ReferenceIndexedBytes
            _ -> failTypePayload "Bytes index is not a three-item sequence"
        _ -> failTypePayload "Bytes index slot is not optional"
    _ -> failTypePayload "Bytes type body is not a two-item sequence"

parseBracketedReference
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypePayloadError GrammarV1ReferenceStaticReferenceSpine
parseBracketedReference keyword tree = do
  fields <- expectSequence (keyword <> " type") tree
  case fields of
    [keywordTree, openBracket, referenceTree, closeBracket] -> do
      expectLiteral keyword keywordTree
      expectLiteral "[" openBracket
      reference <- mapStaticReferenceError
        (grammarV1ReferenceStaticReferenceSpine referenceTree)
      expectLiteral "]" closeBracket
      pure reference
    _ -> failTypePayload (keyword <> " type body is not a four-item sequence")

parseProofPayload
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypePayloadError GrammarV1ReferenceTypePayload
parseProofPayload tree = do
  fields <- expectSequence "Proof type" tree
  case fields of
    [keywordTree, openBracket, propositionTree, closeBracket] -> do
      expectLiteral "Proof" keywordTree
      expectLiteral "[" openBracket
      expectNamedNode "proposition" propositionTree
      expectLiteral "]" closeBracket
      pure GrammarV1ReferencePayloadProof
    _ -> failTypePayload "Proof type body is not a four-item sequence"

parseValidatedPayload
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypePayloadError GrammarV1ReferenceTypePayload
parseValidatedPayload tree = do
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
        reference <- mapStaticReferenceError
          (grammarV1ReferenceStaticReferenceSpine referenceTree)
        expectLiteral "," firstComma
        expectNamedNode "expression" firstExpression
        expectLiteral "," secondComma
        expectNamedNode "expression" secondExpression
        expectLiteral "]" closeBracket
        pure (GrammarV1ReferencePayloadValidated reference)
    _ -> failTypePayload "Validated type body is not an eight-item sequence"

parseRefinementPayload
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypePayloadError GrammarV1ReferenceTypePayload
parseRefinementPayload tree = do
  body <- expectNonterminal "refinement_type" tree
  fields <- expectSequence "refinement_type" body
  case fields of
    [ openBrace
      , binderTree
      , colon
      , baseTypeTree
      , bar
      , propositionTree
      , closeBrace
      ] -> do
        expectLiteral "{" openBrace
        binder <- parseIdentifier binderTree
        expectLiteral ":" colon
        baseType <- grammarV1ReferenceTypePayload baseTypeTree
        expectLiteral "|" bar
        expectNamedNode "proposition" propositionTree
        expectLiteral "}" closeBrace
        pure (GrammarV1ReferencePayloadRefinement binder baseType)
    _ -> failTypePayload "refinement_type body is not a seven-item sequence"

parseTuplePayload
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypePayloadError GrammarV1ReferenceTypePayload
parseTuplePayload tree = do
  body <- expectNonterminal "tuple_type" tree
  fields <- expectSequence "tuple_type" body
  case fields of
    [openParen, firstTree, firstComma, secondTree, restTree, closeParen] -> do
      expectLiteral "(" openParen
      first <- grammarV1ReferenceTypePayload firstTree
      expectLiteral "," firstComma
      second <- grammarV1ReferenceTypePayload secondTree
      restItems <- expectRepetition "tuple_type suffix" restTree
      rest <- traverse parseTupleSuffix restItems
      expectLiteral ")" closeParen
      pure (GrammarV1ReferencePayloadTuple (first : second : rest))
    _ -> failTypePayload "tuple_type body is not a six-item sequence"

parseTupleSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypePayloadError GrammarV1ReferenceTypePayload
parseTupleSuffix tree = do
  fields <- expectSequence "tuple_type suffix item" tree
  case fields of
    [comma, typeTree] -> do
      expectLiteral "," comma
      grammarV1ReferenceTypePayload typeTree
    _ -> failTypePayload "tuple_type suffix item is not a two-item sequence"

parseIdentifier
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypePayloadError Text
parseIdentifier tree = do
  body <- expectNonterminal "identifier" tree
  case body of
    GrammarV1ReferenceLexical "IDENTIFIER" value -> Right value
    GrammarV1ReferenceLexical className _ ->
      failTypePayload ("identifier uses lexical class " <> className)
    _ -> failTypePayload "identifier body is not an IDENTIFIER lexical leaf"

grammarV1ProductionTypeAliasTypePayloads
  :: GrammarV1SourceFile
  -> [GrammarV1ReferenceTypePayload]
grammarV1ProductionTypeAliasTypePayloads sourceFile =
  [ grammarV1ProductionTypePayload (locatedValue (grammarV1TypeAliasTarget alias))
  | locatedTopLevel <- grammarV1TopLevelDecls sourceFile
  , let topLevel = locatedValue locatedTopLevel
  , GrammarV1TypeAliasDeclaration alias <-
      [locatedValue (grammarV1Declaration topLevel)]
  ]

grammarV1ReferenceTypeAliasTypePayloads
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypePayloadError [GrammarV1ReferenceTypePayload]
grammarV1ReferenceTypeAliasTypePayloads tree = do
  sourceBody <- expectNonterminal "source_file" tree
  sourceFields <- expectSequence "source_file" sourceBody
  case sourceFields of
    [_moduleTree, _importTree, topLevelTree] -> do
      topLevels <- expectRepetition "source_file top levels" topLevelTree
      values <- traverse parseTopLevelTypeAliasPayload topLevels
      pure [value | Just value <- values]
    _ -> failTypePayload "source_file body is not a three-item sequence"

parseTopLevelTypeAliasPayload
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypePayloadError (Maybe GrammarV1ReferenceTypePayload)
parseTopLevelTypeAliasPayload tree = do
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
              Just <$> parseTypeAliasTargetPayload selected
            _ -> failTypePayload
              "type-alias declaration does not occupy alternative 2"
        _ -> Right Nothing
    _ -> failTypePayload "top_level_decl body is not a two-item sequence"

parseTypeAliasTargetPayload
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypePayloadError GrammarV1ReferenceTypePayload
parseTypeAliasTargetPayload tree = do
  body <- expectNonterminal "type_alias_decl" tree
  fields <- expectSequence "type_alias_decl" body
  case fields of
    [_keyword, _name, _generic, _requirements, _equals, targetTree, _terminator] ->
      grammarV1ReferenceTypePayload targetTree
    _ -> failTypePayload "type_alias_decl body is not a seven-item sequence"

expectNamedNode
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypePayloadError ()
expectNamedNode name tree = expectNonterminal name tree >> pure ()

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypePayloadError GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> Right body
    | otherwise -> failTypePayload
        ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failTypePayload ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypePayloadError [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence items -> Right items
  _ -> failTypePayload (label <> " is not a sequence node")

expectRepetition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypePayloadError [GrammarV1ReferenceParseTree]
expectRepetition label tree = case tree of
  GrammarV1ReferenceRepetition items -> Right items
  _ -> failTypePayload (label <> " is not a repetition node")

expectLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceTypePayloadError ()
expectLiteral expected tree = case tree of
  GrammarV1ReferenceLiteral actual
    | actual == expected -> Right ()
    | otherwise -> failTypePayload
        ("expected literal " <> expected <> ", got " <> actual)
  _ -> failTypePayload ("expected literal " <> expected)

mapStaticReferenceError
  :: Either GrammarV1ReferenceStaticReferenceError a
  -> Either GrammarV1ReferenceTypePayloadError a
mapStaticReferenceError = mapLeft
  (GrammarV1ReferenceTypePayloadError . Text.pack . show)

mapTopLevelError
  :: Show e
  => Either e a
  -> Either GrammarV1ReferenceTypePayloadError a
mapTopLevelError = mapLeft
  (GrammarV1ReferenceTypePayloadError . Text.pack . show)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value

showText :: Show a => a -> Text
showText = Text.pack . show

failTypePayload
  :: Text
  -> Either GrammarV1ReferenceTypePayloadError a
failTypePayload = Left . GrammarV1ReferenceTypePayloadError
