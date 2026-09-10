{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstStaticReference
  ( GrammarV1ReferenceStaticReferenceError (..)
  , GrammarV1ReferenceStaticArgumentTag (..)
  , GrammarV1ReferenceStaticReferenceSpine (..)
  , grammarV1ProductionStaticReferenceSpine
  , grammarV1ReferenceStaticReferenceSpine
  , grammarV1ProductionTypeAliasStaticReferenceSpines
  , grammarV1ReferenceTypeAliasStaticReferenceSpines
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Declaration (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1SourceFile (..)
  , GrammarV1StaticArgument (..)
  , GrammarV1StaticReference (..)
  , GrammarV1TopLevelDecl (..)
  , GrammarV1Type (..)
  , GrammarV1TypeAliasDecl (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstTopLevel
  ( GrammarV1ReferenceDeclarationTag (..)
  , grammarV1ReferenceDeclarationTag
  )
import Phil.Surface.GrammarV1.ReferenceAstTypeAlias
  ( GrammarV1ReferenceTypeAliasError
  , GrammarV1ReferenceTypeTag
  , grammarV1ProductionTypeTag
  , grammarV1ReferenceTypeTag
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( GrammarV1ReferenceParseTree (..)
  )
import Phil.Surface.Syntax (Located (..))

newtype GrammarV1ReferenceStaticReferenceError =
  GrammarV1ReferenceStaticReferenceError Text
  deriving (Eq, Show)

data GrammarV1ReferenceStaticArgumentTag
  = GrammarV1ReferenceStaticTypeArgument GrammarV1ReferenceTypeTag
  | GrammarV1ReferenceStaticSessionArgument
  | GrammarV1ReferenceStaticValueArgument
  | GrammarV1ReferenceStaticEffectSetArgument
  deriving (Eq, Show)

data GrammarV1ReferenceStaticReferenceSpine = GrammarV1ReferenceStaticReferenceSpine
  { grammarV1ReferenceStaticReferenceName :: [Text]
  , grammarV1ReferenceStaticReferenceArguments :: [GrammarV1ReferenceStaticArgumentTag]
  }
  deriving (Eq, Show)

grammarV1ProductionStaticReferenceSpine
  :: GrammarV1StaticReference
  -> GrammarV1ReferenceStaticReferenceSpine
grammarV1ProductionStaticReferenceSpine reference =
  GrammarV1ReferenceStaticReferenceSpine
    { grammarV1ReferenceStaticReferenceName =
        grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference)
    , grammarV1ReferenceStaticReferenceArguments =
        map productionStaticArgumentTag (grammarV1StaticReferenceArguments reference)
    }

productionStaticArgumentTag
  :: GrammarV1StaticArgument
  -> GrammarV1ReferenceStaticArgumentTag
productionStaticArgumentTag argument = case argument of
  GrammarV1StaticTypeArgument sourceType ->
    GrammarV1ReferenceStaticTypeArgument (grammarV1ProductionTypeTag sourceType)
  GrammarV1StaticSessionArgument _ ->
    GrammarV1ReferenceStaticSessionArgument
  GrammarV1StaticEffectSetArgument _ ->
    GrammarV1ReferenceStaticEffectSetArgument
  GrammarV1StaticReferenceArgument _ ->
    GrammarV1ReferenceStaticValueArgument
  GrammarV1StaticBoolArgument _ ->
    GrammarV1ReferenceStaticValueArgument
  GrammarV1StaticUnitArgument ->
    GrammarV1ReferenceStaticValueArgument
  GrammarV1StaticIntegerArgument _ ->
    GrammarV1ReferenceStaticValueArgument
  GrammarV1StaticValueArgument _ ->
    GrammarV1ReferenceStaticValueArgument

grammarV1ReferenceStaticReferenceSpine
  :: GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceStaticReferenceError
      GrammarV1ReferenceStaticReferenceSpine
grammarV1ReferenceStaticReferenceSpine tree = do
  body <- expectNonterminal "static_reference" tree
  fields <- expectSequence "static_reference" body
  case fields of
    [nameTree, argumentTree] -> do
      name <- parseQualifiedName nameTree
      arguments <- parseOptionalStaticArguments argumentTree
      pure GrammarV1ReferenceStaticReferenceSpine
        { grammarV1ReferenceStaticReferenceName = name
        , grammarV1ReferenceStaticReferenceArguments = arguments
        }
    _ -> failStaticReference "static_reference body is not a two-item sequence"

parseOptionalStaticArguments
  :: GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceStaticReferenceError
      [GrammarV1ReferenceStaticArgumentTag]
parseOptionalStaticArguments tree = case tree of
  GrammarV1ReferenceOptionalNone -> Right []
  GrammarV1ReferenceOptionalSome argumentsTree -> parseStaticArguments argumentsTree
  _ -> failStaticReference "static_reference argument slot is not optional"

parseStaticArguments
  :: GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceStaticReferenceError
      [GrammarV1ReferenceStaticArgumentTag]
parseStaticArguments tree = do
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
              first <- parseStaticArgument firstTree
              restItems <- expectRepetition "static_arguments suffix" restTree
              rest <- traverse parseStaticArgumentSuffix restItems
              pure (first : rest)
            _ -> failStaticReference
              "static_arguments item body is not a two-item sequence"
        _ -> failStaticReference "static_arguments items slot is not optional"
      expectLiteral "]" closeBracket
      pure values
    _ -> failStaticReference "static_arguments body is not a three-item sequence"

parseStaticArgumentSuffix
  :: GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceStaticReferenceError
      GrammarV1ReferenceStaticArgumentTag
parseStaticArgumentSuffix tree = do
  fields <- expectSequence "static_arguments suffix item" tree
  case fields of
    [comma, argumentTree] -> do
      expectLiteral "," comma
      parseStaticArgument argumentTree
    _ -> failStaticReference
      "static_arguments suffix item is not a two-item sequence"

parseStaticArgument
  :: GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceStaticReferenceError
      GrammarV1ReferenceStaticArgumentTag
parseStaticArgument tree = do
  body <- expectNonterminal "static_argument" tree
  case body of
    GrammarV1ReferenceAlternative 0 selected -> do
      typeTag <- mapTypeError
        (grammarV1ReferenceTypeTag
          (GrammarV1ReferenceNonterminal
            "type_expression"
            (GrammarV1ReferenceAlternative 0 selected)))
      pure (GrammarV1ReferenceStaticTypeArgument typeTag)
    GrammarV1ReferenceAlternative 1 selected -> do
      expectNamedNode "nonreference_session_expression" selected
      pure GrammarV1ReferenceStaticSessionArgument
    GrammarV1ReferenceAlternative 2 selected -> do
      expectNamedNode "static_value_expression" selected
      pure GrammarV1ReferenceStaticValueArgument
    GrammarV1ReferenceAlternative 3 selected -> do
      expectNamedNode "effect_set_literal" selected
      pure GrammarV1ReferenceStaticEffectSetArgument
    GrammarV1ReferenceAlternative index _ ->
      failStaticReference
        ("static_argument alternative out of range: " <> showText index)
    _ -> failStaticReference "static_argument body is not an alternative node"

grammarV1ProductionTypeAliasStaticReferenceSpines
  :: GrammarV1SourceFile
  -> [[GrammarV1ReferenceStaticReferenceSpine]]
grammarV1ProductionTypeAliasStaticReferenceSpines sourceFile =
  [ productionTargetReferences (locatedValue (grammarV1TypeAliasTarget alias))
  | locatedTopLevel <- grammarV1TopLevelDecls sourceFile
  , let topLevel = locatedValue locatedTopLevel
  , GrammarV1TypeAliasDeclaration alias <-
      [locatedValue (grammarV1Declaration topLevel)]
  ]
  where
    productionTargetReferences sourceType = case sourceType of
      GrammarV1NamedType reference ->
        [grammarV1ProductionStaticReferenceSpine reference]
      GrammarV1FrameType reference ->
        [grammarV1ProductionStaticReferenceSpine (locatedValue reference)]
      GrammarV1ValidatedType reference _ _ ->
        [grammarV1ProductionStaticReferenceSpine (locatedValue reference)]
      _ -> []

grammarV1ReferenceTypeAliasStaticReferenceSpines
  :: GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceStaticReferenceError
      [[GrammarV1ReferenceStaticReferenceSpine]]
grammarV1ReferenceTypeAliasStaticReferenceSpines tree = do
  sourceBody <- expectNonterminal "source_file" tree
  sourceFields <- expectSequence "source_file" sourceBody
  case sourceFields of
    [_moduleTree, _importTree, topLevelTree] -> do
      topLevels <- expectRepetition "source_file top levels" topLevelTree
      values <- traverse parseTopLevelTypeAliasReference topLevels
      pure [value | Just value <- values]
    _ -> failStaticReference "source_file body is not a three-item sequence"

parseTopLevelTypeAliasReference
  :: GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceStaticReferenceError
      (Maybe [GrammarV1ReferenceStaticReferenceSpine])
parseTopLevelTypeAliasReference tree = do
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
              Just <$> parseTypeAliasTargetReference selected
            _ -> failStaticReference
              "type-alias declaration does not occupy alternative 2"
        _ -> Right Nothing
    _ -> failStaticReference "top_level_decl body is not a two-item sequence"

parseTypeAliasTargetReference
  :: GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceStaticReferenceError
      [GrammarV1ReferenceStaticReferenceSpine]
parseTypeAliasTargetReference tree = do
  body <- expectNonterminal "type_alias_decl" tree
  fields <- expectSequence "type_alias_decl" body
  case fields of
    [_keyword, _name, _generic, _requirements, _equals, targetTree, _terminator] ->
      parseTypeTargetRootReference targetTree
    _ -> failStaticReference "type_alias_decl body is not a seven-item sequence"

parseTypeTargetRootReference
  :: GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceStaticReferenceError
      [GrammarV1ReferenceStaticReferenceSpine]
parseTypeTargetRootReference tree = do
  body <- expectNonterminal "type_expression" tree
  case body of
    GrammarV1ReferenceAlternative 1 namedTree -> do
      namedBody <- expectNonterminal "named_type" namedTree
      value <- grammarV1ReferenceStaticReferenceSpine namedBody
      pure [value]
    GrammarV1ReferenceAlternative 0 nonreferenceTree -> do
      nonreferenceBody <- expectNonterminal "nonreference_type_expression" nonreferenceTree
      case nonreferenceBody of
        GrammarV1ReferenceAlternative 8 selected ->
          oneBracketedReference "Frame" selected
        GrammarV1ReferenceAlternative 10 selected ->
          validatedReference selected
        GrammarV1ReferenceAlternative _ _ -> Right []
        _ -> failStaticReference
          "nonreference_type_expression body is not an alternative node"
    GrammarV1ReferenceAlternative index _ ->
      failStaticReference
        ("type_expression alternative out of range: " <> showText index)
    _ -> failStaticReference "type_expression body is not an alternative node"

oneBracketedReference
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceStaticReferenceError
      [GrammarV1ReferenceStaticReferenceSpine]
oneBracketedReference keyword tree = do
  fields <- expectSequence (keyword <> " type") tree
  case fields of
    [keywordTree, openBracket, referenceTree, closeBracket] -> do
      expectLiteral keyword keywordTree
      expectLiteral "[" openBracket
      reference <- grammarV1ReferenceStaticReferenceSpine referenceTree
      expectLiteral "]" closeBracket
      pure [reference]
    _ -> failStaticReference (keyword <> " type body is not a four-item sequence")

validatedReference
  :: GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceStaticReferenceError
      [GrammarV1ReferenceStaticReferenceSpine]
validatedReference tree = do
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
        reference <- grammarV1ReferenceStaticReferenceSpine referenceTree
        expectLiteral "," firstComma
        expectNamedNode "expression" firstExpression
        expectLiteral "," secondComma
        expectNamedNode "expression" secondExpression
        expectLiteral "]" closeBracket
        pure [reference]
    _ -> failStaticReference "Validated type body is not an eight-item sequence"

parseQualifiedName
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticReferenceError [Text]
parseQualifiedName tree = do
  body <- expectNonterminal "qualified_name" tree
  fields <- expectSequence "qualified_name" body
  case fields of
    [firstTree, restTree] -> do
      first <- parseIdentifier firstTree
      restItems <- expectRepetition "qualified_name suffix" restTree
      rest <- traverse parseQualifiedNameSuffix restItems
      pure (first : rest)
    _ -> failStaticReference "qualified_name body is not a two-item sequence"

parseQualifiedNameSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticReferenceError Text
parseQualifiedNameSuffix tree = do
  fields <- expectSequence "qualified_name suffix item" tree
  case fields of
    [dot, identifier] -> do
      expectLiteral "." dot
      parseIdentifier identifier
    _ -> failStaticReference
      "qualified_name suffix item is not a two-item sequence"

parseIdentifier
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticReferenceError Text
parseIdentifier tree = do
  body <- expectNonterminal "identifier" tree
  case body of
    GrammarV1ReferenceLexical "IDENTIFIER" value -> Right value
    GrammarV1ReferenceLexical className _ ->
      failStaticReference ("identifier uses lexical class " <> className)
    _ -> failStaticReference "identifier body is not an IDENTIFIER lexical leaf"

expectNamedNode
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticReferenceError ()
expectNamedNode name tree = expectNonterminal name tree >> pure ()

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceStaticReferenceError
      GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> Right body
    | otherwise -> failStaticReference
        ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failStaticReference ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceStaticReferenceError
      [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence items -> Right items
  _ -> failStaticReference (label <> " is not a sequence node")

expectRepetition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceStaticReferenceError
      [GrammarV1ReferenceParseTree]
expectRepetition label tree = case tree of
  GrammarV1ReferenceRepetition items -> Right items
  _ -> failStaticReference (label <> " is not a repetition node")

expectLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticReferenceError ()
expectLiteral expected tree = case tree of
  GrammarV1ReferenceLiteral actual
    | actual == expected -> Right ()
    | otherwise -> failStaticReference
        ("expected literal " <> expected <> ", got " <> actual)
  _ -> failStaticReference ("expected literal " <> expected)

mapTypeError
  :: Either GrammarV1ReferenceTypeAliasError a
  -> Either GrammarV1ReferenceStaticReferenceError a
mapTypeError = mapLeft (GrammarV1ReferenceStaticReferenceError . Text.pack . show)

mapTopLevelError
  :: Show e
  => Either e a
  -> Either GrammarV1ReferenceStaticReferenceError a
mapTopLevelError = mapLeft (GrammarV1ReferenceStaticReferenceError . Text.pack . show)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value

showText :: Show a => a -> Text
showText = Text.pack . show

failStaticReference
  :: Text
  -> Either GrammarV1ReferenceStaticReferenceError a
failStaticReference = Left . GrammarV1ReferenceStaticReferenceError
