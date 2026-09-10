{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstEffects
  ( GrammarV1ReferenceEffectsError (..)
  , GrammarV1ReferenceEffectSpine (..)
  , GrammarV1ReferenceEffectSetSpine (..)
  , grammarV1ProductionEffectSetSpine
  , grammarV1ReferenceEffectSetSpine
  , grammarV1ProductionTypeAliasEffectSets
  , grammarV1ReferenceTypeAliasEffectSets
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Declaration (..)
  , GrammarV1EffectExpression (..)
  , GrammarV1EffectSetExpression (..)
  , GrammarV1GenericRequirement (..)
  , GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..)
  , GrammarV1TypeAliasDecl (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstExpressionCore
  ( GrammarV1ReferenceExpressionCore
  , GrammarV1ReferenceExpressionCoreError
  , grammarV1ProductionExpressionCore
  , grammarV1ReferenceExpressionCore
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

newtype GrammarV1ReferenceEffectsError =
  GrammarV1ReferenceEffectsError Text
  deriving (Eq, Show)

data GrammarV1ReferenceEffectSpine = GrammarV1ReferenceEffectSpine
  { grammarV1ReferenceEffectReference :: GrammarV1ReferenceStaticReferenceSpine
  , grammarV1ReferenceEffectArguments :: [GrammarV1ReferenceExpressionCore]
  }
  deriving (Eq, Show)

data GrammarV1ReferenceEffectSetSpine
  = GrammarV1ReferenceEffectSetLiteral [GrammarV1ReferenceEffectSpine]
  | GrammarV1ReferenceEffectSetReference GrammarV1ReferenceStaticReferenceSpine
  deriving (Eq, Show)

grammarV1ProductionEffectSetSpine
  :: GrammarV1EffectSetExpression
  -> GrammarV1ReferenceEffectSetSpine
grammarV1ProductionEffectSetSpine effectSet = case effectSet of
  GrammarV1EffectSetLiteral effects ->
    GrammarV1ReferenceEffectSetLiteral
      (map (productionEffect . locatedValue) effects)
  GrammarV1EffectSetReference reference ->
    GrammarV1ReferenceEffectSetReference
      (grammarV1ProductionStaticReferenceSpine (locatedValue reference))

productionEffect
  :: GrammarV1EffectExpression
  -> GrammarV1ReferenceEffectSpine
productionEffect effect = GrammarV1ReferenceEffectSpine
  { grammarV1ReferenceEffectReference =
      grammarV1ProductionStaticReferenceSpine
        (locatedValue (grammarV1EffectReference effect))
  , grammarV1ReferenceEffectArguments =
      map (grammarV1ProductionExpressionCore . locatedValue)
        (grammarV1EffectArguments effect)
  }

grammarV1ReferenceEffectSetSpine
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceEffectsError GrammarV1ReferenceEffectSetSpine
grammarV1ReferenceEffectSetSpine tree = do
  body <- expectNonterminal "effect_set_expression" tree
  case body of
    GrammarV1ReferenceAlternative 0 literalTree ->
      parseEffectSetLiteral literalTree
    GrammarV1ReferenceAlternative 1 referenceTree ->
      GrammarV1ReferenceEffectSetReference
        <$> mapStaticReferenceError
              (grammarV1ReferenceStaticReferenceSpine referenceTree)
    GrammarV1ReferenceAlternative index _ ->
      failEffects ("effect_set_expression alternative out of range: " <> showText index)
    _ -> failEffects "effect_set_expression body is not an alternative node"

parseEffectSetLiteral
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceEffectsError GrammarV1ReferenceEffectSetSpine
parseEffectSetLiteral tree = do
  body <- expectNonterminal "effect_set_literal" tree
  fields <- expectSequence "effect_set_literal" body
  case fields of
    [openBrace, optionalEffects, closeBrace] -> do
      expectLiteral "{" openBrace
      effects <- parseOptionalEffects optionalEffects
      expectLiteral "}" closeBrace
      pure (GrammarV1ReferenceEffectSetLiteral effects)
    _ -> failEffects "effect_set_literal body is not a three-item sequence"

parseOptionalEffects
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceEffectsError [GrammarV1ReferenceEffectSpine]
parseOptionalEffects tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure []
  GrammarV1ReferenceOptionalSome valuesTree -> do
    fields <- expectSequence "effect_set_literal values" valuesTree
    case fields of
      [firstTree, restTree] -> do
        first <- parseEffectExpression firstTree
        suffixes <- expectRepetition "effect_set_literal suffix" restTree
        rest <- traverse parseEffectSuffix suffixes
        pure (first : rest)
      _ -> failEffects "effect_set_literal values are not a two-item sequence"
  _ -> failEffects "effect_set_literal values slot is not optional"

parseEffectSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceEffectsError GrammarV1ReferenceEffectSpine
parseEffectSuffix tree = do
  fields <- expectSequence "effect_set_literal suffix" tree
  case fields of
    [comma, effectTree] -> do
      expectLiteral "," comma
      parseEffectExpression effectTree
    _ -> failEffects "effect_set_literal suffix is not a two-item sequence"

parseEffectExpression
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceEffectsError GrammarV1ReferenceEffectSpine
parseEffectExpression tree = do
  body <- expectNonterminal "effect_expression" tree
  fields <- expectSequence "effect_expression" body
  case fields of
    [referenceTree, optionalArguments] -> do
      reference <- mapStaticReferenceError
        (grammarV1ReferenceStaticReferenceSpine referenceTree)
      arguments <- parseOptionalTermArguments optionalArguments
      pure GrammarV1ReferenceEffectSpine
        { grammarV1ReferenceEffectReference = reference
        , grammarV1ReferenceEffectArguments = arguments
        }
    _ -> failEffects "effect_expression body is not a two-item sequence"

parseOptionalTermArguments
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceEffectsError [GrammarV1ReferenceExpressionCore]
parseOptionalTermArguments tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure []
  GrammarV1ReferenceOptionalSome argumentsTree -> parseTermArguments argumentsTree
  _ -> failEffects "effect_expression argument slot is not optional"

parseTermArguments
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceEffectsError [GrammarV1ReferenceExpressionCore]
parseTermArguments tree = do
  body <- expectNonterminal "term_arguments" tree
  fields <- expectSequence "term_arguments" body
  case fields of
    [openParen, optionalValues, closeParen] -> do
      expectLiteral "(" openParen
      values <- case optionalValues of
        GrammarV1ReferenceOptionalNone -> pure []
        GrammarV1ReferenceOptionalSome valuesTree -> do
          valueFields <- expectSequence "term_arguments values" valuesTree
          case valueFields of
            [firstTree, restTree] -> do
              first <- mapExpressionError
                (grammarV1ReferenceExpressionCore firstTree)
              suffixes <- expectRepetition "term_arguments suffix" restTree
              rest <- traverse parseTermArgumentSuffix suffixes
              pure (first : rest)
            _ -> failEffects "term_arguments values are not a two-item sequence"
        _ -> failEffects "term_arguments values slot is not optional"
      expectLiteral ")" closeParen
      pure values
    _ -> failEffects "term_arguments body is not a three-item sequence"

parseTermArgumentSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceEffectsError GrammarV1ReferenceExpressionCore
parseTermArgumentSuffix tree = do
  fields <- expectSequence "term_arguments suffix" tree
  case fields of
    [comma, expressionTree] -> do
      expectLiteral "," comma
      mapExpressionError (grammarV1ReferenceExpressionCore expressionTree)
    _ -> failEffects "term_arguments suffix is not a two-item sequence"

grammarV1ProductionTypeAliasEffectSets
  :: GrammarV1SourceFile
  -> [[GrammarV1ReferenceEffectSetSpine]]
grammarV1ProductionTypeAliasEffectSets sourceFile =
  [ [ grammarV1ProductionEffectSetSpine (locatedValue effects)
    | locatedRequirement <- grammarV1TypeAliasRequirements alias
    , GrammarV1EffectsRequirement _ effects <- [locatedValue locatedRequirement]
    ]
  | locatedTopLevel <- grammarV1TopLevelDecls sourceFile
  , let topLevel = locatedValue locatedTopLevel
  , GrammarV1TypeAliasDeclaration alias <-
      [locatedValue (grammarV1Declaration topLevel)]
  ]

grammarV1ReferenceTypeAliasEffectSets
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceEffectsError [[GrammarV1ReferenceEffectSetSpine]]
grammarV1ReferenceTypeAliasEffectSets tree = do
  sourceBody <- expectNonterminal "source_file" tree
  sourceFields <- expectSequence "source_file" sourceBody
  case sourceFields of
    [_moduleTree, _importTree, topLevelTree] -> do
      topLevels <- expectRepetition "source_file top levels" topLevelTree
      values <- traverse parseTopLevelTypeAliasEffects topLevels
      pure [value | Just value <- values]
    _ -> failEffects "source_file body is not a three-item sequence"

parseTopLevelTypeAliasEffects
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceEffectsError (Maybe [GrammarV1ReferenceEffectSetSpine])
parseTopLevelTypeAliasEffects tree = do
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
              Just <$> parseTypeAliasEffects selected
            _ -> failEffects "type-alias declaration does not occupy alternative 2"
        _ -> pure Nothing
    _ -> failEffects "top_level_decl body is not a two-item sequence"

parseTypeAliasEffects
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceEffectsError [GrammarV1ReferenceEffectSetSpine]
parseTypeAliasEffects tree = do
  body <- expectNonterminal "type_alias_decl" tree
  fields <- expectSequence "type_alias_decl" body
  case fields of
    [_keyword, _name, _generic, requirementsTree, _equals, _target, _terminator] ->
      parseOptionalGenericRequirementEffects requirementsTree
    _ -> failEffects "type_alias_decl body is not a seven-item sequence"

parseOptionalGenericRequirementEffects
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceEffectsError [GrammarV1ReferenceEffectSetSpine]
parseOptionalGenericRequirementEffects tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure []
  GrammarV1ReferenceOptionalSome requirementsTree -> do
    body <- expectNonterminal "generic_requirements" requirementsTree
    fields <- expectSequence "generic_requirements" body
    case fields of
      [requiresKeyword, openBrace, entriesTree, closeBrace] -> do
        expectLiteral "requires" requiresKeyword
        expectLiteral "{" openBrace
        entries <- expectRepetition "generic_requirements entries" entriesTree
        values <- traverse parseGenericRequirementEffect entries
        expectLiteral "}" closeBrace
        pure [value | Just value <- values]
      _ -> failEffects "generic_requirements body is not a four-item sequence"
  _ -> failEffects "type_alias_decl requirement slot is not optional"

parseGenericRequirementEffect
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceEffectsError (Maybe GrammarV1ReferenceEffectSetSpine)
parseGenericRequirementEffect tree = do
  body <- expectNonterminal "generic_requirement" tree
  case body of
    GrammarV1ReferenceAlternative 6 selected -> do
      fields <- expectSequence "effects generic requirement" selected
      case fields of
        [effectsKeyword, _nameTree, withinKeyword, effectSetTree, terminator] -> do
          expectLiteral "effects" effectsKeyword
          expectLiteral "within" withinKeyword
          value <- grammarV1ReferenceEffectSetSpine effectSetTree
          expectLiteral ";" terminator
          pure (Just value)
        _ -> failEffects "effects generic requirement is not a five-item sequence"
    GrammarV1ReferenceAlternative index _
      | index >= 0 && index <= 12 -> pure Nothing
      | otherwise -> failEffects
          ("generic_requirement alternative out of range: " <> showText index)
    _ -> failEffects "generic_requirement body is not an alternative node"

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceEffectsError GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> pure body
    | otherwise -> failEffects
        ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failEffects ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceEffectsError [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence values -> pure values
  _ -> failEffects (label <> " is not a sequence node")

expectRepetition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceEffectsError [GrammarV1ReferenceParseTree]
expectRepetition label tree = case tree of
  GrammarV1ReferenceRepetition values -> pure values
  _ -> failEffects (label <> " is not a repetition node")

expectLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceEffectsError ()
expectLiteral expected tree = case tree of
  GrammarV1ReferenceLiteral actual
    | actual == expected -> pure ()
    | otherwise -> failEffects
        ("expected literal " <> expected <> ", got " <> actual)
  _ -> failEffects ("expected literal " <> expected)

mapExpressionError
  :: Either GrammarV1ReferenceExpressionCoreError a
  -> Either GrammarV1ReferenceEffectsError a
mapExpressionError = mapLeft
  (GrammarV1ReferenceEffectsError . Text.pack . show)

mapStaticReferenceError
  :: Either GrammarV1ReferenceStaticReferenceError a
  -> Either GrammarV1ReferenceEffectsError a
mapStaticReferenceError = mapLeft
  (GrammarV1ReferenceEffectsError . Text.pack . show)

mapTopLevelError
  :: Show e
  => Either e a
  -> Either GrammarV1ReferenceEffectsError a
mapTopLevelError = mapLeft
  (GrammarV1ReferenceEffectsError . Text.pack . show)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value

showText :: Show a => a -> Text
showText = Text.pack . show

failEffects :: Text -> Either GrammarV1ReferenceEffectsError a
failEffects = Left . GrammarV1ReferenceEffectsError
