{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstGenericRequirements
  ( GrammarV1ReferenceGenericRequirementError (..)
  , GrammarV1ReferenceEffectSetTag (..)
  , GrammarV1ReferenceGenericRequirementSpine (..)
  , grammarV1ProductionTypeAliasRequirementSpines
  , grammarV1ReferenceTypeAliasRequirementSpines
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Declaration (..)
  , GrammarV1EffectSetExpression (..)
  , GrammarV1GenericRequirement (..)
  , GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..)
  , GrammarV1TypeAliasDecl (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstTopLevel
  ( GrammarV1ReferenceDeclarationTag (..)
  , grammarV1ReferenceDeclarationTag
  )
import Phil.Surface.GrammarV1.ReferenceAstTypeAlias
  ( GrammarV1ReferenceTypeTag
  , grammarV1ProductionTypeTag
  , grammarV1ReferenceTypeTag
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( GrammarV1ReferenceParseTree (..)
  )
import Phil.Surface.Syntax (Located (..))

newtype GrammarV1ReferenceGenericRequirementError =
  GrammarV1ReferenceGenericRequirementError Text
  deriving (Eq, Show)

data GrammarV1ReferenceEffectSetTag
  = GrammarV1ReferenceEffectSetLiteral
  | GrammarV1ReferenceEffectSetReference
  deriving (Eq, Ord, Show)

data GrammarV1ReferenceGenericRequirementSpine
  = GrammarV1ReferenceStructuralRequirement Text Text
  | GrammarV1ReferencePropositionRequirement
  | GrammarV1ReferenceProviderRequirement Text GrammarV1ReferenceTypeTag
  | GrammarV1ReferenceCallableRequirement Text GrammarV1ReferenceTypeTag
  | GrammarV1ReferenceBoundaryRequirement Text GrammarV1ReferenceTypeTag
  | GrammarV1ReferenceArchitectureRequirement Text GrammarV1ReferenceTypeTag
  | GrammarV1ReferenceEffectsRequirement Text GrammarV1ReferenceEffectSetTag
  | GrammarV1ReferenceAuthorityRequirement GrammarV1ReferenceTypeTag
  | GrammarV1ReferenceBoundaryRepresentationRequirement GrammarV1ReferenceTypeTag
  | GrammarV1ReferenceRepresentationRequirement
  | GrammarV1ReferencePlacementRequirement
  | GrammarV1ReferenceCostRequirement
  | GrammarV1ReferenceEnvironmentRequirement
  deriving (Eq, Show)

grammarV1ProductionTypeAliasRequirementSpines
  :: GrammarV1SourceFile
  -> [[GrammarV1ReferenceGenericRequirementSpine]]
grammarV1ProductionTypeAliasRequirementSpines sourceFile =
  [ map (productionRequirement . locatedValue)
      (grammarV1TypeAliasRequirements alias)
  | locatedTopLevel <- grammarV1TopLevelDecls sourceFile
  , let topLevel = locatedValue locatedTopLevel
  , GrammarV1TypeAliasDeclaration alias <-
      [locatedValue (grammarV1Declaration topLevel)]
  ]

productionRequirement
  :: GrammarV1GenericRequirement
  -> GrammarV1ReferenceGenericRequirementSpine
productionRequirement requirement = case requirement of
  GrammarV1StructuralRequirement name required ->
    GrammarV1ReferenceStructuralRequirement
      (locatedValue name)
      (locatedValue required)
  GrammarV1PropositionRequirement _ ->
    GrammarV1ReferencePropositionRequirement
  GrammarV1ProviderRequirement name sourceType ->
    GrammarV1ReferenceProviderRequirement
      (locatedValue name)
      (grammarV1ProductionTypeTag (locatedValue sourceType))
  GrammarV1CallableRequirement name sourceType ->
    GrammarV1ReferenceCallableRequirement
      (locatedValue name)
      (grammarV1ProductionTypeTag (locatedValue sourceType))
  GrammarV1BoundaryRequirement name sourceType ->
    GrammarV1ReferenceBoundaryRequirement
      (locatedValue name)
      (grammarV1ProductionTypeTag (locatedValue sourceType))
  GrammarV1ArchitectureRequirement name sourceType ->
    GrammarV1ReferenceArchitectureRequirement
      (locatedValue name)
      (grammarV1ProductionTypeTag (locatedValue sourceType))
  GrammarV1EffectsRequirement name effects ->
    GrammarV1ReferenceEffectsRequirement
      (locatedValue name)
      (productionEffectSetTag (locatedValue effects))
  GrammarV1AuthorityRequirement sourceType ->
    GrammarV1ReferenceAuthorityRequirement
      (grammarV1ProductionTypeTag (locatedValue sourceType))
  GrammarV1BoundaryRepresentationRequirement sourceType ->
    GrammarV1ReferenceBoundaryRepresentationRequirement
      (grammarV1ProductionTypeTag (locatedValue sourceType))
  GrammarV1RepresentationRequirement _ ->
    GrammarV1ReferenceRepresentationRequirement
  GrammarV1PlacementRequirement _ ->
    GrammarV1ReferencePlacementRequirement
  GrammarV1CostRequirement _ ->
    GrammarV1ReferenceCostRequirement
  GrammarV1EnvironmentRequirement _ ->
    GrammarV1ReferenceEnvironmentRequirement

productionEffectSetTag
  :: GrammarV1EffectSetExpression
  -> GrammarV1ReferenceEffectSetTag
productionEffectSetTag effects = case effects of
  GrammarV1EffectSetLiteral _ -> GrammarV1ReferenceEffectSetLiteral
  GrammarV1EffectSetReference _ -> GrammarV1ReferenceEffectSetReference

grammarV1ReferenceTypeAliasRequirementSpines
  :: GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceGenericRequirementError
      [[GrammarV1ReferenceGenericRequirementSpine]]
grammarV1ReferenceTypeAliasRequirementSpines tree = do
  sourceBody <- expectNonterminal "source_file" tree
  sourceFields <- expectSequence "source_file" sourceBody
  case sourceFields of
    [_moduleTree, _importTree, topLevelTree] -> do
      topLevels <- expectRepetition "source_file top levels" topLevelTree
      values <- traverse parseTopLevelTypeAliasRequirements topLevels
      pure [value | Just value <- values]
    _ -> failRequirement "source_file body is not a three-item sequence"

parseTopLevelTypeAliasRequirements
  :: GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceGenericRequirementError
      (Maybe [GrammarV1ReferenceGenericRequirementSpine])
parseTopLevelTypeAliasRequirements tree = do
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
              Just <$> parseTypeAliasRequirements selected
            _ -> failRequirement
              "type-alias declaration does not occupy alternative 2"
        _ -> Right Nothing
    _ -> failRequirement "top_level_decl body is not a two-item sequence"

parseTypeAliasRequirements
  :: GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceGenericRequirementError
      [GrammarV1ReferenceGenericRequirementSpine]
parseTypeAliasRequirements tree = do
  body <- expectNonterminal "type_alias_decl" tree
  fields <- expectSequence "type_alias_decl" body
  case fields of
    [_typeKeyword, _nameTree, _genericTree, requirementTree, _equalsSign, _targetTree, _terminator] ->
      parseOptionalGenericRequirements requirementTree
    _ -> failRequirement "type_alias_decl body is not a seven-item sequence"

parseOptionalGenericRequirements
  :: GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceGenericRequirementError
      [GrammarV1ReferenceGenericRequirementSpine]
parseOptionalGenericRequirements tree = case tree of
  GrammarV1ReferenceOptionalNone -> Right []
  GrammarV1ReferenceOptionalSome requirementsTree -> do
    body <- expectNonterminal "generic_requirements" requirementsTree
    fields <- expectSequence "generic_requirements" body
    case fields of
      [requiresKeyword, openBrace, entriesTree, closeBrace] -> do
        expectLiteral "requires" requiresKeyword
        expectLiteral "{" openBrace
        entries <- expectRepetition "generic_requirements entries" entriesTree
        values <- traverse parseGenericRequirement entries
        expectLiteral "}" closeBrace
        pure values
      _ -> failRequirement
        "generic_requirements body is not a four-item sequence"
  _ -> failRequirement "type_alias_decl requirement slot is not optional"

parseGenericRequirement
  :: GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceGenericRequirementError
      GrammarV1ReferenceGenericRequirementSpine
parseGenericRequirement tree = do
  body <- expectNonterminal "generic_requirement" tree
  case body of
    GrammarV1ReferenceAlternative index selected -> case index of
      0 -> parseStructuralRequirement selected
      1 -> parsePropositionRequirement selected
      2 -> parseNamedTypeRequirement
        "provider"
        GrammarV1ReferenceProviderRequirement
        selected
      3 -> parseNamedTypeRequirement
        "callable"
        GrammarV1ReferenceCallableRequirement
        selected
      4 -> parseNamedTypeRequirement
        "boundary"
        GrammarV1ReferenceBoundaryRequirement
        selected
      5 -> parseNamedTypeRequirement
        "architecture"
        GrammarV1ReferenceArchitectureRequirement
        selected
      6 -> parseEffectsRequirement selected
      7 -> parseTypeOnlyRequirement
        "authority"
        GrammarV1ReferenceAuthorityRequirement
        selected
      8 -> parseBoundaryRepresentationRequirement selected
      9 -> parsePropositionOnlyRequirement
        "representation"
        GrammarV1ReferenceRepresentationRequirement
        selected
      10 -> parsePropositionOnlyRequirement
        "placement"
        GrammarV1ReferencePlacementRequirement
        selected
      11 -> parsePropositionOnlyRequirement
        "cost"
        GrammarV1ReferenceCostRequirement
        selected
      12 -> parsePropositionOnlyRequirement
        "environment"
        GrammarV1ReferenceEnvironmentRequirement
        selected
      _ -> failRequirement
        ("generic_requirement alternative out of range: " <> showText index)
    _ -> failRequirement "generic_requirement body is not an alternative node"

parseStructuralRequirement
  :: GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceGenericRequirementError
      GrammarV1ReferenceGenericRequirementSpine
parseStructuralRequirement tree = do
  fields <- expectSequence "structural requirement" tree
  case fields of
    [keyword, nameTree, colon, requiredTree, terminator] -> do
      expectLiteral "structural" keyword
      name <- parseIdentifier nameTree
      expectLiteral ":" colon
      required <- parseIdentifier requiredTree
      expectLiteral ";" terminator
      pure (GrammarV1ReferenceStructuralRequirement name required)
    _ -> failRequirement "structural requirement is not a five-item sequence"

parsePropositionRequirement
  :: GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceGenericRequirementError
      GrammarV1ReferenceGenericRequirementSpine
parsePropositionRequirement tree = do
  fields <- expectSequence "proposition requirement" tree
  case fields of
    [keyword, propositionTree, terminator] -> do
      expectLiteral "proposition" keyword
      expectNamedNode "proposition" propositionTree
      expectLiteral ";" terminator
      pure GrammarV1ReferencePropositionRequirement
    _ -> failRequirement "proposition requirement is not a three-item sequence"

parseNamedTypeRequirement
  :: Text
  -> (Text -> GrammarV1ReferenceTypeTag -> GrammarV1ReferenceGenericRequirementSpine)
  -> GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceGenericRequirementError
      GrammarV1ReferenceGenericRequirementSpine
parseNamedTypeRequirement keyword constructor tree = do
  fields <- expectSequence (keyword <> " requirement") tree
  case fields of
    [keywordTree, nameTree, colon, typeTree, terminator] -> do
      expectLiteral keyword keywordTree
      name <- parseIdentifier nameTree
      expectLiteral ":" colon
      typeTag <- mapTypeError (grammarV1ReferenceTypeTag typeTree)
      expectLiteral ";" terminator
      pure (constructor name typeTag)
    _ -> failRequirement (keyword <> " requirement is not a five-item sequence")

parseEffectsRequirement
  :: GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceGenericRequirementError
      GrammarV1ReferenceGenericRequirementSpine
parseEffectsRequirement tree = do
  fields <- expectSequence "effects requirement" tree
  case fields of
    [keyword, nameTree, withinKeyword, effectsTree, terminator] -> do
      expectLiteral "effects" keyword
      name <- parseIdentifier nameTree
      expectLiteral "within" withinKeyword
      effectTag <- parseEffectSetTag effectsTree
      expectLiteral ";" terminator
      pure (GrammarV1ReferenceEffectsRequirement name effectTag)
    _ -> failRequirement "effects requirement is not a five-item sequence"

parseEffectSetTag
  :: GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceGenericRequirementError
      GrammarV1ReferenceEffectSetTag
parseEffectSetTag tree = do
  body <- expectNonterminal "effect_set_expression" tree
  case body of
    GrammarV1ReferenceAlternative 0 selected -> do
      expectNamedNode "effect_set_literal" selected
      pure GrammarV1ReferenceEffectSetLiteral
    GrammarV1ReferenceAlternative 1 selected -> do
      expectNamedNode "static_reference" selected
      pure GrammarV1ReferenceEffectSetReference
    GrammarV1ReferenceAlternative index _ ->
      failRequirement
        ("effect_set_expression alternative out of range: " <> showText index)
    _ -> failRequirement "effect_set_expression body is not an alternative node"

parseTypeOnlyRequirement
  :: Text
  -> (GrammarV1ReferenceTypeTag -> GrammarV1ReferenceGenericRequirementSpine)
  -> GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceGenericRequirementError
      GrammarV1ReferenceGenericRequirementSpine
parseTypeOnlyRequirement keyword constructor tree = do
  fields <- expectSequence (keyword <> " requirement") tree
  case fields of
    [keywordTree, typeTree, terminator] -> do
      expectLiteral keyword keywordTree
      typeTag <- mapTypeError (grammarV1ReferenceTypeTag typeTree)
      expectLiteral ";" terminator
      pure (constructor typeTag)
    _ -> failRequirement (keyword <> " requirement is not a three-item sequence")

parseBoundaryRepresentationRequirement
  :: GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceGenericRequirementError
      GrammarV1ReferenceGenericRequirementSpine
parseBoundaryRepresentationRequirement tree = do
  fields <- expectSequence "boundary representation requirement" tree
  case fields of
    [boundaryKeyword, representationKeyword, typeTree, terminator] -> do
      expectLiteral "boundary" boundaryKeyword
      expectLiteral "representation" representationKeyword
      typeTag <- mapTypeError (grammarV1ReferenceTypeTag typeTree)
      expectLiteral ";" terminator
      pure (GrammarV1ReferenceBoundaryRepresentationRequirement typeTag)
    _ -> failRequirement
      "boundary representation requirement is not a four-item sequence"

parsePropositionOnlyRequirement
  :: Text
  -> GrammarV1ReferenceGenericRequirementSpine
  -> GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceGenericRequirementError
      GrammarV1ReferenceGenericRequirementSpine
parsePropositionOnlyRequirement keyword constructor tree = do
  fields <- expectSequence (keyword <> " requirement") tree
  case fields of
    [keywordTree, propositionTree, terminator] -> do
      expectLiteral keyword keywordTree
      expectNamedNode "proposition" propositionTree
      expectLiteral ";" terminator
      pure constructor
    _ -> failRequirement (keyword <> " requirement is not a three-item sequence")

parseIdentifier
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceGenericRequirementError Text
parseIdentifier tree = do
  body <- expectNonterminal "identifier" tree
  case body of
    GrammarV1ReferenceLexical "IDENTIFIER" value -> Right value
    GrammarV1ReferenceLexical className _ ->
      failRequirement ("identifier uses lexical class " <> className)
    _ -> failRequirement "identifier body is not an IDENTIFIER lexical leaf"

expectNamedNode
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceGenericRequirementError ()
expectNamedNode name tree = expectNonterminal name tree >> pure ()

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceGenericRequirementError
      GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> Right body
    | otherwise -> failRequirement
        ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failRequirement ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceGenericRequirementError
      [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence items -> Right items
  _ -> failRequirement (label <> " is not a sequence node")

expectRepetition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferenceGenericRequirementError
      [GrammarV1ReferenceParseTree]
expectRepetition label tree = case tree of
  GrammarV1ReferenceRepetition items -> Right items
  _ -> failRequirement (label <> " is not a repetition node")

expectLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceGenericRequirementError ()
expectLiteral expected tree = case tree of
  GrammarV1ReferenceLiteral actual
    | actual == expected -> Right ()
    | otherwise -> failRequirement
        ("expected literal " <> expected <> ", got " <> actual)
  _ -> failRequirement ("expected literal " <> expected)

mapTopLevelError
  :: Either e a
  -> Either GrammarV1ReferenceGenericRequirementError a
mapTopLevelError result = case result of
  Left _ -> failRequirement "declaration-tag correspondence failed"
  Right value -> Right value

mapTypeError
  :: Show e
  => Either e a
  -> Either GrammarV1ReferenceGenericRequirementError a
mapTypeError result = case result of
  Left errorValue -> failRequirement
    ("type correspondence failed: " <> Text.pack (show errorValue))
  Right value -> Right value

showText :: Show a => a -> Text
showText = Text.pack . show

failRequirement
  :: Text
  -> Either GrammarV1ReferenceGenericRequirementError a
failRequirement = Left . GrammarV1ReferenceGenericRequirementError
