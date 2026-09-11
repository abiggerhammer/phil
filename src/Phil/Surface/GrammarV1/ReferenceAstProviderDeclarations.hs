{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstProviderDeclarations
  ( GrammarV1ReferenceProviderDeclarationError (..)
  , GrammarV1ReferenceProviderContractItemCore (..)
  , GrammarV1ReferenceProviderImplementationItemCore (..)
  , GrammarV1ReferenceProviderDeclaration (..)
  , grammarV1ProductionProviderDeclaration
  , grammarV1ReferenceProviderDeclaration
  , grammarV1ProductionProviderDeclarations
  , grammarV1ReferenceProviderDeclarations
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Declaration (..)
  , GrammarV1OpaqueProviderImplementationDecl (..)
  , GrammarV1ProviderContractDecl (..)
  , GrammarV1ProviderContractItem (..)
  , GrammarV1ProviderImplementationDecl (..)
  , GrammarV1ProviderImplementationItem (..)
  , GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstBlockStructure
  ( GrammarV1ReferenceBlockCore
  , grammarV1ProductionBlockCore
  , grammarV1ReferenceBlockCore
  )
import Phil.Surface.GrammarV1.ReferenceAstDeclarationCommon
  ( GrammarV1ReferenceGenericParamCore
  , GrammarV1ReferenceRequirementCore
  , grammarV1ProductionGenericParamCore
  , grammarV1ProductionRequirementCore
  , grammarV1ReferenceIdentifierCore
  , grammarV1ReferenceOptionalGenericParamsCore
  , grammarV1ReferenceOptionalRequirementsCore
  )
import Phil.Surface.GrammarV1.ReferenceAstProposition
  ( GrammarV1ReferencePropositionCore
  , grammarV1ProductionPropositionCore
  , grammarV1ReferencePropositionCore
  )
import Phil.Surface.GrammarV1.ReferenceAstTypePayload
  ( GrammarV1ReferenceTypePayload
  , grammarV1ProductionTypePayload
  , grammarV1ReferenceTypePayload
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( GrammarV1ReferenceParseTree (..)
  )
import Phil.Surface.Syntax (Located (..))

newtype GrammarV1ReferenceProviderDeclarationError =
  GrammarV1ReferenceProviderDeclarationError Text
  deriving (Eq, Show)

data GrammarV1ReferenceProviderContractItemCore
  = GrammarV1ReferenceProviderContractOperation Text GrammarV1ReferenceTypePayload
  | GrammarV1ReferenceProviderContractLaw Text GrammarV1ReferencePropositionCore
  | GrammarV1ReferenceProviderContractLifecycle Text GrammarV1ReferencePropositionCore
  deriving (Eq, Show)

data GrammarV1ReferenceProviderImplementationItemCore
  = GrammarV1ReferenceProviderImplementationOperation
      Text GrammarV1ReferenceTypePayload GrammarV1ReferenceBlockCore
  | GrammarV1ReferenceProviderImplementationLaw Text GrammarV1ReferencePropositionCore
  | GrammarV1ReferenceProviderImplementationLifecycle Text GrammarV1ReferencePropositionCore
  deriving (Eq, Show)

data GrammarV1ReferenceProviderDeclaration
  = GrammarV1ReferenceProviderContractDeclaration
      Text
      [GrammarV1ReferenceGenericParamCore]
      [GrammarV1ReferenceRequirementCore]
      [GrammarV1ReferenceProviderContractItemCore]
  | GrammarV1ReferenceProviderImplementationDeclaration
      Text
      [GrammarV1ReferenceGenericParamCore]
      [GrammarV1ReferenceRequirementCore]
      GrammarV1ReferenceTypePayload
      [GrammarV1ReferenceProviderImplementationItemCore]
  | GrammarV1ReferenceOpaqueProviderImplementationDeclaration
      Text
      [GrammarV1ReferenceGenericParamCore]
      [GrammarV1ReferenceRequirementCore]
      GrammarV1ReferenceTypePayload
  deriving (Eq, Show)

grammarV1ProductionProviderDeclaration
  :: GrammarV1Declaration
  -> Maybe GrammarV1ReferenceProviderDeclaration
grammarV1ProductionProviderDeclaration declaration = case declaration of
  GrammarV1ProviderContractDeclaration value ->
    Just (productionContract value)
  GrammarV1ProviderImplementationDeclaration value ->
    Just (productionImplementation value)
  GrammarV1OpaqueProviderImplementationDeclaration value ->
    Just (productionOpaqueImplementation value)
  _ -> Nothing

productionContract
  :: GrammarV1ProviderContractDecl
  -> GrammarV1ReferenceProviderDeclaration
productionContract value = GrammarV1ReferenceProviderContractDeclaration
  (locatedValue (grammarV1ProviderContractName value))
  (map (grammarV1ProductionGenericParamCore . locatedValue)
    (grammarV1ProviderContractGenericParams value))
  (map (grammarV1ProductionRequirementCore . locatedValue)
    (grammarV1ProviderContractRequirements value))
  (map (productionContractItem . locatedValue)
    (grammarV1ProviderContractItems value))

productionContractItem
  :: GrammarV1ProviderContractItem
  -> GrammarV1ReferenceProviderContractItemCore
productionContractItem item = case item of
  GrammarV1ProviderContractOperation name sourceType ->
    GrammarV1ReferenceProviderContractOperation
      (locatedValue name)
      (grammarV1ProductionTypePayload (locatedValue sourceType))
  GrammarV1ProviderContractLaw name proposition ->
    GrammarV1ReferenceProviderContractLaw
      (locatedValue name)
      (grammarV1ProductionPropositionCore (locatedValue proposition))
  GrammarV1ProviderContractLifecycle name proposition ->
    GrammarV1ReferenceProviderContractLifecycle
      (locatedValue name)
      (grammarV1ProductionPropositionCore (locatedValue proposition))

productionImplementation
  :: GrammarV1ProviderImplementationDecl
  -> GrammarV1ReferenceProviderDeclaration
productionImplementation value = GrammarV1ReferenceProviderImplementationDeclaration
  (locatedValue (grammarV1ProviderImplementationName value))
  (map (grammarV1ProductionGenericParamCore . locatedValue)
    (grammarV1ProviderImplementationGenericParams value))
  (map (grammarV1ProductionRequirementCore . locatedValue)
    (grammarV1ProviderImplementationRequirements value))
  (grammarV1ProductionTypePayload
    (locatedValue (grammarV1ProviderImplementationSatisfies value)))
  (map (productionImplementationItem . locatedValue)
    (grammarV1ProviderImplementationItems value))

productionImplementationItem
  :: GrammarV1ProviderImplementationItem
  -> GrammarV1ReferenceProviderImplementationItemCore
productionImplementationItem item = case item of
  GrammarV1ProviderImplementationOperation name sourceType block ->
    GrammarV1ReferenceProviderImplementationOperation
      (locatedValue name)
      (grammarV1ProductionTypePayload (locatedValue sourceType))
      (grammarV1ProductionBlockCore (locatedValue block))
  GrammarV1ProviderImplementationLaw name proposition ->
    GrammarV1ReferenceProviderImplementationLaw
      (locatedValue name)
      (grammarV1ProductionPropositionCore (locatedValue proposition))
  GrammarV1ProviderImplementationLifecycle name proposition ->
    GrammarV1ReferenceProviderImplementationLifecycle
      (locatedValue name)
      (grammarV1ProductionPropositionCore (locatedValue proposition))

productionOpaqueImplementation
  :: GrammarV1OpaqueProviderImplementationDecl
  -> GrammarV1ReferenceProviderDeclaration
productionOpaqueImplementation value =
  GrammarV1ReferenceOpaqueProviderImplementationDeclaration
    (locatedValue (grammarV1OpaqueProviderImplementationName value))
    (map (grammarV1ProductionGenericParamCore . locatedValue)
      (grammarV1OpaqueProviderImplementationGenericParams value))
    (map (grammarV1ProductionRequirementCore . locatedValue)
      (grammarV1OpaqueProviderImplementationRequirements value))
    (grammarV1ProductionTypePayload
      (locatedValue (grammarV1OpaqueProviderImplementationSatisfies value)))

grammarV1ReferenceProviderDeclaration
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceProviderDeclarationError
      (Maybe GrammarV1ReferenceProviderDeclaration)
grammarV1ReferenceProviderDeclaration tree = do
  body <- expectNonterminal "declaration" tree
  case body of
    GrammarV1ReferenceAlternative 6 selected -> Just <$> parseContract selected
    GrammarV1ReferenceAlternative 7 selected -> Just <$> parseImplementation selected
    GrammarV1ReferenceAlternative 8 selected -> Just <$> parseOpaqueImplementation selected
    GrammarV1ReferenceAlternative index _
      | index >= 0 && index <= 14 -> pure Nothing
      | otherwise -> failProvider
          ("declaration alternative out of range: " <> showText index)
    _ -> failProvider "declaration body is not an alternative node"

parseContract
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceProviderDeclarationError
      GrammarV1ReferenceProviderDeclaration
parseContract tree = do
  fields <- namedSequence "provider_contract_decl" tree
  case fields of
    [keyword, nameTree, genericTree, requirementsTree, openBrace, itemsTree, closeBrace] -> do
      expectLiteral "provider" keyword
      name <- mapCommon (grammarV1ReferenceIdentifierCore nameTree)
      genericParams <- mapCommon
        (grammarV1ReferenceOptionalGenericParamsCore genericTree)
      requirements <- mapCommon
        (grammarV1ReferenceOptionalRequirementsCore requirementsTree)
      expectLiteral "{" openBrace
      items <- expectRepetition "provider contract items" itemsTree
        >>= traverse parseContractItem
      expectLiteral "}" closeBrace
      pure (GrammarV1ReferenceProviderContractDeclaration
        name genericParams requirements items)
    _ -> failProvider "provider_contract_decl body is not a seven-item sequence"

parseContractItem
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceProviderDeclarationError
      GrammarV1ReferenceProviderContractItemCore
parseContractItem tree = do
  body <- expectNonterminal "provider_contract_item" tree
  case body of
    GrammarV1ReferenceAlternative 0 selected -> do
      fields <- expectSequence "provider contract operation" selected
      case fields of
        [keyword, nameTree, colon, typeTree, terminator] -> do
          expectLiteral "operation" keyword
          name <- mapCommon (grammarV1ReferenceIdentifierCore nameTree)
          expectLiteral ":" colon
          sourceType <- mapType (grammarV1ReferenceTypePayload typeTree)
          expectLiteral ";" terminator
          pure (GrammarV1ReferenceProviderContractOperation name sourceType)
        _ -> failProvider "provider contract operation is not a five-item sequence"
    GrammarV1ReferenceAlternative 1 selected ->
      parseNamedPropositionItem
        "provider contract law" "law" GrammarV1ReferenceProviderContractLaw selected
    GrammarV1ReferenceAlternative 2 selected ->
      parseNamedPropositionItem
        "provider contract lifecycle" "lifecycle"
        GrammarV1ReferenceProviderContractLifecycle selected
    GrammarV1ReferenceAlternative index _ ->
      failProvider ("provider_contract_item alternative out of range: " <> showText index)
    _ -> failProvider "provider_contract_item body is not an alternative node"

parseImplementation
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceProviderDeclarationError
      GrammarV1ReferenceProviderDeclaration
parseImplementation tree = do
  fields <- namedSequence "provider_implementation_decl" tree
  case fields of
    [providerKeyword, implementationKeyword, nameTree, genericTree,
      requirementsTree, satisfiesKeyword, typeTree, openBrace, itemsTree, closeBrace] -> do
      expectLiteral "provider" providerKeyword
      expectLiteral "implementation" implementationKeyword
      name <- mapCommon (grammarV1ReferenceIdentifierCore nameTree)
      genericParams <- mapCommon
        (grammarV1ReferenceOptionalGenericParamsCore genericTree)
      requirements <- mapCommon
        (grammarV1ReferenceOptionalRequirementsCore requirementsTree)
      expectLiteral "satisfies" satisfiesKeyword
      sourceType <- mapType (grammarV1ReferenceTypePayload typeTree)
      expectLiteral "{" openBrace
      items <- expectRepetition "provider implementation items" itemsTree
        >>= traverse parseImplementationItem
      expectLiteral "}" closeBrace
      pure (GrammarV1ReferenceProviderImplementationDeclaration
        name genericParams requirements sourceType items)
    _ -> failProvider
      "provider_implementation_decl body is not a ten-item sequence"

parseImplementationItem
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceProviderDeclarationError
      GrammarV1ReferenceProviderImplementationItemCore
parseImplementationItem tree = do
  body <- expectNonterminal "provider_implementation_item" tree
  case body of
    GrammarV1ReferenceAlternative 0 selected -> do
      fields <- expectSequence "provider implementation operation" selected
      case fields of
        [keyword, nameTree, satisfiesKeyword, typeTree, blockTree] -> do
          expectLiteral "operation" keyword
          name <- mapCommon (grammarV1ReferenceIdentifierCore nameTree)
          expectLiteral "satisfies" satisfiesKeyword
          sourceType <- mapType (grammarV1ReferenceTypePayload typeTree)
          block <- mapBlock (grammarV1ReferenceBlockCore blockTree)
          pure (GrammarV1ReferenceProviderImplementationOperation
            name sourceType block)
        _ -> failProvider
          "provider implementation operation is not a five-item sequence"
    GrammarV1ReferenceAlternative 1 selected ->
      parseNamedAssignedPropositionItem
        "provider implementation law" "law"
        GrammarV1ReferenceProviderImplementationLaw selected
    GrammarV1ReferenceAlternative 2 selected ->
      parseNamedAssignedPropositionItem
        "provider implementation lifecycle" "lifecycle"
        GrammarV1ReferenceProviderImplementationLifecycle selected
    GrammarV1ReferenceAlternative index _ ->
      failProvider
        ("provider_implementation_item alternative out of range: " <> showText index)
    _ -> failProvider "provider_implementation_item body is not an alternative node"

parseOpaqueImplementation
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceProviderDeclarationError
      GrammarV1ReferenceProviderDeclaration
parseOpaqueImplementation tree = do
  fields <- namedSequence "opaque_provider_implementation_decl" tree
  case fields of
    [opaqueKeyword, providerKeyword, implementationKeyword, nameTree,
      genericTree, requirementsTree, satisfiesKeyword, typeTree, terminator] -> do
      expectLiteral "opaque" opaqueKeyword
      expectLiteral "provider" providerKeyword
      expectLiteral "implementation" implementationKeyword
      name <- mapCommon (grammarV1ReferenceIdentifierCore nameTree)
      genericParams <- mapCommon
        (grammarV1ReferenceOptionalGenericParamsCore genericTree)
      requirements <- mapCommon
        (grammarV1ReferenceOptionalRequirementsCore requirementsTree)
      expectLiteral "satisfies" satisfiesKeyword
      sourceType <- mapType (grammarV1ReferenceTypePayload typeTree)
      expectLiteral ";" terminator
      pure (GrammarV1ReferenceOpaqueProviderImplementationDeclaration
        name genericParams requirements sourceType)
    _ -> failProvider
      "opaque_provider_implementation_decl body is not a nine-item sequence"

parseNamedPropositionItem
  :: Text
  -> Text
  -> (Text -> GrammarV1ReferencePropositionCore -> a)
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceProviderDeclarationError a
parseNamedPropositionItem label keyword constructor tree = do
  fields <- expectSequence label tree
  case fields of
    [keywordTree, nameTree, colon, propositionTree, terminator] -> do
      expectLiteral keyword keywordTree
      name <- mapCommon (grammarV1ReferenceIdentifierCore nameTree)
      expectLiteral ":" colon
      proposition <- mapProp (grammarV1ReferencePropositionCore propositionTree)
      expectLiteral ";" terminator
      pure (constructor name proposition)
    _ -> failProvider (label <> " is not a five-item sequence")

parseNamedAssignedPropositionItem
  :: Text
  -> Text
  -> (Text -> GrammarV1ReferencePropositionCore -> a)
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceProviderDeclarationError a
parseNamedAssignedPropositionItem label keyword constructor tree = do
  fields <- expectSequence label tree
  case fields of
    [keywordTree, nameTree, equalsSign, propositionTree, terminator] -> do
      expectLiteral keyword keywordTree
      name <- mapCommon (grammarV1ReferenceIdentifierCore nameTree)
      expectLiteral "=" equalsSign
      proposition <- mapProp (grammarV1ReferencePropositionCore propositionTree)
      expectLiteral ";" terminator
      pure (constructor name proposition)
    _ -> failProvider (label <> " is not a five-item sequence")

grammarV1ProductionProviderDeclarations
  :: GrammarV1SourceFile
  -> [GrammarV1ReferenceProviderDeclaration]
grammarV1ProductionProviderDeclarations sourceFile =
  [ value
  | locatedTopLevel <- grammarV1TopLevelDecls sourceFile
  , let declaration = locatedValue (grammarV1Declaration (locatedValue locatedTopLevel))
  , Just value <- [grammarV1ProductionProviderDeclaration declaration]
  ]

grammarV1ReferenceProviderDeclarations
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceProviderDeclarationError
      [GrammarV1ReferenceProviderDeclaration]
grammarV1ReferenceProviderDeclarations tree = do
  body <- expectNonterminal "source_file" tree
  fields <- expectSequence "source_file" body
  case fields of
    [_moduleTree, _importsTree, topLevelsTree] -> do
      topLevels <- expectRepetition "source_file top levels" topLevelsTree
      values <- traverse parseTopLevel topLevels
      pure [value | Just value <- values]
    _ -> failProvider "source_file body is not a three-item sequence"
  where
    parseTopLevel topLevelTree = do
      topBody <- expectNonterminal "top_level_decl" topLevelTree
      topFields <- expectSequence "top_level_decl" topBody
      case topFields of
        [_attributesTree, declarationTree] ->
          grammarV1ReferenceProviderDeclaration declarationTree
        _ -> failProvider "top_level_decl body is not a two-item sequence"

namedSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceProviderDeclarationError [GrammarV1ReferenceParseTree]
namedSequence name tree = expectNonterminal name tree >>= expectSequence name

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceProviderDeclarationError GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> pure body
    | otherwise -> failProvider
        ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failProvider ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceProviderDeclarationError [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence values -> pure values
  _ -> failProvider (label <> " is not a sequence node")

expectRepetition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceProviderDeclarationError [GrammarV1ReferenceParseTree]
expectRepetition label tree = case tree of
  GrammarV1ReferenceRepetition values -> pure values
  _ -> failProvider (label <> " is not a repetition node")

expectLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceProviderDeclarationError ()
expectLiteral expected tree = case tree of
  GrammarV1ReferenceLiteral actual
    | actual == expected -> pure ()
    | otherwise -> failProvider
        ("expected literal " <> expected <> ", got " <> actual)
  _ -> failProvider ("expected literal " <> expected)

mapCommon :: Show e => Either e a -> Either GrammarV1ReferenceProviderDeclarationError a
mapCommon = mapNested "declaration-common"

mapType :: Show e => Either e a -> Either GrammarV1ReferenceProviderDeclarationError a
mapType = mapNested "type"

mapProp :: Show e => Either e a -> Either GrammarV1ReferenceProviderDeclarationError a
mapProp = mapNested "proposition"

mapBlock :: Show e => Either e a -> Either GrammarV1ReferenceProviderDeclarationError a
mapBlock = mapNested "block"

mapNested
  :: Show e
  => Text
  -> Either e a
  -> Either GrammarV1ReferenceProviderDeclarationError a
mapNested label result = case result of
  Left errorValue -> failProvider
    (label <> " correspondence failed: " <> Text.pack (show errorValue))
  Right value -> pure value

showText :: Show a => a -> Text
showText = Text.pack . show

failProvider
  :: Text
  -> Either GrammarV1ReferenceProviderDeclarationError a
failProvider = Left . GrammarV1ReferenceProviderDeclarationError
