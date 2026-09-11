{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstCapabilityBoundary
  ( GrammarV1ReferenceCapabilityBoundaryError (..)
  , GrammarV1ReferenceCapabilityItemCore (..)
  , GrammarV1ReferenceBoundaryItemCore (..)
  , GrammarV1ReferenceCapabilityBoundaryDeclaration (..)
  , grammarV1ProductionCapabilityBoundaryDeclaration
  , grammarV1ReferenceCapabilityBoundaryDeclaration
  , grammarV1ProductionCapabilityBoundaryDeclarations
  , grammarV1ReferenceCapabilityBoundaryDeclarations
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1BoundaryDecl (..)
  , GrammarV1BoundaryItem (..)
  , GrammarV1CapabilityDecl (..)
  , GrammarV1CapabilityItem (..)
  , GrammarV1Declaration (..)
  , GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstDeclarationCommon
  ( GrammarV1ReferenceGenericParamCore
  , GrammarV1ReferenceRequirementCore
  , GrammarV1ReferenceStructuralModeCore
  , grammarV1ProductionGenericParamCore
  , grammarV1ProductionRequirementCore
  , grammarV1ProductionStructuralModeCore
  , grammarV1ReferenceIdentifierCore
  , grammarV1ReferenceOptionalGenericParamsCore
  , grammarV1ReferenceOptionalRequirementsCore
  , grammarV1ReferenceStructuralModeCore
  )
import Phil.Surface.GrammarV1.ReferenceAstProposition
  ( GrammarV1ReferencePropositionCore
  , grammarV1ProductionPropositionCore
  , grammarV1ReferencePropositionCore
  )
import Phil.Surface.GrammarV1.ReferenceAstStaticReference
  ( GrammarV1ReferenceStaticReferenceSpine
  , grammarV1ProductionStaticReferenceSpine
  , grammarV1ReferenceStaticReferenceSpine
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

newtype GrammarV1ReferenceCapabilityBoundaryError =
  GrammarV1ReferenceCapabilityBoundaryError Text
  deriving (Eq, Show)

data GrammarV1ReferenceCapabilityItemCore
  = GrammarV1ReferenceCapabilityPermits GrammarV1ReferenceStaticReferenceSpine
  | GrammarV1ReferenceCapabilityRequires GrammarV1ReferencePropositionCore
  | GrammarV1ReferenceCapabilityLaw Text GrammarV1ReferencePropositionCore
  deriving (Eq, Show)

data GrammarV1ReferenceBoundaryItemCore
  = GrammarV1ReferenceBoundaryReceive GrammarV1ReferenceStaticReferenceSpine
  | GrammarV1ReferenceBoundarySend GrammarV1ReferenceStaticReferenceSpine
  | GrammarV1ReferenceBoundaryCorrespondence GrammarV1ReferencePropositionCore
  | GrammarV1ReferenceBoundaryCanonical
  | GrammarV1ReferenceBoundaryFailure GrammarV1ReferenceTypePayload
  | GrammarV1ReferenceBoundaryLaw Text GrammarV1ReferencePropositionCore
  deriving (Eq, Show)

data GrammarV1ReferenceCapabilityBoundaryDeclaration
  = GrammarV1ReferenceCapabilityDeclaration
      Text
      [GrammarV1ReferenceGenericParamCore]
      GrammarV1ReferenceStructuralModeCore
      [GrammarV1ReferenceRequirementCore]
      [GrammarV1ReferenceCapabilityItemCore]
  | GrammarV1ReferenceBoundaryDeclaration
      Text
      [GrammarV1ReferenceGenericParamCore]
      [GrammarV1ReferenceRequirementCore]
      GrammarV1ReferenceTypePayload
      [GrammarV1ReferenceBoundaryItemCore]
  deriving (Eq, Show)

grammarV1ProductionCapabilityBoundaryDeclaration
  :: GrammarV1Declaration
  -> Maybe GrammarV1ReferenceCapabilityBoundaryDeclaration
grammarV1ProductionCapabilityBoundaryDeclaration declaration = case declaration of
  GrammarV1CapabilityDeclaration value -> Just (productionCapability value)
  GrammarV1BoundaryDeclaration value -> Just (productionBoundary value)
  _ -> Nothing

productionCapability
  :: GrammarV1CapabilityDecl
  -> GrammarV1ReferenceCapabilityBoundaryDeclaration
productionCapability value = GrammarV1ReferenceCapabilityDeclaration
  (locatedValue (grammarV1CapabilityName value))
  (map (grammarV1ProductionGenericParamCore . locatedValue)
    (grammarV1CapabilityGenericParams value))
  (grammarV1ProductionStructuralModeCore (grammarV1CapabilityMode value))
  (map (grammarV1ProductionRequirementCore . locatedValue)
    (grammarV1CapabilityRequirements value))
  (map (productionCapabilityItem . locatedValue)
    (grammarV1CapabilityItems value))

productionCapabilityItem
  :: GrammarV1CapabilityItem
  -> GrammarV1ReferenceCapabilityItemCore
productionCapabilityItem item = case item of
  GrammarV1CapabilityPermits reference ->
    GrammarV1ReferenceCapabilityPermits
      (grammarV1ProductionStaticReferenceSpine (locatedValue reference))
  GrammarV1CapabilityRequires proposition ->
    GrammarV1ReferenceCapabilityRequires
      (grammarV1ProductionPropositionCore (locatedValue proposition))
  GrammarV1CapabilityLaw name proposition ->
    GrammarV1ReferenceCapabilityLaw
      (locatedValue name)
      (grammarV1ProductionPropositionCore (locatedValue proposition))

productionBoundary
  :: GrammarV1BoundaryDecl
  -> GrammarV1ReferenceCapabilityBoundaryDeclaration
productionBoundary value = GrammarV1ReferenceBoundaryDeclaration
  (locatedValue (grammarV1BoundaryName value))
  (map (grammarV1ProductionGenericParamCore . locatedValue)
    (grammarV1BoundaryGenericParams value))
  (map (grammarV1ProductionRequirementCore . locatedValue)
    (grammarV1BoundaryRequirements value))
  (grammarV1ProductionTypePayload (locatedValue (grammarV1BoundaryType value)))
  (map (productionBoundaryItem . locatedValue) (grammarV1BoundaryItems value))

productionBoundaryItem
  :: GrammarV1BoundaryItem
  -> GrammarV1ReferenceBoundaryItemCore
productionBoundaryItem item = case item of
  GrammarV1BoundaryReceive reference ->
    GrammarV1ReferenceBoundaryReceive
      (grammarV1ProductionStaticReferenceSpine (locatedValue reference))
  GrammarV1BoundarySend reference ->
    GrammarV1ReferenceBoundarySend
      (grammarV1ProductionStaticReferenceSpine (locatedValue reference))
  GrammarV1BoundaryCorrespondence proposition ->
    GrammarV1ReferenceBoundaryCorrespondence
      (grammarV1ProductionPropositionCore (locatedValue proposition))
  GrammarV1BoundaryCanonical -> GrammarV1ReferenceBoundaryCanonical
  GrammarV1BoundaryFailure sourceType ->
    GrammarV1ReferenceBoundaryFailure
      (grammarV1ProductionTypePayload (locatedValue sourceType))
  GrammarV1BoundaryLaw name proposition ->
    GrammarV1ReferenceBoundaryLaw
      (locatedValue name)
      (grammarV1ProductionPropositionCore (locatedValue proposition))

grammarV1ReferenceCapabilityBoundaryDeclaration
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCapabilityBoundaryError
      (Maybe GrammarV1ReferenceCapabilityBoundaryDeclaration)
grammarV1ReferenceCapabilityBoundaryDeclaration tree = do
  body <- expectNonterminal "declaration" tree
  case body of
    GrammarV1ReferenceAlternative 10 selected -> Just <$> parseCapability selected
    GrammarV1ReferenceAlternative 11 selected -> Just <$> parseBoundary selected
    GrammarV1ReferenceAlternative index _
      | index >= 0 && index <= 14 -> pure Nothing
      | otherwise -> failCB ("declaration alternative out of range: " <> showText index)
    _ -> failCB "declaration body is not an alternative node"

parseCapability
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCapabilityBoundaryError
      GrammarV1ReferenceCapabilityBoundaryDeclaration
parseCapability tree = do
  fields <- namedSequence "capability_decl" tree
  case fields of
    [keyword, nameTree, genericTree, modeKeyword, modeTree, requirementsTree,
      openBrace, itemsTree, closeBrace] -> do
      expectLiteral "capability" keyword
      name <- mapCommon (grammarV1ReferenceIdentifierCore nameTree)
      genericParams <- mapCommon
        (grammarV1ReferenceOptionalGenericParamsCore genericTree)
      expectLiteral "mode" modeKeyword
      mode <- mapCommon (grammarV1ReferenceStructuralModeCore modeTree)
      requirements <- mapCommon
        (grammarV1ReferenceOptionalRequirementsCore requirementsTree)
      expectLiteral "{" openBrace
      items <- expectRepetition "capability items" itemsTree >>= traverse parseCapabilityItem
      expectLiteral "}" closeBrace
      pure (GrammarV1ReferenceCapabilityDeclaration
        name genericParams mode requirements items)
    _ -> failCB "capability_decl body is not a nine-item sequence"

parseCapabilityItem
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCapabilityBoundaryError GrammarV1ReferenceCapabilityItemCore
parseCapabilityItem tree = do
  body <- expectNonterminal "capability_item" tree
  case body of
    GrammarV1ReferenceAlternative 0 selected -> do
      fields <- expectSequence "capability permits item" selected
      case fields of
        [keyword, referenceTree, terminator] -> do
          expectLiteral "permits" keyword
          reference <- mapStatic (grammarV1ReferenceStaticReferenceSpine referenceTree)
          expectLiteral ";" terminator
          pure (GrammarV1ReferenceCapabilityPermits reference)
        _ -> failCB "capability permits item is not a three-item sequence"
    GrammarV1ReferenceAlternative 1 selected -> do
      fields <- expectSequence "capability requires item" selected
      case fields of
        [keyword, propositionTree, terminator] -> do
          expectLiteral "requires" keyword
          proposition <- mapProp (grammarV1ReferencePropositionCore propositionTree)
          expectLiteral ";" terminator
          pure (GrammarV1ReferenceCapabilityRequires proposition)
        _ -> failCB "capability requires item is not a three-item sequence"
    GrammarV1ReferenceAlternative 2 selected -> do
      fields <- expectSequence "capability law item" selected
      case fields of
        [keyword, nameTree, colon, propositionTree, terminator] -> do
          expectLiteral "law" keyword
          name <- mapCommon (grammarV1ReferenceIdentifierCore nameTree)
          expectLiteral ":" colon
          proposition <- mapProp (grammarV1ReferencePropositionCore propositionTree)
          expectLiteral ";" terminator
          pure (GrammarV1ReferenceCapabilityLaw name proposition)
        _ -> failCB "capability law item is not a five-item sequence"
    GrammarV1ReferenceAlternative index _ ->
      failCB ("capability_item alternative out of range: " <> showText index)
    _ -> failCB "capability_item body is not an alternative node"

parseBoundary
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCapabilityBoundaryError
      GrammarV1ReferenceCapabilityBoundaryDeclaration
parseBoundary tree = do
  fields <- namedSequence "boundary_decl" tree
  case fields of
    [keyword, nameTree, genericTree, requirementsTree, colon, typeTree,
      openBrace, itemsTree, closeBrace] -> do
      expectLiteral "boundary" keyword
      name <- mapCommon (grammarV1ReferenceIdentifierCore nameTree)
      genericParams <- mapCommon
        (grammarV1ReferenceOptionalGenericParamsCore genericTree)
      requirements <- mapCommon
        (grammarV1ReferenceOptionalRequirementsCore requirementsTree)
      expectLiteral ":" colon
      sourceType <- mapType (grammarV1ReferenceTypePayload typeTree)
      expectLiteral "{" openBrace
      items <- expectRepetition "boundary items" itemsTree >>= traverse parseBoundaryItem
      expectLiteral "}" closeBrace
      pure (GrammarV1ReferenceBoundaryDeclaration
        name genericParams requirements sourceType items)
    _ -> failCB "boundary_decl body is not a nine-item sequence"

parseBoundaryItem
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCapabilityBoundaryError GrammarV1ReferenceBoundaryItemCore
parseBoundaryItem tree = do
  body <- expectNonterminal "boundary_item" tree
  case body of
    GrammarV1ReferenceAlternative 0 selected -> parseBoundaryTransport
      "receive" GrammarV1ReferenceBoundaryReceive selected
    GrammarV1ReferenceAlternative 1 selected -> parseBoundaryTransport
      "send" GrammarV1ReferenceBoundarySend selected
    GrammarV1ReferenceAlternative 2 selected -> do
      fields <- expectSequence "boundary correspondence item" selected
      case fields of
        [keyword, propositionTree, terminator] -> do
          expectLiteral "correspondence" keyword
          proposition <- mapProp (grammarV1ReferencePropositionCore propositionTree)
          expectLiteral ";" terminator
          pure (GrammarV1ReferenceBoundaryCorrespondence proposition)
        _ -> failCB "boundary correspondence item is not a three-item sequence"
    GrammarV1ReferenceAlternative 3 selected -> do
      fields <- expectSequence "boundary canonical item" selected
      case fields of
        [keyword, terminator] -> do
          expectLiteral "canonical" keyword
          expectLiteral ";" terminator
          pure GrammarV1ReferenceBoundaryCanonical
        _ -> failCB "boundary canonical item is not a two-item sequence"
    GrammarV1ReferenceAlternative 4 selected -> do
      fields <- expectSequence "boundary failure item" selected
      case fields of
        [keyword, typeTree, terminator] -> do
          expectLiteral "failure" keyword
          sourceType <- mapType (grammarV1ReferenceTypePayload typeTree)
          expectLiteral ";" terminator
          pure (GrammarV1ReferenceBoundaryFailure sourceType)
        _ -> failCB "boundary failure item is not a three-item sequence"
    GrammarV1ReferenceAlternative 5 selected -> do
      fields <- expectSequence "boundary law item" selected
      case fields of
        [keyword, nameTree, colon, propositionTree, terminator] -> do
          expectLiteral "law" keyword
          name <- mapCommon (grammarV1ReferenceIdentifierCore nameTree)
          expectLiteral ":" colon
          proposition <- mapProp (grammarV1ReferencePropositionCore propositionTree)
          expectLiteral ";" terminator
          pure (GrammarV1ReferenceBoundaryLaw name proposition)
        _ -> failCB "boundary law item is not a five-item sequence"
    GrammarV1ReferenceAlternative index _ ->
      failCB ("boundary_item alternative out of range: " <> showText index)
    _ -> failCB "boundary_item body is not an alternative node"

parseBoundaryTransport
  :: Text
  -> (GrammarV1ReferenceStaticReferenceSpine -> GrammarV1ReferenceBoundaryItemCore)
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCapabilityBoundaryError GrammarV1ReferenceBoundaryItemCore
parseBoundaryTransport keyword constructor tree = do
  fields <- expectSequence ("boundary " <> keyword <> " item") tree
  case fields of
    [keywordTree, usingKeyword, referenceTree, terminator] -> do
      expectLiteral keyword keywordTree
      expectLiteral "using" usingKeyword
      reference <- mapStatic (grammarV1ReferenceStaticReferenceSpine referenceTree)
      expectLiteral ";" terminator
      pure (constructor reference)
    _ -> failCB ("boundary " <> keyword <> " item is not a four-item sequence")

grammarV1ProductionCapabilityBoundaryDeclarations
  :: GrammarV1SourceFile
  -> [GrammarV1ReferenceCapabilityBoundaryDeclaration]
grammarV1ProductionCapabilityBoundaryDeclarations sourceFile =
  [ value
  | locatedTopLevel <- grammarV1TopLevelDecls sourceFile
  , let declaration = locatedValue (grammarV1Declaration (locatedValue locatedTopLevel))
  , Just value <- [grammarV1ProductionCapabilityBoundaryDeclaration declaration]
  ]

grammarV1ReferenceCapabilityBoundaryDeclarations
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCapabilityBoundaryError
      [GrammarV1ReferenceCapabilityBoundaryDeclaration]
grammarV1ReferenceCapabilityBoundaryDeclarations tree = do
  body <- expectNonterminal "source_file" tree
  fields <- expectSequence "source_file" body
  case fields of
    [_moduleTree, _importsTree, topLevelsTree] -> do
      topLevels <- expectRepetition "source_file top levels" topLevelsTree
      values <- traverse parseTopLevel topLevels
      pure [value | Just value <- values]
    _ -> failCB "source_file body is not a three-item sequence"
  where
    parseTopLevel topLevelTree = do
      topBody <- expectNonterminal "top_level_decl" topLevelTree
      topFields <- expectSequence "top_level_decl" topBody
      case topFields of
        [_attributesTree, declarationTree] ->
          grammarV1ReferenceCapabilityBoundaryDeclaration declarationTree
        _ -> failCB "top_level_decl body is not a two-item sequence"

namedSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCapabilityBoundaryError [GrammarV1ReferenceParseTree]
namedSequence name tree = expectNonterminal name tree >>= expectSequence name

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCapabilityBoundaryError GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> pure body
    | otherwise -> failCB ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failCB ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCapabilityBoundaryError [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence values -> pure values
  _ -> failCB (label <> " is not a sequence node")

expectRepetition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCapabilityBoundaryError [GrammarV1ReferenceParseTree]
expectRepetition label tree = case tree of
  GrammarV1ReferenceRepetition values -> pure values
  _ -> failCB (label <> " is not a repetition node")

expectLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCapabilityBoundaryError ()
expectLiteral expected tree = case tree of
  GrammarV1ReferenceLiteral actual
    | actual == expected -> pure ()
    | otherwise -> failCB ("expected literal " <> expected <> ", got " <> actual)
  _ -> failCB ("expected literal " <> expected)

mapCommon :: Show e => Either e a -> Either GrammarV1ReferenceCapabilityBoundaryError a
mapCommon = mapNested "declaration-common"

mapProp :: Show e => Either e a -> Either GrammarV1ReferenceCapabilityBoundaryError a
mapProp = mapNested "proposition"

mapStatic :: Show e => Either e a -> Either GrammarV1ReferenceCapabilityBoundaryError a
mapStatic = mapNested "static-reference"

mapType :: Show e => Either e a -> Either GrammarV1ReferenceCapabilityBoundaryError a
mapType = mapNested "type"

mapNested
  :: Show e
  => Text
  -> Either e a
  -> Either GrammarV1ReferenceCapabilityBoundaryError a
mapNested label result = case result of
  Left errorValue -> failCB (label <> " correspondence failed: " <> Text.pack (show errorValue))
  Right value -> pure value

showText :: Show a => a -> Text
showText = Text.pack . show

failCB
  :: Text
  -> Either GrammarV1ReferenceCapabilityBoundaryError a
failCB = Left . GrammarV1ReferenceCapabilityBoundaryError
