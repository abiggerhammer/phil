{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstArchitectureProgram
  ( GrammarV1ReferenceArchitectureProgramError (..)
  , GrammarV1ReferenceRoleTargetCore (..)
  , GrammarV1ReferenceArchitectureItemCore (..)
  , GrammarV1ReferenceProgramItemCore (..)
  , GrammarV1ReferenceArchitectureProgramDeclaration (..)
  , grammarV1ProductionArchitectureProgramDeclaration
  , grammarV1ReferenceArchitectureProgramDeclaration
  , grammarV1ProductionArchitectureProgramDeclarations
  , grammarV1ReferenceArchitectureProgramDeclarations
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ArchitectureDecl (..)
  , GrammarV1ArchitectureItem (..)
  , GrammarV1Declaration (..)
  , GrammarV1ProgramDecl (..)
  , GrammarV1ProgramItem (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1RoleTarget (..)
  , GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstDeclarationCommon
  ( GrammarV1ReferenceDeclarationCommonError
  , GrammarV1ReferenceGenericParamCore
  , GrammarV1ReferenceRequirementCore
  , grammarV1ProductionGenericParamCore
  , grammarV1ProductionRequirementCore
  , grammarV1ReferenceIdentifierCore
  , grammarV1ReferenceOptionalGenericParamsCore
  , grammarV1ReferenceOptionalRequirementsCore
  )
import Phil.Surface.GrammarV1.ReferenceAstExpressionCore
  ( GrammarV1ReferenceExpressionCore
  , grammarV1ProductionExpressionCore
  , grammarV1ReferenceExpressionCore
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

newtype GrammarV1ReferenceArchitectureProgramError =
  GrammarV1ReferenceArchitectureProgramError Text
  deriving (Eq, Show)

data GrammarV1ReferenceRoleTargetCore
  = GrammarV1ReferenceInternalRoleTarget [Text]
  | GrammarV1ReferenceExternalRoleTarget
  deriving (Eq, Show)

data GrammarV1ReferenceArchitectureItemCore
  = GrammarV1ReferenceArchitectureInstance Text GrammarV1ReferenceStaticReferenceSpine
  | GrammarV1ReferenceArchitectureRef Text [Text]
  | GrammarV1ReferenceArchitectureProcess Text [Text]
  | GrammarV1ReferenceArchitectureProtocol Text GrammarV1ReferenceStaticReferenceSpine
  | GrammarV1ReferenceArchitectureRole [Text] GrammarV1ReferenceRoleTargetCore
  | GrammarV1ReferenceArchitectureBind [Text] [Text]
  | GrammarV1ReferenceArchitectureAuthority Text GrammarV1ReferenceTypePayload [Text]
  | GrammarV1ReferenceArchitectureGrant [Text] GrammarV1ReferenceExpressionCore
  | GrammarV1ReferenceArchitectureBoundary [Text] [Text]
  | GrammarV1ReferenceArchitectureEntry Text GrammarV1ReferenceTypePayload
  | GrammarV1ReferenceArchitectureAssume GrammarV1ReferencePropositionCore [Text]
  | GrammarV1ReferenceArchitectureExportObligation [Text] [Text]
  | GrammarV1ReferenceArchitectureObservable [Text]
  | GrammarV1ReferenceArchitectureConstraint GrammarV1ReferencePropositionCore
  deriving (Eq, Show)

data GrammarV1ReferenceProgramItemCore
  = GrammarV1ReferenceProgramEntry Text GrammarV1ReferenceTypePayload
  | GrammarV1ReferenceProgramAssume GrammarV1ReferencePropositionCore [Text]
  | GrammarV1ReferenceProgramExportObligation [Text] [Text]
  | GrammarV1ReferenceProgramObservable [Text]
  deriving (Eq, Show)

data GrammarV1ReferenceArchitectureProgramDeclaration
  = GrammarV1ReferenceArchitectureDeclarationCore
      Text
      [GrammarV1ReferenceGenericParamCore]
      [GrammarV1ReferenceRequirementCore]
      [GrammarV1ReferenceArchitectureItemCore]
  | GrammarV1ReferenceProgramDeclarationCore
      Text
      GrammarV1ReferenceStaticReferenceSpine
      [GrammarV1ReferenceProgramItemCore]
  deriving (Eq, Show)

grammarV1ProductionArchitectureProgramDeclaration
  :: GrammarV1Declaration
  -> Maybe GrammarV1ReferenceArchitectureProgramDeclaration
grammarV1ProductionArchitectureProgramDeclaration declaration = case declaration of
  GrammarV1ArchitectureDeclaration architecture ->
    Just (GrammarV1ReferenceArchitectureDeclarationCore
      (locatedValue (grammarV1ArchitectureName architecture))
      (map (grammarV1ProductionGenericParamCore . locatedValue)
        (grammarV1ArchitectureGenericParams architecture))
      (map (grammarV1ProductionRequirementCore . locatedValue)
        (grammarV1ArchitectureRequirements architecture))
      (map (productionArchitectureItem . locatedValue)
        (grammarV1ArchitectureItems architecture)))
  GrammarV1ProgramDeclaration program ->
    Just (GrammarV1ReferenceProgramDeclarationCore
      (locatedValue (grammarV1ProgramName program))
      (grammarV1ProductionStaticReferenceSpine
        (locatedValue (grammarV1ProgramTarget program)))
      (map (productionProgramItem . locatedValue) (grammarV1ProgramItems program)))
  _ -> Nothing

productionArchitectureItem
  :: GrammarV1ArchitectureItem
  -> GrammarV1ReferenceArchitectureItemCore
productionArchitectureItem item = case item of
  GrammarV1ArchitectureInstance name reference ->
    GrammarV1ReferenceArchitectureInstance
      (locatedValue name)
      (grammarV1ProductionStaticReferenceSpine (locatedValue reference))
  GrammarV1ArchitectureRef name target ->
    GrammarV1ReferenceArchitectureRef
      (locatedValue name)
      (qualifiedNameParts (locatedValue target))
  GrammarV1ArchitectureProcess name target ->
    GrammarV1ReferenceArchitectureProcess
      (locatedValue name)
      (qualifiedNameParts (locatedValue target))
  GrammarV1ArchitectureProtocol name reference ->
    GrammarV1ReferenceArchitectureProtocol
      (locatedValue name)
      (grammarV1ProductionStaticReferenceSpine (locatedValue reference))
  GrammarV1ArchitectureRole role target ->
    GrammarV1ReferenceArchitectureRole
      (qualifiedNameParts (locatedValue role))
      (productionRoleTarget (locatedValue target))
  GrammarV1ArchitectureBind source target ->
    GrammarV1ReferenceArchitectureBind
      (qualifiedNameParts (locatedValue source))
      (qualifiedNameParts (locatedValue target))
  GrammarV1ArchitectureAuthority name sourceType origin ->
    GrammarV1ReferenceArchitectureAuthority
      (locatedValue name)
      (grammarV1ProductionTypePayload (locatedValue sourceType))
      (qualifiedNameParts (locatedValue origin))
  GrammarV1ArchitectureGrant target expression ->
    GrammarV1ReferenceArchitectureGrant
      (qualifiedNameParts (locatedValue target))
      (grammarV1ProductionExpressionCore (locatedValue expression))
  GrammarV1ArchitectureBoundary source target ->
    GrammarV1ReferenceArchitectureBoundary
      (qualifiedNameParts (locatedValue source))
      (qualifiedNameParts (locatedValue target))
  GrammarV1ArchitectureEntry name sourceType ->
    GrammarV1ReferenceArchitectureEntry
      (locatedValue name)
      (grammarV1ProductionTypePayload (locatedValue sourceType))
  GrammarV1ArchitectureAssume proposition scope ->
    GrammarV1ReferenceArchitectureAssume
      (grammarV1ProductionPropositionCore (locatedValue proposition))
      (qualifiedNameParts (locatedValue scope))
  GrammarV1ArchitectureExportObligation obligation target ->
    GrammarV1ReferenceArchitectureExportObligation
      (qualifiedNameParts (locatedValue obligation))
      (qualifiedNameParts (locatedValue target))
  GrammarV1ArchitectureObservable target ->
    GrammarV1ReferenceArchitectureObservable
      (qualifiedNameParts (locatedValue target))
  GrammarV1ArchitectureConstraint proposition ->
    GrammarV1ReferenceArchitectureConstraint
      (grammarV1ProductionPropositionCore (locatedValue proposition))

productionRoleTarget :: GrammarV1RoleTarget -> GrammarV1ReferenceRoleTargetCore
productionRoleTarget target = case target of
  GrammarV1InternalRoleTarget name ->
    GrammarV1ReferenceInternalRoleTarget (qualifiedNameParts (locatedValue name))
  GrammarV1ExternalRoleTarget -> GrammarV1ReferenceExternalRoleTarget

productionProgramItem :: GrammarV1ProgramItem -> GrammarV1ReferenceProgramItemCore
productionProgramItem item = case item of
  GrammarV1ProgramEntry name sourceType ->
    GrammarV1ReferenceProgramEntry
      (locatedValue name)
      (grammarV1ProductionTypePayload (locatedValue sourceType))
  GrammarV1ProgramAssume proposition scope ->
    GrammarV1ReferenceProgramAssume
      (grammarV1ProductionPropositionCore (locatedValue proposition))
      (qualifiedNameParts (locatedValue scope))
  GrammarV1ProgramExportObligation obligation target ->
    GrammarV1ReferenceProgramExportObligation
      (qualifiedNameParts (locatedValue obligation))
      (qualifiedNameParts (locatedValue target))
  GrammarV1ProgramObservable target ->
    GrammarV1ReferenceProgramObservable
      (qualifiedNameParts (locatedValue target))

qualifiedNameParts :: GrammarV1QualifiedName -> [Text]
qualifiedNameParts = grammarV1QualifiedNameParts

grammarV1ReferenceArchitectureProgramDeclaration
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError
      (Maybe GrammarV1ReferenceArchitectureProgramDeclaration)
grammarV1ReferenceArchitectureProgramDeclaration tree = do
  body <- expectNonterminal "declaration" tree
  case body of
    GrammarV1ReferenceAlternative 12 selected -> Just <$> parseArchitecture selected
    GrammarV1ReferenceAlternative 14 selected -> Just <$> parseProgram selected
    GrammarV1ReferenceAlternative index _
      | index >= 0 && index <= 14 -> pure Nothing
      | otherwise -> failAP ("declaration alternative out of range: " <> showText index)
    _ -> failAP "declaration body is not an alternative node"

parseArchitecture
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError
      GrammarV1ReferenceArchitectureProgramDeclaration
parseArchitecture tree = do
  fields <- namedSequence "architecture_decl" tree
  case fields of
    [keyword, nameTree, genericTree, requirementsTree, openBrace, itemsTree, closeBrace] -> do
      expectLiteral "architecture" keyword
      name <- mapCommon (grammarV1ReferenceIdentifierCore nameTree)
      generics <- mapCommon (grammarV1ReferenceOptionalGenericParamsCore genericTree)
      requirements <- mapCommon
        (grammarV1ReferenceOptionalRequirementsCore requirementsTree)
      expectLiteral "{" openBrace
      items <- expectRepetition "architecture items" itemsTree >>= traverse parseArchitectureItem
      expectLiteral "}" closeBrace
      pure (GrammarV1ReferenceArchitectureDeclarationCore
        name generics requirements items)
    _ -> failAP "architecture_decl body is not a seven-item sequence"

parseArchitectureItem
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError GrammarV1ReferenceArchitectureItemCore
parseArchitectureItem tree = do
  body <- expectNonterminal "architecture_item" tree
  case body of
    GrammarV1ReferenceAlternative index selected -> case index of
      0 -> parseNamedStaticItem "instance" GrammarV1ReferenceArchitectureInstance selected
      1 -> parseNamedQualifiedItem "ref" GrammarV1ReferenceArchitectureRef selected
      2 -> parseNamedQualifiedItem "process" GrammarV1ReferenceArchitectureProcess selected
      3 -> parseNamedStaticItem "protocol" GrammarV1ReferenceArchitectureProtocol selected
      4 -> parseRoleItem selected
      5 -> parseQualifiedPairItem "bind" GrammarV1ReferenceArchitectureBind selected
      6 -> parseAuthorityItem selected
      7 -> parseGrantItem selected
      8 -> parseQualifiedPairItem "boundary" GrammarV1ReferenceArchitectureBoundary selected
      9 -> parseEntryItem selected
      10 -> parseAssumeItem GrammarV1ReferenceArchitectureAssume selected
      11 -> parseExportObligationItem GrammarV1ReferenceArchitectureExportObligation selected
      12 -> parseObservableItem GrammarV1ReferenceArchitectureObservable selected
      13 -> parseConstraintItem selected
      _ -> failAP ("architecture_item alternative out of range: " <> showText index)
    _ -> failAP "architecture_item body is not an alternative node"

parseNamedStaticItem
  :: Text
  -> (Text -> GrammarV1ReferenceStaticReferenceSpine -> GrammarV1ReferenceArchitectureItemCore)
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError GrammarV1ReferenceArchitectureItemCore
parseNamedStaticItem keyword constructor tree = do
  fields <- expectSequence (keyword <> " architecture item") tree
  case fields of
    [keywordTree, nameTree, equals, referenceTree, terminator] -> do
      expectLiteral keyword keywordTree
      name <- mapCommon (grammarV1ReferenceIdentifierCore nameTree)
      expectLiteral "=" equals
      reference <- mapStatic (grammarV1ReferenceStaticReferenceSpine referenceTree)
      expectLiteral ";" terminator
      pure (constructor name reference)
    _ -> failAP (keyword <> " architecture item is not a five-item sequence")

parseNamedQualifiedItem
  :: Text
  -> (Text -> [Text] -> GrammarV1ReferenceArchitectureItemCore)
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError GrammarV1ReferenceArchitectureItemCore
parseNamedQualifiedItem keyword constructor tree = do
  fields <- expectSequence (keyword <> " architecture item") tree
  case fields of
    [keywordTree, nameTree, equals, targetTree, terminator] -> do
      expectLiteral keyword keywordTree
      name <- mapCommon (grammarV1ReferenceIdentifierCore nameTree)
      expectLiteral "=" equals
      target <- parseQualifiedName targetTree
      expectLiteral ";" terminator
      pure (constructor name target)
    _ -> failAP (keyword <> " architecture item is not a five-item sequence")

parseRoleItem
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError GrammarV1ReferenceArchitectureItemCore
parseRoleItem tree = do
  fields <- expectSequence "role architecture item" tree
  case fields of
    [keyword, roleTree, equals, targetTree, terminator] -> do
      expectLiteral "role" keyword
      role <- parseQualifiedName roleTree
      expectLiteral "=" equals
      target <- parseRoleTarget targetTree
      expectLiteral ";" terminator
      pure (GrammarV1ReferenceArchitectureRole role target)
    _ -> failAP "role architecture item is not a five-item sequence"

parseRoleTarget
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError GrammarV1ReferenceRoleTargetCore
parseRoleTarget tree = do
  body <- expectNonterminal "role_target" tree
  case body of
    GrammarV1ReferenceAlternative 0 qualifiedTree ->
      GrammarV1ReferenceInternalRoleTarget <$> parseQualifiedName qualifiedTree
    GrammarV1ReferenceAlternative 1 externalTree -> do
      expectLiteral "external" externalTree
      pure GrammarV1ReferenceExternalRoleTarget
    GrammarV1ReferenceAlternative index _ ->
      failAP ("role_target alternative out of range: " <> showText index)
    _ -> failAP "role_target body is not an alternative node"

parseQualifiedPairItem
  :: Text
  -> ([Text] -> [Text] -> GrammarV1ReferenceArchitectureItemCore)
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError GrammarV1ReferenceArchitectureItemCore
parseQualifiedPairItem keyword constructor tree = do
  fields <- expectSequence (keyword <> " architecture item") tree
  case fields of
    [keywordTree, sourceTree, equals, targetTree, terminator] -> do
      expectLiteral keyword keywordTree
      source <- parseQualifiedName sourceTree
      expectLiteral "=" equals
      target <- parseQualifiedName targetTree
      expectLiteral ";" terminator
      pure (constructor source target)
    _ -> failAP (keyword <> " architecture item is not a five-item sequence")

parseAuthorityItem
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError GrammarV1ReferenceArchitectureItemCore
parseAuthorityItem tree = do
  fields <- expectSequence "authority architecture item" tree
  case fields of
    [keyword, nameTree, colon, typeTree, originatesKeyword, atKeyword, originTree, terminator] -> do
      expectLiteral "authority" keyword
      name <- mapCommon (grammarV1ReferenceIdentifierCore nameTree)
      expectLiteral ":" colon
      sourceType <- mapType (grammarV1ReferenceTypePayload typeTree)
      expectLiteral "originates" originatesKeyword
      expectLiteral "at" atKeyword
      origin <- parseQualifiedName originTree
      expectLiteral ";" terminator
      pure (GrammarV1ReferenceArchitectureAuthority name sourceType origin)
    _ -> failAP "authority architecture item is not an eight-item sequence"

parseGrantItem
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError GrammarV1ReferenceArchitectureItemCore
parseGrantItem tree = do
  fields <- expectSequence "grant architecture item" tree
  case fields of
    [keyword, targetTree, equals, expressionTree, terminator] -> do
      expectLiteral "grant" keyword
      target <- parseQualifiedName targetTree
      expectLiteral "=" equals
      expression <- mapExpression (grammarV1ReferenceExpressionCore expressionTree)
      expectLiteral ";" terminator
      pure (GrammarV1ReferenceArchitectureGrant target expression)
    _ -> failAP "grant architecture item is not a five-item sequence"

parseEntryItem
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError GrammarV1ReferenceArchitectureItemCore
parseEntryItem tree = do
  fields <- expectSequence "entry architecture item" tree
  case fields of
    [keyword, nameTree, colon, typeTree, terminator] -> do
      expectLiteral "entry" keyword
      name <- mapCommon (grammarV1ReferenceIdentifierCore nameTree)
      expectLiteral ":" colon
      sourceType <- mapType (grammarV1ReferenceTypePayload typeTree)
      expectLiteral ";" terminator
      pure (GrammarV1ReferenceArchitectureEntry name sourceType)
    _ -> failAP "entry architecture item is not a five-item sequence"

parseAssumeItem
  :: (GrammarV1ReferencePropositionCore -> [Text] -> a)
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError a
parseAssumeItem constructor tree = do
  fields <- expectSequence "assume item" tree
  case fields of
    [keyword, propositionTree, withinKeyword, scopeTree, terminator] -> do
      expectLiteral "assume" keyword
      proposition <- mapProposition (grammarV1ReferencePropositionCore propositionTree)
      expectLiteral "within" withinKeyword
      scope <- parseQualifiedName scopeTree
      expectLiteral ";" terminator
      pure (constructor proposition scope)
    _ -> failAP "assume item is not a five-item sequence"

parseExportObligationItem
  :: ([Text] -> [Text] -> a)
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError a
parseExportObligationItem constructor tree = do
  fields <- expectSequence "export obligation item" tree
  case fields of
    [exportKeyword, obligationKeyword, obligationTree, toKeyword, targetTree, terminator] -> do
      expectLiteral "export" exportKeyword
      expectLiteral "obligation" obligationKeyword
      obligation <- parseQualifiedName obligationTree
      expectLiteral "to" toKeyword
      target <- parseQualifiedName targetTree
      expectLiteral ";" terminator
      pure (constructor obligation target)
    _ -> failAP "export obligation item is not a six-item sequence"

parseObservableItem
  :: ([Text] -> a)
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError a
parseObservableItem constructor tree = do
  fields <- expectSequence "observable item" tree
  case fields of
    [keyword, targetTree, terminator] -> do
      expectLiteral "observable" keyword
      target <- parseQualifiedName targetTree
      expectLiteral ";" terminator
      pure (constructor target)
    _ -> failAP "observable item is not a three-item sequence"

parseConstraintItem
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError GrammarV1ReferenceArchitectureItemCore
parseConstraintItem tree = do
  fields <- expectSequence "constraint architecture item" tree
  case fields of
    [keyword, propositionTree, terminator] -> do
      expectLiteral "constraint" keyword
      proposition <- mapProposition (grammarV1ReferencePropositionCore propositionTree)
      expectLiteral ";" terminator
      pure (GrammarV1ReferenceArchitectureConstraint proposition)
    _ -> failAP "constraint architecture item is not a three-item sequence"

parseProgram
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError
      GrammarV1ReferenceArchitectureProgramDeclaration
parseProgram tree = do
  fields <- namedSequence "program_decl" tree
  case fields of
    [keyword, nameTree, equals, instantiateKeyword, targetTree, blockTree, terminator] -> do
      expectLiteral "program" keyword
      name <- mapCommon (grammarV1ReferenceIdentifierCore nameTree)
      expectLiteral "=" equals
      expectLiteral "instantiate" instantiateKeyword
      target <- mapStatic (grammarV1ReferenceStaticReferenceSpine targetTree)
      items <- parseOptionalProgramBlock blockTree
      expectLiteral ";" terminator
      pure (GrammarV1ReferenceProgramDeclarationCore name target items)
    _ -> failAP "program_decl body is not a seven-item sequence"

parseOptionalProgramBlock
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError [GrammarV1ReferenceProgramItemCore]
parseOptionalProgramBlock tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure []
  GrammarV1ReferenceOptionalSome blockTree -> parseProgramBlock blockTree
  _ -> failAP "program block slot is not optional"

parseProgramBlock
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError [GrammarV1ReferenceProgramItemCore]
parseProgramBlock tree = do
  fields <- namedSequence "program_block" tree
  case fields of
    [openBrace, itemsTree, closeBrace] -> do
      expectLiteral "{" openBrace
      items <- expectRepetition "program items" itemsTree >>= traverse parseProgramItem
      expectLiteral "}" closeBrace
      pure items
    _ -> failAP "program_block body is not a three-item sequence"

parseProgramItem
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError GrammarV1ReferenceProgramItemCore
parseProgramItem tree = do
  body <- expectNonterminal "program_item" tree
  case body of
    GrammarV1ReferenceAlternative index selected -> case index of
      0 -> parseProgramEntry selected
      1 -> parseAssumeItem GrammarV1ReferenceProgramAssume selected
      2 -> parseExportObligationItem GrammarV1ReferenceProgramExportObligation selected
      3 -> parseObservableItem GrammarV1ReferenceProgramObservable selected
      _ -> failAP ("program_item alternative out of range: " <> showText index)
    _ -> failAP "program_item body is not an alternative node"

parseProgramEntry
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError GrammarV1ReferenceProgramItemCore
parseProgramEntry tree = do
  fields <- expectSequence "program entry item" tree
  case fields of
    [keyword, nameTree, colon, typeTree, terminator] -> do
      expectLiteral "entry" keyword
      name <- mapCommon (grammarV1ReferenceIdentifierCore nameTree)
      expectLiteral ":" colon
      sourceType <- mapType (grammarV1ReferenceTypePayload typeTree)
      expectLiteral ";" terminator
      pure (GrammarV1ReferenceProgramEntry name sourceType)
    _ -> failAP "program entry item is not a five-item sequence"

grammarV1ProductionArchitectureProgramDeclarations
  :: GrammarV1SourceFile
  -> [GrammarV1ReferenceArchitectureProgramDeclaration]
grammarV1ProductionArchitectureProgramDeclarations sourceFile =
  [ value
  | locatedTopLevel <- grammarV1TopLevelDecls sourceFile
  , let declaration = locatedValue (grammarV1Declaration (locatedValue locatedTopLevel))
  , Just value <- [grammarV1ProductionArchitectureProgramDeclaration declaration]
  ]

grammarV1ReferenceArchitectureProgramDeclarations
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError
      [GrammarV1ReferenceArchitectureProgramDeclaration]
grammarV1ReferenceArchitectureProgramDeclarations tree = do
  fields <- namedSequence "source_file" tree
  case fields of
    [_moduleTree, _importsTree, topLevelsTree] -> do
      topLevels <- expectRepetition "source_file top levels" topLevelsTree
      values <- traverse parseTopLevel topLevels
      pure [value | Just value <- values]
    _ -> failAP "source_file body is not a three-item sequence"
  where
    parseTopLevel topLevelTree = do
      topFields <- namedSequence "top_level_decl" topLevelTree
      case topFields of
        [_attributesTree, declarationTree] ->
          grammarV1ReferenceArchitectureProgramDeclaration declarationTree
        _ -> failAP "top_level_decl body is not a two-item sequence"

parseQualifiedName
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError [Text]
parseQualifiedName tree = do
  fields <- namedSequence "qualified_name" tree
  case fields of
    [firstTree, restTree] -> do
      first <- mapCommon (grammarV1ReferenceIdentifierCore firstTree)
      suffixes <- expectRepetition "qualified-name suffixes" restTree
      rest <- traverse parseQualifiedSuffix suffixes
      pure (first : rest)
    _ -> failAP "qualified_name body is not a two-item sequence"

parseQualifiedSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError Text
parseQualifiedSuffix tree = do
  fields <- expectSequence "qualified-name suffix" tree
  case fields of
    [dot, identifierTree] -> do
      expectLiteral "." dot
      mapCommon (grammarV1ReferenceIdentifierCore identifierTree)
    _ -> failAP "qualified-name suffix is not a two-item sequence"

namedSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError [GrammarV1ReferenceParseTree]
namedSequence name tree = expectNonterminal name tree >>= expectSequence name

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> pure body
    | otherwise -> failAP ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failAP ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence values -> pure values
  _ -> failAP (label <> " is not a sequence node")

expectRepetition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError [GrammarV1ReferenceParseTree]
expectRepetition label tree = case tree of
  GrammarV1ReferenceRepetition values -> pure values
  _ -> failAP (label <> " is not a repetition node")

expectLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceArchitectureProgramError ()
expectLiteral expected tree = case tree of
  GrammarV1ReferenceLiteral actual
    | actual == expected -> pure ()
    | otherwise -> failAP ("expected literal " <> expected <> ", got " <> actual)
  _ -> failAP ("expected literal " <> expected)

mapCommon
  :: Either GrammarV1ReferenceDeclarationCommonError a
  -> Either GrammarV1ReferenceArchitectureProgramError a
mapCommon = mapNested "declaration-common"

mapExpression :: Show e => Either e a -> Either GrammarV1ReferenceArchitectureProgramError a
mapExpression = mapNested "expression"

mapProposition :: Show e => Either e a -> Either GrammarV1ReferenceArchitectureProgramError a
mapProposition = mapNested "proposition"

mapStatic :: Show e => Either e a -> Either GrammarV1ReferenceArchitectureProgramError a
mapStatic = mapNested "static-reference"

mapType :: Show e => Either e a -> Either GrammarV1ReferenceArchitectureProgramError a
mapType = mapNested "type"

mapNested
  :: Show e
  => Text
  -> Either e a
  -> Either GrammarV1ReferenceArchitectureProgramError a
mapNested label result = case result of
  Left errorValue -> failAP
    (label <> " correspondence failed: " <> Text.pack (show errorValue))
  Right value -> pure value

showText :: Show a => a -> Text
showText = Text.pack . show

failAP
  :: Text
  -> Either GrammarV1ReferenceArchitectureProgramError a
failAP = Left . GrammarV1ReferenceArchitectureProgramError
