{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstCallableContract
  ( GrammarV1ReferenceCallableContractError (..)
  , GrammarV1ReferenceOutcomeKindCore (..)
  , GrammarV1ReferenceOutcomeSpecCore (..)
  , GrammarV1ReferenceStateSlotCore (..)
  , GrammarV1ReferenceCalleeTransitionCore (..)
  , GrammarV1ReferenceOutcomeResidueClauseCore (..)
  , GrammarV1ReferenceOutcomeResidueCore (..)
  , GrammarV1ReferenceCallableClauseCore (..)
  , GrammarV1ReferenceCallableContractDeclaration (..)
  , grammarV1ProductionCallableContractDeclaration
  , grammarV1ReferenceCallableContractDeclaration
  , grammarV1ProductionCallableContractDeclarations
  , grammarV1ReferenceCallableContractDeclarations
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1CalleeTransition (..)
  , GrammarV1CallableClause (..)
  , GrammarV1CallableContractDecl (..)
  , GrammarV1Declaration (..)
  , GrammarV1OutcomeKind (..)
  , GrammarV1OutcomeResidue (..)
  , GrammarV1OutcomeResidueClause (..)
  , GrammarV1OutcomeSpec (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1SourceFile (..)
  , GrammarV1StateSlot (..)
  , GrammarV1TopLevelDecl (..)
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
import Phil.Surface.GrammarV1.ReferenceAstEffects
  ( GrammarV1ReferenceEffectSetSpine
  , grammarV1ProductionEffectSetSpine
  , grammarV1ReferenceEffectSetSpine
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
import Phil.Surface.GrammarV1.ReferenceAstTermParams
  ( GrammarV1ReferenceTermParamCore
  , grammarV1ProductionTermParamCore
  , grammarV1ReferenceTermParamsCore
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

newtype GrammarV1ReferenceCallableContractError =
  GrammarV1ReferenceCallableContractError Text
  deriving (Eq, Show)

data GrammarV1ReferenceOutcomeKindCore
  = GrammarV1ReferenceSuccessOutcome
  | GrammarV1ReferenceNegativeOutcome
  | GrammarV1ReferenceTerminalOutcome
  | GrammarV1ReferenceFatalOutcome
  deriving (Eq, Ord, Show)

data GrammarV1ReferenceOutcomeSpecCore = GrammarV1ReferenceOutcomeSpecCore
  { grammarV1ReferenceOutcomeSpecKindCore :: GrammarV1ReferenceOutcomeKindCore
  , grammarV1ReferenceOutcomeSpecTypeCore :: GrammarV1ReferenceTypePayload
  }
  deriving (Eq, Show)

data GrammarV1ReferenceStateSlotCore = GrammarV1ReferenceStateSlotCore
  { grammarV1ReferenceStateSlotNameCore :: Text
  , grammarV1ReferenceStateSlotTypeCore :: GrammarV1ReferenceTypePayload
  }
  deriving (Eq, Show)

data GrammarV1ReferenceCalleeTransitionCore
  = GrammarV1ReferenceCalleePreserve
  | GrammarV1ReferenceCalleeConsume
  | GrammarV1ReferenceCalleeReplace
      GrammarV1ReferenceStaticReferenceSpine
      (Maybe GrammarV1ReferenceExpressionCore)
  deriving (Eq, Show)

data GrammarV1ReferenceOutcomeResidueClauseCore
  = GrammarV1ReferenceOutcomeState [GrammarV1ReferenceStateSlotCore]
  | GrammarV1ReferenceOutcomeCallee GrammarV1ReferenceCalleeTransitionCore
  | GrammarV1ReferenceOutcomeEnsures GrammarV1ReferencePropositionCore
  | GrammarV1ReferenceOutcomeObligation GrammarV1ReferencePropositionCore
  deriving (Eq, Show)

data GrammarV1ReferenceOutcomeResidueCore = GrammarV1ReferenceOutcomeResidueCore
  { grammarV1ReferenceOutcomeResidueKindCore :: GrammarV1ReferenceOutcomeKindCore
  , grammarV1ReferenceOutcomeResidueTypeCore :: GrammarV1ReferenceTypePayload
  , grammarV1ReferenceOutcomeResidueClausesCore :: [GrammarV1ReferenceOutcomeResidueClauseCore]
  }
  deriving (Eq, Show)

data GrammarV1ReferenceCallableClauseCore
  = GrammarV1ReferenceCallableRequires GrammarV1ReferencePropositionCore
  | GrammarV1ReferenceCallableConsumes [[Text]]
  | GrammarV1ReferenceCallableBorrows [[Text]]
  | GrammarV1ReferenceCallableAuthority [GrammarV1ReferenceTypePayload]
  | GrammarV1ReferenceCallableEffects GrammarV1ReferenceEffectSetSpine
  | GrammarV1ReferenceCallableOutcomes [GrammarV1ReferenceOutcomeSpecCore]
  | GrammarV1ReferenceCallableOutcomeResidue GrammarV1ReferenceOutcomeResidueCore
  | GrammarV1ReferenceCallableEnsures GrammarV1ReferencePropositionCore
  | GrammarV1ReferenceCallableObligation GrammarV1ReferencePropositionCore
  | GrammarV1ReferenceCallableAssumes GrammarV1ReferencePropositionCore
  | GrammarV1ReferenceCallableCost GrammarV1ReferenceExpressionCore
  | GrammarV1ReferenceCallableCallee GrammarV1ReferenceCalleeTransitionCore
  deriving (Eq, Show)

data GrammarV1ReferenceCallableContractDeclaration =
  GrammarV1ReferenceCallableContractDeclaration
    Text
    [GrammarV1ReferenceGenericParamCore]
    [GrammarV1ReferenceRequirementCore]
    [GrammarV1ReferenceTermParamCore]
    GrammarV1ReferenceTypePayload
    [GrammarV1ReferenceCallableClauseCore]
  deriving (Eq, Show)

grammarV1ProductionCallableContractDeclaration
  :: GrammarV1Declaration
  -> Maybe GrammarV1ReferenceCallableContractDeclaration
grammarV1ProductionCallableContractDeclaration declaration = case declaration of
  GrammarV1CallableContractDeclaration value -> Just (productionCallable value)
  _ -> Nothing

productionCallable
  :: GrammarV1CallableContractDecl
  -> GrammarV1ReferenceCallableContractDeclaration
productionCallable value = GrammarV1ReferenceCallableContractDeclaration
  (locatedValue (grammarV1CallableName value))
  (map (grammarV1ProductionGenericParamCore . locatedValue)
    (grammarV1CallableGenericParams value))
  (map (grammarV1ProductionRequirementCore . locatedValue)
    (grammarV1CallableRequirements value))
  (map (grammarV1ProductionTermParamCore . locatedValue)
    (grammarV1CallableTermParams value))
  (grammarV1ProductionTypePayload (locatedValue (grammarV1CallableResultType value)))
  (map (productionCallableClause . locatedValue) (grammarV1CallableClauses value))

productionCallableClause
  :: GrammarV1CallableClause
  -> GrammarV1ReferenceCallableClauseCore
productionCallableClause clause = case clause of
  GrammarV1CallableRequires proposition ->
    GrammarV1ReferenceCallableRequires
      (grammarV1ProductionPropositionCore (locatedValue proposition))
  GrammarV1CallableConsumes names ->
    GrammarV1ReferenceCallableConsumes
      (map (grammarV1QualifiedNameParts . locatedValue) names)
  GrammarV1CallableBorrows names ->
    GrammarV1ReferenceCallableBorrows
      (map (grammarV1QualifiedNameParts . locatedValue) names)
  GrammarV1CallableAuthority types ->
    GrammarV1ReferenceCallableAuthority
      (map (grammarV1ProductionTypePayload . locatedValue) types)
  GrammarV1CallableEffects effects ->
    GrammarV1ReferenceCallableEffects
      (grammarV1ProductionEffectSetSpine (locatedValue effects))
  GrammarV1CallableOutcomes outcomes ->
    GrammarV1ReferenceCallableOutcomes
      (map (productionOutcomeSpec . locatedValue) outcomes)
  GrammarV1CallableOutcomeResidue residue ->
    GrammarV1ReferenceCallableOutcomeResidue
      (productionOutcomeResidue (locatedValue residue))
  GrammarV1CallableEnsures proposition ->
    GrammarV1ReferenceCallableEnsures
      (grammarV1ProductionPropositionCore (locatedValue proposition))
  GrammarV1CallableObligation proposition ->
    GrammarV1ReferenceCallableObligation
      (grammarV1ProductionPropositionCore (locatedValue proposition))
  GrammarV1CallableAssumes proposition ->
    GrammarV1ReferenceCallableAssumes
      (grammarV1ProductionPropositionCore (locatedValue proposition))
  GrammarV1CallableCost expression ->
    GrammarV1ReferenceCallableCost
      (grammarV1ProductionExpressionCore (locatedValue expression))
  GrammarV1CallableCallee transition ->
    GrammarV1ReferenceCallableCallee
      (productionCalleeTransition (locatedValue transition))

productionOutcomeKind
  :: GrammarV1OutcomeKind
  -> GrammarV1ReferenceOutcomeKindCore
productionOutcomeKind kind = case kind of
  GrammarV1SuccessOutcome -> GrammarV1ReferenceSuccessOutcome
  GrammarV1NegativeOutcome -> GrammarV1ReferenceNegativeOutcome
  GrammarV1TerminalOutcome -> GrammarV1ReferenceTerminalOutcome
  GrammarV1FatalOutcome -> GrammarV1ReferenceFatalOutcome

productionOutcomeSpec
  :: GrammarV1OutcomeSpec
  -> GrammarV1ReferenceOutcomeSpecCore
productionOutcomeSpec spec = GrammarV1ReferenceOutcomeSpecCore
  { grammarV1ReferenceOutcomeSpecKindCore =
      productionOutcomeKind (locatedValue (grammarV1OutcomeSpecKind spec))
  , grammarV1ReferenceOutcomeSpecTypeCore =
      grammarV1ProductionTypePayload (locatedValue (grammarV1OutcomeSpecType spec))
  }

productionStateSlot
  :: GrammarV1StateSlot
  -> GrammarV1ReferenceStateSlotCore
productionStateSlot slot = GrammarV1ReferenceStateSlotCore
  { grammarV1ReferenceStateSlotNameCore = locatedValue (grammarV1StateSlotName slot)
  , grammarV1ReferenceStateSlotTypeCore =
      grammarV1ProductionTypePayload (locatedValue (grammarV1StateSlotType slot))
  }

productionCalleeTransition
  :: GrammarV1CalleeTransition
  -> GrammarV1ReferenceCalleeTransitionCore
productionCalleeTransition transition = case transition of
  GrammarV1CalleePreserve -> GrammarV1ReferenceCalleePreserve
  GrammarV1CalleeConsume -> GrammarV1ReferenceCalleeConsume
  GrammarV1CalleeReplace reference state ->
    GrammarV1ReferenceCalleeReplace
      (grammarV1ProductionStaticReferenceSpine (locatedValue reference))
      (fmap (grammarV1ProductionExpressionCore . locatedValue) state)

productionOutcomeResidueClause
  :: GrammarV1OutcomeResidueClause
  -> GrammarV1ReferenceOutcomeResidueClauseCore
productionOutcomeResidueClause clause = case clause of
  GrammarV1OutcomeState slots ->
    GrammarV1ReferenceOutcomeState
      (map (productionStateSlot . locatedValue) slots)
  GrammarV1OutcomeCallee transition ->
    GrammarV1ReferenceOutcomeCallee
      (productionCalleeTransition (locatedValue transition))
  GrammarV1OutcomeEnsures proposition ->
    GrammarV1ReferenceOutcomeEnsures
      (grammarV1ProductionPropositionCore (locatedValue proposition))
  GrammarV1OutcomeObligation proposition ->
    GrammarV1ReferenceOutcomeObligation
      (grammarV1ProductionPropositionCore (locatedValue proposition))

productionOutcomeResidue
  :: GrammarV1OutcomeResidue
  -> GrammarV1ReferenceOutcomeResidueCore
productionOutcomeResidue residue = GrammarV1ReferenceOutcomeResidueCore
  { grammarV1ReferenceOutcomeResidueKindCore =
      productionOutcomeKind (locatedValue (grammarV1OutcomeResidueKind residue))
  , grammarV1ReferenceOutcomeResidueTypeCore =
      grammarV1ProductionTypePayload (locatedValue (grammarV1OutcomeResidueType residue))
  , grammarV1ReferenceOutcomeResidueClausesCore =
      map (productionOutcomeResidueClause . locatedValue)
        (grammarV1OutcomeResidueClauses residue)
  }

grammarV1ReferenceCallableContractDeclaration
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError
      (Maybe GrammarV1ReferenceCallableContractDeclaration)
grammarV1ReferenceCallableContractDeclaration tree = do
  body <- expectNonterminal "declaration" tree
  case body of
    GrammarV1ReferenceAlternative 4 selected -> Just <$> parseCallable selected
    GrammarV1ReferenceAlternative index _
      | index >= 0 && index <= 14 -> pure Nothing
      | otherwise -> failCallable
          ("declaration alternative out of range: " <> showText index)
    _ -> failCallable "declaration body is not an alternative node"

parseCallable
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError
      GrammarV1ReferenceCallableContractDeclaration
parseCallable tree = do
  fields <- namedSequence "callable_contract_decl" tree
  case fields of
    [keyword, nameTree, genericTree, requirementsTree, paramsTree, arrow,
      resultTree, blockTree] -> do
      expectLiteral "callable" keyword
      name <- mapCommon (grammarV1ReferenceIdentifierCore nameTree)
      genericParams <- mapCommon
        (grammarV1ReferenceOptionalGenericParamsCore genericTree)
      requirements <- mapCommon
        (grammarV1ReferenceOptionalRequirementsCore requirementsTree)
      params <- mapTermParams (grammarV1ReferenceTermParamsCore paramsTree)
      expectLiteral "->" arrow
      resultType <- mapType (grammarV1ReferenceTypePayload resultTree)
      clauses <- parseCallableBlock blockTree
      pure (GrammarV1ReferenceCallableContractDeclaration
        name genericParams requirements params resultType clauses)
    _ -> failCallable "callable_contract_decl body is not an eight-item sequence"

parseCallableBlock
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError [GrammarV1ReferenceCallableClauseCore]
parseCallableBlock tree = do
  fields <- namedSequence "callable_contract_block" tree
  case fields of
    [openBrace, clausesTree, closeBrace] -> do
      expectLiteral "{" openBrace
      clauses <- expectRepetition "callable clauses" clausesTree
        >>= traverse parseCallableClause
      expectLiteral "}" closeBrace
      pure clauses
    _ -> failCallable "callable_contract_block body is not a three-item sequence"

parseCallableClause
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError GrammarV1ReferenceCallableClauseCore
parseCallableClause tree = do
  body <- expectNonterminal "callable_clause" tree
  case body of
    GrammarV1ReferenceAlternative index selected -> case index of
      0 -> GrammarV1ReferenceCallableRequires <$> parseKeywordProposition "requires" selected
      1 -> GrammarV1ReferenceCallableConsumes <$> parseKeywordNameSet "consumes" selected
      2 -> GrammarV1ReferenceCallableBorrows <$> parseKeywordNameSet "borrows" selected
      3 -> GrammarV1ReferenceCallableAuthority <$> parseKeywordTypeSet "authority" selected
      4 -> GrammarV1ReferenceCallableEffects <$> parseKeywordEffectSet "effects" selected
      5 -> GrammarV1ReferenceCallableOutcomes <$> parseKeywordOutcomeSet "outcomes" selected
      6 -> GrammarV1ReferenceCallableOutcomeResidue <$> parseOutcomeResidue selected
      7 -> GrammarV1ReferenceCallableEnsures <$> parseKeywordProposition "ensures" selected
      8 -> GrammarV1ReferenceCallableObligation <$> parseKeywordProposition "obligation" selected
      9 -> GrammarV1ReferenceCallableAssumes <$> parseKeywordProposition "assumes" selected
      10 -> GrammarV1ReferenceCallableCost <$> parseKeywordExpression "cost" selected
      11 -> GrammarV1ReferenceCallableCallee <$> parseKeywordCallee "callee" selected
      _ -> failCallable ("callable_clause alternative out of range: " <> showText index)
    _ -> failCallable "callable_clause body is not an alternative node"

parseKeywordProposition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError GrammarV1ReferencePropositionCore
parseKeywordProposition keyword tree = do
  fields <- expectSequence (keyword <> " callable clause") tree
  case fields of
    [keywordTree, propositionTree, terminator] -> do
      expectLiteral keyword keywordTree
      proposition <- mapProposition (grammarV1ReferencePropositionCore propositionTree)
      expectLiteral ";" terminator
      pure proposition
    _ -> failCallable (keyword <> " callable clause is not a three-item sequence")

parseKeywordNameSet
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError [[Text]]
parseKeywordNameSet keyword tree = do
  fields <- expectSequence (keyword <> " callable clause") tree
  case fields of
    [keywordTree, setTree, terminator] -> do
      expectLiteral keyword keywordTree
      names <- parseNameSet setTree
      expectLiteral ";" terminator
      pure names
    _ -> failCallable (keyword <> " callable clause is not a three-item sequence")

parseKeywordTypeSet
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError [GrammarV1ReferenceTypePayload]
parseKeywordTypeSet keyword tree = do
  fields <- expectSequence (keyword <> " callable clause") tree
  case fields of
    [keywordTree, setTree, terminator] -> do
      expectLiteral keyword keywordTree
      types <- parseTypeSet setTree
      expectLiteral ";" terminator
      pure types
    _ -> failCallable (keyword <> " callable clause is not a three-item sequence")

parseKeywordEffectSet
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError GrammarV1ReferenceEffectSetSpine
parseKeywordEffectSet keyword tree = do
  fields <- expectSequence (keyword <> " callable clause") tree
  case fields of
    [keywordTree, effectsTree, terminator] -> do
      expectLiteral keyword keywordTree
      effects <- mapEffects (grammarV1ReferenceEffectSetSpine effectsTree)
      expectLiteral ";" terminator
      pure effects
    _ -> failCallable (keyword <> " callable clause is not a three-item sequence")

parseKeywordOutcomeSet
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError [GrammarV1ReferenceOutcomeSpecCore]
parseKeywordOutcomeSet keyword tree = do
  fields <- expectSequence (keyword <> " callable clause") tree
  case fields of
    [keywordTree, outcomesTree, terminator] -> do
      expectLiteral keyword keywordTree
      outcomes <- parseOutcomeSet outcomesTree
      expectLiteral ";" terminator
      pure outcomes
    _ -> failCallable (keyword <> " callable clause is not a three-item sequence")

parseKeywordExpression
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError GrammarV1ReferenceExpressionCore
parseKeywordExpression keyword tree = do
  fields <- expectSequence (keyword <> " callable clause") tree
  case fields of
    [keywordTree, expressionTree, terminator] -> do
      expectLiteral keyword keywordTree
      expression <- mapExpression (grammarV1ReferenceExpressionCore expressionTree)
      expectLiteral ";" terminator
      pure expression
    _ -> failCallable (keyword <> " callable clause is not a three-item sequence")

parseKeywordCallee
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError GrammarV1ReferenceCalleeTransitionCore
parseKeywordCallee keyword tree = do
  fields <- expectSequence (keyword <> " callable clause") tree
  case fields of
    [keywordTree, transitionTree, terminator] -> do
      expectLiteral keyword keywordTree
      transition <- parseCalleeTransition transitionTree
      expectLiteral ";" terminator
      pure transition
    _ -> failCallable (keyword <> " callable clause is not a three-item sequence")

parseOutcomeKind
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError GrammarV1ReferenceOutcomeKindCore
parseOutcomeKind tree = do
  body <- expectNonterminal "outcome_kind" tree
  case body of
    GrammarV1ReferenceAlternative index selected -> case index of
      0 -> expectLiteral "success" selected >> pure GrammarV1ReferenceSuccessOutcome
      1 -> expectLiteral "negative" selected >> pure GrammarV1ReferenceNegativeOutcome
      2 -> expectLiteral "terminal" selected >> pure GrammarV1ReferenceTerminalOutcome
      3 -> expectLiteral "fatal" selected >> pure GrammarV1ReferenceFatalOutcome
      _ -> failCallable ("outcome_kind alternative out of range: " <> showText index)
    _ -> failCallable "outcome_kind body is not an alternative node"

parseOutcomeSpec
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError GrammarV1ReferenceOutcomeSpecCore
parseOutcomeSpec tree = do
  fields <- namedSequence "outcome_spec" tree
  case fields of
    [kindTree, typeTree] -> do
      kind <- parseOutcomeKind kindTree
      sourceType <- mapType (grammarV1ReferenceTypePayload typeTree)
      pure GrammarV1ReferenceOutcomeSpecCore
        { grammarV1ReferenceOutcomeSpecKindCore = kind
        , grammarV1ReferenceOutcomeSpecTypeCore = sourceType
        }
    _ -> failCallable "outcome_spec body is not a two-item sequence"

parseOutcomeSet
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError [GrammarV1ReferenceOutcomeSpecCore]
parseOutcomeSet tree = do
  fields <- namedSequence "outcome_set" tree
  case fields of
    [openBrace, optionalValues, closeBrace] -> do
      expectLiteral "{" openBrace
      values <- parseOptionalCommaList "outcome_set" parseOutcomeSpec optionalValues
      expectLiteral "}" closeBrace
      pure values
    _ -> failCallable "outcome_set body is not a three-item sequence"

parseNameSet
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError [[Text]]
parseNameSet tree = do
  fields <- namedSequence "name_set" tree
  case fields of
    [openBrace, optionalValues, closeBrace] -> do
      expectLiteral "{" openBrace
      values <- parseOptionalCommaList "name_set" parseQualifiedName optionalValues
      expectLiteral "}" closeBrace
      pure values
    _ -> failCallable "name_set body is not a three-item sequence"

parseTypeSet
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError [GrammarV1ReferenceTypePayload]
parseTypeSet tree = do
  fields <- namedSequence "type_set" tree
  case fields of
    [openBrace, optionalValues, closeBrace] -> do
      expectLiteral "{" openBrace
      values <- parseOptionalCommaList "type_set" (mapType . grammarV1ReferenceTypePayload) optionalValues
      expectLiteral "}" closeBrace
      pure values
    _ -> failCallable "type_set body is not a three-item sequence"

parseOptionalCommaList
  :: Text
  -> (GrammarV1ReferenceParseTree -> Either GrammarV1ReferenceCallableContractError a)
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError [a]
parseOptionalCommaList label parseValue tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure []
  GrammarV1ReferenceOptionalSome payload -> do
    fields <- expectSequence (label <> " values") payload
    case fields of
      [firstTree, restTree] -> do
        first <- parseValue firstTree
        restItems <- expectRepetition (label <> " suffixes") restTree
        rest <- traverse parseSuffix restItems
        pure (first : rest)
      _ -> failCallable (label <> " values are not a two-item sequence")
  _ -> failCallable (label <> " values slot is not optional")
  where
    parseSuffix suffixTree = do
      suffixFields <- expectSequence (label <> " suffix") suffixTree
      case suffixFields of
        [comma, valueTree] -> do
          expectLiteral "," comma
          parseValue valueTree
        _ -> failCallable (label <> " suffix is not a two-item sequence")

parseQualifiedName
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError [Text]
parseQualifiedName tree = do
  fields <- namedSequence "qualified_name" tree
  case fields of
    [firstTree, restTree] -> do
      first <- mapCommon (grammarV1ReferenceIdentifierCore firstTree)
      restItems <- expectRepetition "qualified_name suffixes" restTree
      rest <- traverse parseQualifiedNameSuffix restItems
      pure (first : rest)
    _ -> failCallable "qualified_name body is not a two-item sequence"

parseQualifiedNameSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError Text
parseQualifiedNameSuffix tree = do
  fields <- expectSequence "qualified_name suffix" tree
  case fields of
    [dot, nameTree] -> do
      expectLiteral "." dot
      mapCommon (grammarV1ReferenceIdentifierCore nameTree)
    _ -> failCallable "qualified_name suffix is not a two-item sequence"

parseStateSlot
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError GrammarV1ReferenceStateSlotCore
parseStateSlot tree = do
  fields <- namedSequence "state_slot" tree
  case fields of
    [nameTree, colon, typeTree] -> do
      name <- mapCommon (grammarV1ReferenceIdentifierCore nameTree)
      expectLiteral ":" colon
      sourceType <- mapType (grammarV1ReferenceTypePayload typeTree)
      pure GrammarV1ReferenceStateSlotCore
        { grammarV1ReferenceStateSlotNameCore = name
        , grammarV1ReferenceStateSlotTypeCore = sourceType
        }
    _ -> failCallable "state_slot body is not a three-item sequence"

parseCalleeTransition
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError GrammarV1ReferenceCalleeTransitionCore
parseCalleeTransition tree = do
  body <- expectNonterminal "callee_transition" tree
  case body of
    GrammarV1ReferenceAlternative index selected -> case index of
      0 -> expectLiteral "preserve" selected >> pure GrammarV1ReferenceCalleePreserve
      1 -> expectLiteral "consume" selected >> pure GrammarV1ReferenceCalleeConsume
      2 -> do
        fields <- expectSequence "replace callee transition" selected
        case fields of
          [replaceKeyword, withKeyword, referenceTree, stateTree] -> do
            expectLiteral "replace" replaceKeyword
            expectLiteral "with" withKeyword
            reference <- mapStatic (grammarV1ReferenceStaticReferenceSpine referenceTree)
            state <- case stateTree of
              GrammarV1ReferenceOptionalNone -> pure Nothing
              GrammarV1ReferenceOptionalSome payload -> do
                stateFields <- expectSequence "callee replacement state" payload
                case stateFields of
                  [stateKeyword, expressionTree] -> do
                    expectLiteral "state" stateKeyword
                    Just <$> mapExpression (grammarV1ReferenceExpressionCore expressionTree)
                  _ -> failCallable "callee replacement state is not a two-item sequence"
              _ -> failCallable "callee replacement state slot is not optional"
            pure (GrammarV1ReferenceCalleeReplace reference state)
          _ -> failCallable "replace callee transition is not a four-item sequence"
      _ -> failCallable ("callee_transition alternative out of range: " <> showText index)
    _ -> failCallable "callee_transition body is not an alternative node"

parseOutcomeResidue
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError GrammarV1ReferenceOutcomeResidueCore
parseOutcomeResidue tree = do
  fields <- namedSequence "outcome_residue" tree
  case fields of
    [outcomeKeyword, kindTree, typeTree, openBrace, clausesTree, closeBrace] -> do
      expectLiteral "outcome" outcomeKeyword
      kind <- parseOutcomeKind kindTree
      sourceType <- mapType (grammarV1ReferenceTypePayload typeTree)
      expectLiteral "{" openBrace
      clauses <- expectRepetition "outcome residue clauses" clausesTree
        >>= traverse parseOutcomeResidueClause
      expectLiteral "}" closeBrace
      pure GrammarV1ReferenceOutcomeResidueCore
        { grammarV1ReferenceOutcomeResidueKindCore = kind
        , grammarV1ReferenceOutcomeResidueTypeCore = sourceType
        , grammarV1ReferenceOutcomeResidueClausesCore = clauses
        }
    _ -> failCallable "outcome_residue body is not a six-item sequence"

parseOutcomeResidueClause
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError GrammarV1ReferenceOutcomeResidueClauseCore
parseOutcomeResidueClause tree = do
  body <- expectNonterminal "outcome_residue_clause" tree
  case body of
    GrammarV1ReferenceAlternative index selected -> case index of
      0 -> GrammarV1ReferenceOutcomeState <$> parseStateClause selected
      1 -> GrammarV1ReferenceOutcomeCallee <$> parseKeywordCallee "callee" selected
      2 -> GrammarV1ReferenceOutcomeEnsures <$> parseKeywordProposition "ensures" selected
      3 -> GrammarV1ReferenceOutcomeObligation <$> parseKeywordProposition "obligation" selected
      _ -> failCallable ("outcome_residue_clause alternative out of range: " <> showText index)
    _ -> failCallable "outcome_residue_clause body is not an alternative node"

parseStateClause
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError [GrammarV1ReferenceStateSlotCore]
parseStateClause tree = do
  fields <- expectSequence "outcome state clause" tree
  case fields of
    [stateKeyword, openParen, optionalValues, closeParen, terminator] -> do
      expectLiteral "state" stateKeyword
      expectLiteral "(" openParen
      values <- parseOptionalCommaList "state slots" parseStateSlot optionalValues
      expectLiteral ")" closeParen
      expectLiteral ";" terminator
      pure values
    _ -> failCallable "outcome state clause is not a five-item sequence"

grammarV1ProductionCallableContractDeclarations
  :: GrammarV1SourceFile
  -> [GrammarV1ReferenceCallableContractDeclaration]
grammarV1ProductionCallableContractDeclarations sourceFile =
  [ value
  | locatedTopLevel <- grammarV1TopLevelDecls sourceFile
  , let declaration = locatedValue (grammarV1Declaration (locatedValue locatedTopLevel))
  , Just value <- [grammarV1ProductionCallableContractDeclaration declaration]
  ]

grammarV1ReferenceCallableContractDeclarations
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError
      [GrammarV1ReferenceCallableContractDeclaration]
grammarV1ReferenceCallableContractDeclarations tree = do
  body <- expectNonterminal "source_file" tree
  fields <- expectSequence "source_file" body
  case fields of
    [_moduleTree, _importsTree, topLevelsTree] -> do
      topLevels <- expectRepetition "source_file top levels" topLevelsTree
      values <- traverse parseTopLevel topLevels
      pure [value | Just value <- values]
    _ -> failCallable "source_file body is not a three-item sequence"
  where
    parseTopLevel topLevelTree = do
      topBody <- expectNonterminal "top_level_decl" topLevelTree
      topFields <- expectSequence "top_level_decl" topBody
      case topFields of
        [_attributesTree, declarationTree] ->
          grammarV1ReferenceCallableContractDeclaration declarationTree
        _ -> failCallable "top_level_decl body is not a two-item sequence"

namedSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError [GrammarV1ReferenceParseTree]
namedSequence name tree = expectNonterminal name tree >>= expectSequence name

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> pure body
    | otherwise -> failCallable ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failCallable ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence values -> pure values
  _ -> failCallable (label <> " is not a sequence node")

expectRepetition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError [GrammarV1ReferenceParseTree]
expectRepetition label tree = case tree of
  GrammarV1ReferenceRepetition values -> pure values
  _ -> failCallable (label <> " is not a repetition node")

expectLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceCallableContractError ()
expectLiteral expected tree = case tree of
  GrammarV1ReferenceLiteral actual
    | actual == expected -> pure ()
    | otherwise -> failCallable ("expected literal " <> expected <> ", got " <> actual)
  _ -> failCallable ("expected literal " <> expected)

mapCommon :: Show e => Either e a -> Either GrammarV1ReferenceCallableContractError a
mapCommon = mapNested "declaration-common"

mapTermParams :: Show e => Either e a -> Either GrammarV1ReferenceCallableContractError a
mapTermParams = mapNested "term-params"

mapType :: Show e => Either e a -> Either GrammarV1ReferenceCallableContractError a
mapType = mapNested "type"

mapProposition :: Show e => Either e a -> Either GrammarV1ReferenceCallableContractError a
mapProposition = mapNested "proposition"

mapEffects :: Show e => Either e a -> Either GrammarV1ReferenceCallableContractError a
mapEffects = mapNested "effects"

mapExpression :: Show e => Either e a -> Either GrammarV1ReferenceCallableContractError a
mapExpression = mapNested "expression"

mapStatic :: Show e => Either e a -> Either GrammarV1ReferenceCallableContractError a
mapStatic = mapNested "static-reference"

mapNested
  :: Show e
  => Text
  -> Either e a
  -> Either GrammarV1ReferenceCallableContractError a
mapNested label result = case result of
  Left errorValue -> failCallable
    (label <> " correspondence failed: " <> Text.pack (show errorValue))
  Right value -> pure value

showText :: Show a => a -> Text
showText = Text.pack . show

failCallable
  :: Text
  -> Either GrammarV1ReferenceCallableContractError a
failCallable = Left . GrammarV1ReferenceCallableContractError
