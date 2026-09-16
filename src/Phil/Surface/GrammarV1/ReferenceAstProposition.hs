{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstProposition
  ( GrammarV1ReferencePropositionError (..)
  , GrammarV1ReferenceRelationOperator (..)
  , GrammarV1ReferencePropositionCore (..)
  , GrammarV1ReferenceTypeAliasPropositions (..)
  , grammarV1ProductionPropositionCore
  , grammarV1ReferencePropositionCore
  , grammarV1ProductionTypeAliasPropositions
  , grammarV1ReferenceTypeAliasPropositions
  ) where

import Control.Monad (foldM)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Declaration (..)
  , GrammarV1GenericRequirement (..)
  , GrammarV1Proposition (..)
  , GrammarV1RelationOperator (..)
  , GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..)
  , GrammarV1Type (..)
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

newtype GrammarV1ReferencePropositionError =
  GrammarV1ReferencePropositionError Text
  deriving (Eq, Show)

data GrammarV1ReferenceRelationOperator
  = GrammarV1ReferenceEqualRelation
  | GrammarV1ReferenceNotEqualRelation
  | GrammarV1ReferenceLessEqualRelation
  | GrammarV1ReferenceGreaterEqualRelation
  | GrammarV1ReferenceLessRelation
  | GrammarV1ReferenceGreaterRelation
  | GrammarV1ReferenceInRelation
  | GrammarV1ReferenceDisjointRelation
  deriving (Eq, Ord, Show)

data GrammarV1ReferencePropositionCore
  = GrammarV1ReferenceTrueProposition
  | GrammarV1ReferenceFalseProposition
  | GrammarV1ReferenceRelationProposition
      GrammarV1ReferenceExpressionCore
      GrammarV1ReferenceRelationOperator
      GrammarV1ReferenceExpressionCore
  | GrammarV1ReferenceClaimApplicationProposition
      GrammarV1ReferenceStaticReferenceSpine
      [GrammarV1ReferenceExpressionCore]
  | GrammarV1ReferenceNotProposition GrammarV1ReferencePropositionCore
  | GrammarV1ReferenceAndProposition
      GrammarV1ReferencePropositionCore
      GrammarV1ReferencePropositionCore
  | GrammarV1ReferenceOrProposition
      GrammarV1ReferencePropositionCore
      GrammarV1ReferencePropositionCore
  deriving (Eq, Show)

data GrammarV1ReferenceTypeAliasPropositions = GrammarV1ReferenceTypeAliasPropositions
  { grammarV1ReferenceTypeAliasRequirementPropositions :: [GrammarV1ReferencePropositionCore]
  , grammarV1ReferenceTypeAliasTargetPropositions :: [GrammarV1ReferencePropositionCore]
  }
  deriving (Eq, Show)

grammarV1ProductionPropositionCore
  :: GrammarV1Proposition
  -> GrammarV1ReferencePropositionCore
grammarV1ProductionPropositionCore proposition = case proposition of
  GrammarV1TrueProposition -> GrammarV1ReferenceTrueProposition
  GrammarV1FalseProposition -> GrammarV1ReferenceFalseProposition
  GrammarV1RelationProposition left operator right ->
    GrammarV1ReferenceRelationProposition
      (grammarV1ProductionExpressionCore (locatedValue left))
      (productionRelationOperator (locatedValue operator))
      (grammarV1ProductionExpressionCore (locatedValue right))
  GrammarV1ClaimApplicationProposition reference arguments ->
    GrammarV1ReferenceClaimApplicationProposition
      (grammarV1ProductionStaticReferenceSpine reference)
      (map (grammarV1ProductionExpressionCore . locatedValue) arguments)
  GrammarV1NotProposition inner ->
    GrammarV1ReferenceNotProposition
      (grammarV1ProductionPropositionCore (locatedValue inner))
  GrammarV1AndProposition left right ->
    GrammarV1ReferenceAndProposition
      (grammarV1ProductionPropositionCore (locatedValue left))
      (grammarV1ProductionPropositionCore (locatedValue right))
  GrammarV1OrProposition left right ->
    GrammarV1ReferenceOrProposition
      (grammarV1ProductionPropositionCore (locatedValue left))
      (grammarV1ProductionPropositionCore (locatedValue right))

productionRelationOperator
  :: GrammarV1RelationOperator
  -> GrammarV1ReferenceRelationOperator
productionRelationOperator operator = case operator of
  GrammarV1EqualRelation -> GrammarV1ReferenceEqualRelation
  GrammarV1NotEqualRelation -> GrammarV1ReferenceNotEqualRelation
  GrammarV1LessEqualRelation -> GrammarV1ReferenceLessEqualRelation
  GrammarV1GreaterEqualRelation -> GrammarV1ReferenceGreaterEqualRelation
  GrammarV1LessRelation -> GrammarV1ReferenceLessRelation
  GrammarV1GreaterRelation -> GrammarV1ReferenceGreaterRelation
  GrammarV1InRelation -> GrammarV1ReferenceInRelation
  GrammarV1DisjointRelation -> GrammarV1ReferenceDisjointRelation

grammarV1ReferencePropositionCore
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError GrammarV1ReferencePropositionCore
grammarV1ReferencePropositionCore tree = do
  body <- expectNonterminal "proposition" tree
  parsePropositionOr body

parsePropositionOr
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError GrammarV1ReferencePropositionCore
parsePropositionOr tree = do
  body <- expectNonterminal "proposition_or" tree
  fields <- expectSequence "proposition_or" body
  case fields of
    [firstTree, restTree] -> do
      first <- parsePropositionAnd firstTree
      rest <- expectRepetition "proposition_or suffix" restTree
      foldM applyOrSuffix first rest
    _ -> failProposition "proposition_or body is not a two-item sequence"

applyOrSuffix
  :: GrammarV1ReferencePropositionCore
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError GrammarV1ReferencePropositionCore
applyOrSuffix left tree = do
  fields <- expectSequence "proposition_or suffix" tree
  case fields of
    [orKeyword, rightTree] -> do
      expectLiteral "or" orKeyword
      right <- parsePropositionAnd rightTree
      pure (GrammarV1ReferenceOrProposition left right)
    _ -> failProposition "proposition_or suffix is not a two-item sequence"

parsePropositionAnd
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError GrammarV1ReferencePropositionCore
parsePropositionAnd tree = do
  body <- expectNonterminal "proposition_and" tree
  fields <- expectSequence "proposition_and" body
  case fields of
    [firstTree, restTree] -> do
      first <- parsePropositionNot firstTree
      rest <- expectRepetition "proposition_and suffix" restTree
      foldM applyAndSuffix first rest
    _ -> failProposition "proposition_and body is not a two-item sequence"

applyAndSuffix
  :: GrammarV1ReferencePropositionCore
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError GrammarV1ReferencePropositionCore
applyAndSuffix left tree = do
  fields <- expectSequence "proposition_and suffix" tree
  case fields of
    [andKeyword, rightTree] -> do
      expectLiteral "and" andKeyword
      right <- parsePropositionNot rightTree
      pure (GrammarV1ReferenceAndProposition left right)
    _ -> failProposition "proposition_and suffix is not a two-item sequence"

parsePropositionNot
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError GrammarV1ReferencePropositionCore
parsePropositionNot tree = do
  body <- expectNonterminal "proposition_not" tree
  case body of
    GrammarV1ReferenceAlternative 0 selected -> do
      fields <- expectSequence "not proposition" selected
      case fields of
        [notKeyword, innerTree] -> do
          expectLiteral "not" notKeyword
          inner <- parsePropositionNot innerTree
          pure (GrammarV1ReferenceNotProposition inner)
        _ -> failProposition "not proposition is not a two-item sequence"
    GrammarV1ReferenceAlternative 1 atomTree -> parsePropositionAtom atomTree
    GrammarV1ReferenceAlternative index _ ->
      failProposition ("proposition_not alternative out of range: " <> showText index)
    _ -> failProposition "proposition_not body is not an alternative node"

parsePropositionAtom
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError GrammarV1ReferencePropositionCore
parsePropositionAtom tree = do
  body <- expectNonterminal "proposition_atom" tree
  case body of
    GrammarV1ReferenceAlternative index selected -> case index of
      0 -> parseRelationProposition selected
      1 -> parseParenthesizedProposition selected
      2 -> expectLiteral "true" selected >> pure GrammarV1ReferenceTrueProposition
      3 -> expectLiteral "false" selected >> pure GrammarV1ReferenceFalseProposition
      4 -> parseClaimApplication selected
      _ -> failProposition
        ("proposition_atom alternative out of range: " <> showText index)
    _ -> failProposition "proposition_atom body is not an alternative node"

parseParenthesizedProposition
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError GrammarV1ReferencePropositionCore
parseParenthesizedProposition tree = do
  fields <- expectSequence "parenthesized proposition" tree
  case fields of
    [openParen, propositionTree, closeParen] -> do
      expectLiteral "(" openParen
      proposition <- grammarV1ReferencePropositionCore propositionTree
      expectLiteral ")" closeParen
      -- Production intentionally carries no parenthesized-proposition constructor.
      pure proposition
    _ -> failProposition "parenthesized proposition is not a three-item sequence"

parseRelationProposition
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError GrammarV1ReferencePropositionCore
parseRelationProposition tree = do
  body <- expectNonterminal "relation_proposition" tree
  fields <- expectSequence "relation_proposition" body
  case fields of
    [leftTree, operatorTree, rightTree] -> do
      left <- referenceShiftExpressionCore leftTree
      operator <- parseRelationOperator operatorTree
      right <- referenceShiftExpressionCore rightTree
      pure (GrammarV1ReferenceRelationProposition left operator right)
    _ -> failProposition "relation_proposition body is not a three-item sequence"

referenceShiftExpressionCore
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError GrammarV1ReferenceExpressionCore
referenceShiftExpressionCore shiftTree = mapExpressionError
  (grammarV1ReferenceExpressionCore
    (GrammarV1ReferenceNonterminal
      "expression"
      (GrammarV1ReferenceSequence
        [ GrammarV1ReferenceNonterminal
            "base_expression"
            (GrammarV1ReferenceAlternative 1 shiftTree)
        , GrammarV1ReferenceOptionalNone
        ])))

parseRelationOperator
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError GrammarV1ReferenceRelationOperator
parseRelationOperator tree = do
  body <- expectNonterminal "relation_operator" tree
  case body of
    GrammarV1ReferenceAlternative index selected -> case index of
      0 -> expectLiteral "==" selected >> pure GrammarV1ReferenceEqualRelation
      1 -> expectLiteral "!=" selected >> pure GrammarV1ReferenceNotEqualRelation
      2 -> expectLiteral "<=" selected >> pure GrammarV1ReferenceLessEqualRelation
      3 -> expectLiteral ">=" selected >> pure GrammarV1ReferenceGreaterEqualRelation
      4 -> expectLiteral "<" selected >> pure GrammarV1ReferenceLessRelation
      5 -> expectLiteral ">" selected >> pure GrammarV1ReferenceGreaterRelation
      6 -> expectLiteral "in" selected >> pure GrammarV1ReferenceInRelation
      7 -> expectLiteral "disjoint" selected >> pure GrammarV1ReferenceDisjointRelation
      _ -> failProposition
        ("relation_operator alternative out of range: " <> showText index)
    _ -> failProposition "relation_operator body is not an alternative node"

parseClaimApplication
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError GrammarV1ReferencePropositionCore
parseClaimApplication tree = do
  body <- expectNonterminal "claim_application" tree
  fields <- expectSequence "claim_application" body
  case fields of
    [referenceTree, openParen, optionalArguments, closeParen] -> do
      reference <- mapStaticReferenceError
        (grammarV1ReferenceStaticReferenceSpine referenceTree)
      expectLiteral "(" openParen
      arguments <- parseOptionalExpressionList optionalArguments
      expectLiteral ")" closeParen
      pure (GrammarV1ReferenceClaimApplicationProposition reference arguments)
    _ -> failProposition "claim_application body is not a four-item sequence"

parseOptionalExpressionList
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError [GrammarV1ReferenceExpressionCore]
parseOptionalExpressionList tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure []
  GrammarV1ReferenceOptionalSome valuesTree -> do
    fields <- expectSequence "expression list" valuesTree
    case fields of
      [firstTree, restTree] -> do
        first <- mapExpressionError (grammarV1ReferenceExpressionCore firstTree)
        restItems <- expectRepetition "expression list suffix" restTree
        rest <- traverse parseExpressionListSuffix restItems
        pure (first : rest)
      _ -> failProposition "expression list is not a two-item sequence"
  _ -> failProposition "expression list slot is not optional"

parseExpressionListSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError GrammarV1ReferenceExpressionCore
parseExpressionListSuffix tree = do
  fields <- expectSequence "expression list suffix" tree
  case fields of
    [comma, expressionTree] -> do
      expectLiteral "," comma
      mapExpressionError (grammarV1ReferenceExpressionCore expressionTree)
    _ -> failProposition "expression list suffix is not a two-item sequence"

grammarV1ProductionTypeAliasPropositions
  :: GrammarV1SourceFile
  -> [GrammarV1ReferenceTypeAliasPropositions]
grammarV1ProductionTypeAliasPropositions sourceFile =
  [ GrammarV1ReferenceTypeAliasPropositions
      { grammarV1ReferenceTypeAliasRequirementPropositions =
          concatMap (productionRequirementPropositions . locatedValue)
            (grammarV1TypeAliasRequirements alias)
      , grammarV1ReferenceTypeAliasTargetPropositions =
          productionTypePropositions (locatedValue (grammarV1TypeAliasTarget alias))
      }
  | locatedTopLevel <- grammarV1TopLevelDecls sourceFile
  , let topLevel = locatedValue locatedTopLevel
  , GrammarV1TypeAliasDeclaration alias <-
      [locatedValue (grammarV1Declaration topLevel)]
  ]

productionRequirementPropositions
  :: GrammarV1GenericRequirement
  -> [GrammarV1ReferencePropositionCore]
productionRequirementPropositions requirement = case requirement of
  GrammarV1PropositionRequirement proposition -> one proposition
  GrammarV1RepresentationRequirement proposition -> one proposition
  GrammarV1PlacementRequirement proposition -> one proposition
  GrammarV1CostRequirement proposition -> one proposition
  GrammarV1EnvironmentRequirement proposition -> one proposition
  _ -> []
  where
    one = pure . grammarV1ProductionPropositionCore . locatedValue

productionTypePropositions
  :: GrammarV1Type
  -> [GrammarV1ReferencePropositionCore]
productionTypePropositions sourceType = case sourceType of
  GrammarV1ProofType proposition ->
    [grammarV1ProductionPropositionCore (locatedValue proposition)]
  GrammarV1RefinementType _ baseType proposition ->
    productionTypePropositions (locatedValue baseType)
      <> [grammarV1ProductionPropositionCore (locatedValue proposition)]
  GrammarV1TupleType elements ->
    concatMap (productionTypePropositions . locatedValue) elements
  _ -> []

grammarV1ReferenceTypeAliasPropositions
  :: GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferencePropositionError
      [GrammarV1ReferenceTypeAliasPropositions]
grammarV1ReferenceTypeAliasPropositions tree = do
  sourceBody <- expectNonterminal "source_file" tree
  sourceFields <- expectSequence "source_file" sourceBody
  case sourceFields of
    [_moduleTree, _importTree, topLevelTree] -> do
      topLevels <- expectRepetition "source_file top levels" topLevelTree
      values <- traverse parseTopLevelTypeAliasPropositions topLevels
      pure [value | Just value <- values]
    _ -> failProposition "source_file body is not a three-item sequence"

parseTopLevelTypeAliasPropositions
  :: GrammarV1ReferenceParseTree
  -> Either
      GrammarV1ReferencePropositionError
      (Maybe GrammarV1ReferenceTypeAliasPropositions)
parseTopLevelTypeAliasPropositions tree = do
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
              Just <$> parseTypeAliasPropositions selected
            _ -> failProposition
              "type-alias declaration does not occupy alternative 2"
        _ -> pure Nothing
    _ -> failProposition "top_level_decl body is not a two-item sequence"

parseTypeAliasPropositions
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError GrammarV1ReferenceTypeAliasPropositions
parseTypeAliasPropositions tree = do
  body <- expectNonterminal "type_alias_decl" tree
  fields <- expectSequence "type_alias_decl" body
  case fields of
    [_keyword, _name, _generic, requirementTree, _equals, targetTree, _terminator] -> do
      requirements <- referenceRequirementPropositions requirementTree
      targets <- referenceTypePropositions targetTree
      pure GrammarV1ReferenceTypeAliasPropositions
        { grammarV1ReferenceTypeAliasRequirementPropositions = requirements
        , grammarV1ReferenceTypeAliasTargetPropositions = targets
        }
    _ -> failProposition "type_alias_decl body is not a seven-item sequence"

referenceRequirementPropositions
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError [GrammarV1ReferencePropositionCore]
referenceRequirementPropositions tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure []
  GrammarV1ReferenceOptionalSome requirementsTree -> do
    body <- expectNonterminal "generic_requirements" requirementsTree
    fields <- expectSequence "generic_requirements" body
    case fields of
      [requiresKeyword, openBrace, entriesTree, closeBrace] -> do
        expectLiteral "requires" requiresKeyword
        expectLiteral "{" openBrace
        entries <- expectRepetition "generic_requirements entries" entriesTree
        values <- traverse referenceGenericRequirementProposition entries
        expectLiteral "}" closeBrace
        pure [value | Just value <- values]
      _ -> failProposition
        "generic_requirements body is not a four-item sequence"
  _ -> failProposition "type_alias_decl requirement slot is not optional"

referenceGenericRequirementProposition
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError (Maybe GrammarV1ReferencePropositionCore)
referenceGenericRequirementProposition tree = do
  body <- expectNonterminal "generic_requirement" tree
  case body of
    GrammarV1ReferenceAlternative index selected
      | index == 1 -> Just <$> propositionRequirement "proposition" selected
      | index == 9 -> Just <$> propositionRequirement "representation" selected
      | index == 10 -> Just <$> propositionRequirement "placement" selected
      | index == 11 -> Just <$> propositionRequirement "cost" selected
      | index == 12 -> Just <$> propositionRequirement "environment" selected
      | index >= 0 && index <= 12 -> pure Nothing
      | otherwise -> failProposition
          ("generic_requirement alternative out of range: " <> showText index)
    _ -> failProposition "generic_requirement body is not an alternative node"

propositionRequirement
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError GrammarV1ReferencePropositionCore
propositionRequirement keyword tree = do
  fields <- expectSequence (keyword <> " requirement") tree
  case fields of
    [keywordTree, propositionTree, terminator] -> do
      expectLiteral keyword keywordTree
      proposition <- grammarV1ReferencePropositionCore propositionTree
      expectLiteral ";" terminator
      pure proposition
    _ -> failProposition
      (keyword <> " requirement is not a three-item sequence")

referenceTypePropositions
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError [GrammarV1ReferencePropositionCore]
referenceTypePropositions tree = do
  body <- expectNonterminal "type_expression" tree
  case body of
    GrammarV1ReferenceAlternative 0 nonreference -> do
      nonreferenceBody <- expectNonterminal "nonreference_type_expression" nonreference
      case nonreferenceBody of
        GrammarV1ReferenceAlternative 9 proofTree -> referenceProofPropositions proofTree
        GrammarV1ReferenceAlternative 11 refinementTree ->
          referenceRefinementPropositions refinementTree
        GrammarV1ReferenceAlternative 12 tupleTree -> referenceTupleTypePropositions tupleTree
        GrammarV1ReferenceAlternative _ _ -> pure []
        _ -> failProposition
          "nonreference_type_expression body is not an alternative node"
    GrammarV1ReferenceAlternative 1 _named -> pure []
    GrammarV1ReferenceAlternative index _ ->
      failProposition ("type_expression alternative out of range: " <> showText index)
    _ -> failProposition "type_expression body is not an alternative node"

referenceProofPropositions
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError [GrammarV1ReferencePropositionCore]
referenceProofPropositions tree = do
  fields <- expectSequence "Proof type" tree
  case fields of
    [proofKeyword, openBracket, propositionTree, closeBracket] -> do
      expectLiteral "Proof" proofKeyword
      expectLiteral "[" openBracket
      proposition <- grammarV1ReferencePropositionCore propositionTree
      expectLiteral "]" closeBracket
      pure [proposition]
    _ -> failProposition "Proof type is not a four-item sequence"

referenceRefinementPropositions
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError [GrammarV1ReferencePropositionCore]
referenceRefinementPropositions tree = do
  body <- expectNonterminal "refinement_type" tree
  fields <- expectSequence "refinement_type" body
  case fields of
    [_openBrace, _binder, _colon, baseTypeTree, _bar, propositionTree, _closeBrace] -> do
      base <- referenceTypePropositions baseTypeTree
      proposition <- grammarV1ReferencePropositionCore propositionTree
      pure (base <> [proposition])
    _ -> failProposition "refinement_type body is not a seven-item sequence"

referenceTupleTypePropositions
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError [GrammarV1ReferencePropositionCore]
referenceTupleTypePropositions tree = do
  body <- expectNonterminal "tuple_type" tree
  fields <- expectSequence "tuple_type" body
  case fields of
    [_openParen, firstTree, _firstComma, secondTree, restTree, _closeParen] -> do
      first <- referenceTypePropositions firstTree
      second <- referenceTypePropositions secondTree
      restItems <- expectRepetition "tuple_type suffix" restTree
      rest <- fmap concat (traverse referenceTupleTypeSuffixPropositions restItems)
      pure (first <> second <> rest)
    _ -> failProposition "tuple_type body is not a six-item sequence"

referenceTupleTypeSuffixPropositions
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError [GrammarV1ReferencePropositionCore]
referenceTupleTypeSuffixPropositions tree = do
  fields <- expectSequence "tuple_type suffix" tree
  case fields of
    [_comma, typeTree] -> referenceTypePropositions typeTree
    _ -> failProposition "tuple_type suffix is not a two-item sequence"

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> pure body
    | otherwise -> failProposition
        ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failProposition ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence items -> pure items
  _ -> failProposition (label <> " is not a sequence node")

expectRepetition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError [GrammarV1ReferenceParseTree]
expectRepetition label tree = case tree of
  GrammarV1ReferenceRepetition items -> pure items
  _ -> failProposition (label <> " is not a repetition node")

expectLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferencePropositionError ()
expectLiteral expected tree = case tree of
  GrammarV1ReferenceLiteral actual
    | actual == expected -> pure ()
    | otherwise -> failProposition
        ("expected literal " <> expected <> ", got " <> actual)
  _ -> failProposition ("expected literal " <> expected)

mapExpressionError
  :: Either GrammarV1ReferenceExpressionCoreError a
  -> Either GrammarV1ReferencePropositionError a
mapExpressionError = mapLeft
  (GrammarV1ReferencePropositionError . Text.pack . show)

mapStaticReferenceError
  :: Either GrammarV1ReferenceStaticReferenceError a
  -> Either GrammarV1ReferencePropositionError a
mapStaticReferenceError = mapLeft
  (GrammarV1ReferencePropositionError . Text.pack . show)

mapTopLevelError
  :: Show e
  => Either e a
  -> Either GrammarV1ReferencePropositionError a
mapTopLevelError = mapLeft
  (GrammarV1ReferencePropositionError . Text.pack . show)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value

showText :: Show a => a -> Text
showText = Text.pack . show

failProposition
  :: Text
  -> Either GrammarV1ReferencePropositionError a
failProposition = Left . GrammarV1ReferencePropositionError
