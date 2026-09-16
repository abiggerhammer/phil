{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstFixedCommandHelpers
  ( GrammarV1ReferenceFixedCommandHelperError (..)
  , GrammarV1ReferenceBranchValueCore (..)
  , GrammarV1ReferenceFixedCommandHelper (..)
  , grammarV1ProductionFixedCommandHelper
  , grammarV1ReferenceFixedCommandHelper
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1BranchValue (..)
  , GrammarV1Expression (..)
  , GrammarV1FailureTarget (..)
  , GrammarV1QualifiedName (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstExpressionCore
  ( GrammarV1ReferenceExpressionCore
  , GrammarV1ReferenceExpressionCoreError
  , GrammarV1ReferenceFailureTarget (..)
  , grammarV1ProductionExpressionCore
  , grammarV1ReferenceExpressionCore
  )
import Phil.Surface.GrammarV1.ReferenceAstStaticReference
  ( GrammarV1ReferenceStaticReferenceError
  , GrammarV1ReferenceStaticReferenceSpine
  , grammarV1ProductionStaticReferenceSpine
  , grammarV1ReferenceStaticReferenceSpine
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( GrammarV1ReferenceParseTree (..)
  )
import Phil.Surface.Syntax (Located (..))

newtype GrammarV1ReferenceFixedCommandHelperError =
  GrammarV1ReferenceFixedCommandHelperError Text
  deriving (Eq, Show)

data GrammarV1ReferenceBranchValueCore = GrammarV1ReferenceBranchValueCore
  { grammarV1ReferenceBranchValueName :: [Text]
  , grammarV1ReferenceBranchValueArguments :: [GrammarV1ReferenceExpressionCore]
  }
  deriving (Eq, Show)

data GrammarV1ReferenceFixedCommandHelper
  = GrammarV1ReferenceConstruct
      GrammarV1ReferenceStaticReferenceSpine
      [(Text, GrammarV1ReferenceExpressionCore)]
  | GrammarV1ReferenceContinue [GrammarV1ReferenceExpressionCore]
  | GrammarV1ReferenceBreak [GrammarV1ReferenceExpressionCore]
  | GrammarV1ReferenceSelect
      GrammarV1ReferenceBranchValueCore
      (Maybe GrammarV1ReferenceExpressionCore)
      GrammarV1ReferenceExpressionCore
  | GrammarV1ReferenceFail
      GrammarV1ReferenceFailureTarget
      GrammarV1ReferenceExpressionCore
  deriving (Eq, Show)

grammarV1ProductionFixedCommandHelper
  :: GrammarV1Expression
  -> Maybe GrammarV1ReferenceFixedCommandHelper
grammarV1ProductionFixedCommandHelper expression = case expression of
  GrammarV1ConstructExpression target assignments ->
    Just (GrammarV1ReferenceConstruct
      (grammarV1ProductionStaticReferenceSpine (locatedValue target))
      [ (locatedValue field, productionExpression value)
      | (field, value) <- assignments
      ])
  GrammarV1ContinueExpression arguments ->
    Just (GrammarV1ReferenceContinue (map productionExpression arguments))
  GrammarV1BreakExpression arguments ->
    Just (GrammarV1ReferenceBreak (map productionExpression arguments))
  GrammarV1SelectExpression branch endpoint evidence ->
    Just (GrammarV1ReferenceSelect
      (productionBranchValue (locatedValue branch))
      (fmap productionExpression evidence)
      (productionExpression endpoint))
  GrammarV1FailExpression target endpoint ->
    Just (GrammarV1ReferenceFail
      (productionFailureTarget (locatedValue target))
      (productionExpression endpoint))
  _ -> Nothing
  where
    productionExpression = grammarV1ProductionExpressionCore . locatedValue

productionBranchValue :: GrammarV1BranchValue -> GrammarV1ReferenceBranchValueCore
productionBranchValue branch = GrammarV1ReferenceBranchValueCore
  { grammarV1ReferenceBranchValueName =
      grammarV1QualifiedNameParts (locatedValue (grammarV1BranchValueName branch))
  , grammarV1ReferenceBranchValueArguments =
      map (grammarV1ProductionExpressionCore . locatedValue)
        (grammarV1BranchValueArguments branch)
  }

productionFailureTarget
  :: GrammarV1FailureTarget
  -> GrammarV1ReferenceFailureTarget
productionFailureTarget target = GrammarV1ReferenceFailureTarget
  { grammarV1ReferenceFailureTargetReference =
      grammarV1ProductionStaticReferenceSpine
        (grammarV1FailureTargetReference target)
  , grammarV1ReferenceFailureTargetArguments =
      map (grammarV1ProductionExpressionCore . locatedValue)
        (grammarV1FailureTargetArguments target)
  }

grammarV1ReferenceFixedCommandHelper
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandHelperError
      (Maybe GrammarV1ReferenceFixedCommandHelper)
grammarV1ReferenceFixedCommandHelper tree = do
  body <- expectNonterminal "command_expression" tree
  case body of
    GrammarV1ReferenceAlternative index selected -> case index of
      0 -> Just <$> parseConstruct selected
      7 -> Just <$> parseContinue selected
      8 -> Just <$> parseBreak selected
      16 -> Just <$> parseSelect selected
      20 -> Just <$> parseFail selected
      _ | index >= 0 && index <= 26 -> pure Nothing
        | otherwise -> failHelper
            ("command_expression alternative out of range: " <> showText index)
    _ -> failHelper "command_expression body is not an alternative node"

parseConstruct
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandHelperError GrammarV1ReferenceFixedCommandHelper
parseConstruct tree = do
  fields <- namedSequence "construct_expression" tree
  case fields of
    [keyword, targetTree, openBrace, assignmentsTree, closeBrace] -> do
      expectLiteral "construct" keyword
      target <- mapStaticReferenceError
        (grammarV1ReferenceStaticReferenceSpine targetTree)
      expectLiteral "{" openBrace
      assignments <- parseOptionalAssignments assignmentsTree
      expectLiteral "}" closeBrace
      pure (GrammarV1ReferenceConstruct target assignments)
    _ -> failHelper "construct_expression body is not a five-item sequence"

parseOptionalAssignments
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandHelperError
      [(Text, GrammarV1ReferenceExpressionCore)]
parseOptionalAssignments tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure []
  GrammarV1ReferenceOptionalSome payload -> do
    fields <- expectSequence "field assignment list" payload
    case fields of
      [firstTree, restTree, trailingComma] -> do
        first <- parseFieldAssignment firstTree
        rest <- expectRepetition "field assignment suffixes" restTree
        suffixes <- traverse parseFieldAssignmentSuffix rest
        case trailingComma of
          GrammarV1ReferenceOptionalNone -> pure ()
          GrammarV1ReferenceOptionalSome commaTree -> expectLiteral "," commaTree
          _ -> failHelper "construct trailing comma slot is not optional"
        pure (first : suffixes)
      _ -> failHelper "construct assignment payload is not a three-item sequence"
  _ -> failHelper "construct assignment slot is not optional"

parseFieldAssignmentSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandHelperError
      (Text, GrammarV1ReferenceExpressionCore)
parseFieldAssignmentSuffix tree = do
  fields <- expectSequence "field assignment suffix" tree
  case fields of
    [commaTree, assignmentTree] ->
      expectLiteral "," commaTree >> parseFieldAssignment assignmentTree
    _ -> failHelper "field assignment suffix is not a two-item sequence"

parseFieldAssignment
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandHelperError
      (Text, GrammarV1ReferenceExpressionCore)
parseFieldAssignment tree = do
  fields <- namedSequence "field_assignment" tree
  case fields of
    [fieldTree, equalsTree, valueTree] -> do
      field <- parseIdentifier fieldTree
      expectLiteral "=" equalsTree
      value <- parseExpression valueTree
      pure (field, value)
    _ -> failHelper "field_assignment body is not a three-item sequence"

parseContinue, parseBreak
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandHelperError GrammarV1ReferenceFixedCommandHelper
parseContinue = parseControlArguments
  "continue_expression" "continue" GrammarV1ReferenceContinue
parseBreak = parseControlArguments
  "break_expression" "break" GrammarV1ReferenceBreak

parseControlArguments
  :: Text
  -> Text
  -> ([GrammarV1ReferenceExpressionCore] -> GrammarV1ReferenceFixedCommandHelper)
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandHelperError GrammarV1ReferenceFixedCommandHelper
parseControlArguments nonterminal keyword constructor tree = do
  fields <- namedSequence nonterminal tree
  case fields of
    [keywordTree, optionalArguments] -> do
      expectLiteral keyword keywordTree
      arguments <- case optionalArguments of
        GrammarV1ReferenceOptionalNone -> pure []
        GrammarV1ReferenceOptionalSome payload -> parseParenthesizedArguments payload
        _ -> failHelper (nonterminal <> " argument slot is not optional")
      pure (constructor arguments)
    _ -> failHelper (nonterminal <> " body is not a two-item sequence")

parseParenthesizedArguments
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandHelperError [GrammarV1ReferenceExpressionCore]
parseParenthesizedArguments tree = do
  fields <- expectSequence "parenthesized argument payload" tree
  case fields of
    [openParen, optionalValues, closeParen] -> do
      expectLiteral "(" openParen
      values <- parseOptionalExpressionList optionalValues
      expectLiteral ")" closeParen
      pure values
    _ -> failHelper "parenthesized argument payload is not a three-item sequence"

parseSelect
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandHelperError GrammarV1ReferenceFixedCommandHelper
parseSelect tree = do
  fields <- namedSequence "select_expression" tree
  case fields of
    [keyword, branchTree, optionalUsing, onKeyword, endpointTree] -> do
      expectLiteral "select" keyword
      branch <- parseBranchValue branchTree
      evidence <- parseOptionalKeywordBase "using" optionalUsing
      expectLiteral "on" onKeyword
      endpoint <- parseBase endpointTree
      pure (GrammarV1ReferenceSelect branch evidence endpoint)
    _ -> failHelper "select_expression body is not a five-item sequence"

parseBranchValue
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandHelperError GrammarV1ReferenceBranchValueCore
parseBranchValue tree = do
  fields <- namedSequence "branch_value" tree
  case fields of
    [nameTree, optionalArguments] -> do
      name <- parseQualifiedName nameTree
      arguments <- case optionalArguments of
        GrammarV1ReferenceOptionalNone -> pure []
        GrammarV1ReferenceOptionalSome termArgumentsTree ->
          parseTermArguments termArgumentsTree
        _ -> failHelper "branch_value argument slot is not optional"
      pure GrammarV1ReferenceBranchValueCore
        { grammarV1ReferenceBranchValueName = name
        , grammarV1ReferenceBranchValueArguments = arguments
        }
    _ -> failHelper "branch_value body is not a two-item sequence"

parseFail
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandHelperError GrammarV1ReferenceFixedCommandHelper
parseFail tree = do
  fields <- namedSequence "fail_expression" tree
  case fields of
    [keyword, targetTree, onKeyword, endpointTree] -> do
      expectLiteral "fail" keyword
      target <- parseFailureTarget targetTree
      expectLiteral "on" onKeyword
      endpoint <- parseBase endpointTree
      pure (GrammarV1ReferenceFail target endpoint)
    _ -> failHelper "fail_expression body is not a four-item sequence"

parseFailureTarget
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandHelperError GrammarV1ReferenceFailureTarget
parseFailureTarget tree = do
  fields <- namedSequence "failure_target" tree
  case fields of
    [referenceTree, optionalArguments] -> do
      reference <- mapStaticReferenceError
        (grammarV1ReferenceStaticReferenceSpine referenceTree)
      arguments <- case optionalArguments of
        GrammarV1ReferenceOptionalNone -> pure []
        GrammarV1ReferenceOptionalSome termArgumentsTree ->
          parseTermArguments termArgumentsTree
        _ -> failHelper "failure_target argument slot is not optional"
      pure GrammarV1ReferenceFailureTarget
        { grammarV1ReferenceFailureTargetReference = reference
        , grammarV1ReferenceFailureTargetArguments = arguments
        }
    _ -> failHelper "failure_target body is not a two-item sequence"

parseTermArguments
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandHelperError [GrammarV1ReferenceExpressionCore]
parseTermArguments tree = do
  fields <- namedSequence "term_arguments" tree
  case fields of
    [openParen, optionalValues, closeParen] -> do
      expectLiteral "(" openParen
      values <- parseOptionalExpressionList optionalValues
      expectLiteral ")" closeParen
      pure values
    _ -> failHelper "term_arguments body is not a three-item sequence"

parseOptionalExpressionList
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandHelperError [GrammarV1ReferenceExpressionCore]
parseOptionalExpressionList tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure []
  GrammarV1ReferenceOptionalSome payload -> do
    fields <- expectSequence "expression list" payload
    case fields of
      [firstTree, restTree] -> do
        first <- parseExpression firstTree
        rest <- expectRepetition "expression list suffixes" restTree
        suffixes <- traverse parseExpressionSuffix rest
        pure (first : suffixes)
      _ -> failHelper "expression list payload is not a two-item sequence"
  _ -> failHelper "expression list slot is not optional"

parseExpressionSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandHelperError GrammarV1ReferenceExpressionCore
parseExpressionSuffix tree = do
  fields <- expectSequence "expression list suffix" tree
  case fields of
    [commaTree, expressionTree] ->
      expectLiteral "," commaTree >> parseExpression expressionTree
    _ -> failHelper "expression list suffix is not a two-item sequence"

parseOptionalKeywordBase
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandHelperError
      (Maybe GrammarV1ReferenceExpressionCore)
parseOptionalKeywordBase keyword tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure Nothing
  GrammarV1ReferenceOptionalSome payload -> do
    fields <- expectSequence (keyword <> " optional payload") payload
    case fields of
      [keywordTree, baseTree] -> do
        expectLiteral keyword keywordTree
        Just <$> parseBase baseTree
      _ -> failHelper (keyword <> " optional payload is not a two-item sequence")
  _ -> failHelper (keyword <> " payload slot is not optional")

parseBase
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandHelperError GrammarV1ReferenceExpressionCore
parseBase baseTree =
  parseExpression
    (GrammarV1ReferenceNonterminal "expression"
      (GrammarV1ReferenceSequence
        [baseTree, GrammarV1ReferenceOptionalNone]))

parseExpression
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandHelperError GrammarV1ReferenceExpressionCore
parseExpression = mapExpressionError . grammarV1ReferenceExpressionCore

parseIdentifier
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandHelperError Text
parseIdentifier tree = do
  body <- expectNonterminal "identifier" tree
  case body of
    GrammarV1ReferenceLexical className value
      | className == "IDENTIFIER" -> pure value
      | otherwise -> failHelper
          ("identifier lexical class mismatch: " <> className)
    _ -> failHelper "identifier body is not an IDENTIFIER lexical leaf"

parseQualifiedName
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandHelperError [Text]
parseQualifiedName tree = do
  fields <- namedSequence "qualified_name" tree
  case fields of
    [firstTree, restTree] -> do
      first <- parseIdentifier firstTree
      rest <- expectRepetition "qualified_name suffixes" restTree
      suffixes <- traverse parseQualifiedNameSuffix rest
      pure (first : suffixes)
    _ -> failHelper "qualified_name body is not a two-item sequence"

parseQualifiedNameSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandHelperError Text
parseQualifiedNameSuffix tree = do
  fields <- expectSequence "qualified_name suffix" tree
  case fields of
    [dotTree, identifierTree] ->
      expectLiteral "." dotTree >> parseIdentifier identifierTree
    _ -> failHelper "qualified_name suffix is not a two-item sequence"

namedSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandHelperError [GrammarV1ReferenceParseTree]
namedSequence name tree = expectNonterminal name tree >>= expectSequence name

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandHelperError GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> pure body
    | otherwise -> failHelper
        ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failHelper ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandHelperError [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence values -> pure values
  _ -> failHelper (label <> " is not a sequence node")

expectRepetition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandHelperError [GrammarV1ReferenceParseTree]
expectRepetition label tree = case tree of
  GrammarV1ReferenceRepetition values -> pure values
  _ -> failHelper (label <> " is not a repetition node")

expectLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandHelperError ()
expectLiteral expected tree = case tree of
  GrammarV1ReferenceLiteral actual
    | actual == expected -> pure ()
    | otherwise -> failHelper
        ("expected literal " <> expected <> ", got " <> actual)
  _ -> failHelper ("expected literal " <> expected)

mapExpressionError
  :: Either GrammarV1ReferenceExpressionCoreError a
  -> Either GrammarV1ReferenceFixedCommandHelperError a
mapExpressionError = mapLeft
  (GrammarV1ReferenceFixedCommandHelperError . Text.pack . show)

mapStaticReferenceError
  :: Either GrammarV1ReferenceStaticReferenceError a
  -> Either GrammarV1ReferenceFixedCommandHelperError a
mapStaticReferenceError = mapLeft
  (GrammarV1ReferenceFixedCommandHelperError . Text.pack . show)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value

showText :: Show a => a -> Text
showText = Text.pack . show

failHelper
  :: Text
  -> Either GrammarV1ReferenceFixedCommandHelperError a
failHelper = Left . GrammarV1ReferenceFixedCommandHelperError
