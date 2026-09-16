{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstBlockStructure
  ( GrammarV1ReferenceBlockStructureError (..)
  , GrammarV1ReferencePatternCore (..)
  , GrammarV1ReferenceFieldPatternCore (..)
  , GrammarV1ReferenceStatementCore (..)
  , GrammarV1ReferenceBlockCore (..)
  , GrammarV1ReferenceCaseBindersCore (..)
  , GrammarV1ReferenceCasePatternCore (..)
  , GrammarV1ReferenceMatchArmBodyCore (..)
  , GrammarV1ReferenceMatchArmCore (..)
  , GrammarV1ReferenceStateSlotCore (..)
  , GrammarV1ReferenceJoinClauseCore (..)
  , GrammarV1ReferenceStateBindingCore (..)
  , grammarV1ProductionPatternCore
  , grammarV1ProductionStatementCore
  , grammarV1ProductionBlockCore
  , grammarV1ProductionMatchArmCore
  , grammarV1ProductionJoinClauseCore
  , grammarV1ProductionStateBindingCore
  , grammarV1ReferencePatternCore
  , grammarV1ReferenceStatementCore
  , grammarV1ReferenceBlockCore
  , grammarV1ReferenceMatchArmCore
  , grammarV1ReferenceJoinClauseCore
  , grammarV1ReferenceStateBindingCore
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..)
  , GrammarV1CaseBinders (..)
  , GrammarV1CasePattern (..)
  , GrammarV1FieldBinder (..)
  , GrammarV1FieldPattern (..)
  , GrammarV1JoinClause (..)
  , GrammarV1MatchArm (..)
  , GrammarV1MatchArmBody (..)
  , GrammarV1Pattern (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1StateBinding (..)
  , GrammarV1StateSlot (..)
  , GrammarV1Statement (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstExpressionCore
  ( GrammarV1ReferenceExpressionCore
  , GrammarV1ReferenceExpressionCoreError
  , grammarV1ProductionExpressionCore
  , grammarV1ReferenceExpressionCore
  )
import Phil.Surface.GrammarV1.ReferenceAstProposition
  ( GrammarV1ReferencePropositionCore
  , GrammarV1ReferencePropositionError
  , grammarV1ProductionPropositionCore
  , grammarV1ReferencePropositionCore
  )
import Phil.Surface.GrammarV1.ReferenceAstTypePayload
  ( GrammarV1ReferenceTypePayload
  , GrammarV1ReferenceTypePayloadError
  , grammarV1ProductionTypePayload
  , grammarV1ReferenceTypePayload
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( GrammarV1ReferenceParseTree (..)
  )
import Phil.Surface.Syntax (Located (..))

newtype GrammarV1ReferenceBlockStructureError =
  GrammarV1ReferenceBlockStructureError Text
  deriving (Eq, Show)

data GrammarV1ReferencePatternCore
  = GrammarV1ReferenceIdentifierPattern Text
  | GrammarV1ReferenceTuplePattern [GrammarV1ReferencePatternCore]
  | GrammarV1ReferenceRecordPattern
      [Text]
      [GrammarV1ReferenceFieldPatternCore]
  deriving (Eq, Show)

data GrammarV1ReferenceFieldPatternCore = GrammarV1ReferenceFieldPatternCore
  { grammarV1ReferenceFieldPatternName :: Text
  , grammarV1ReferenceFieldPatternValue :: Maybe GrammarV1ReferencePatternCore
  }
  deriving (Eq, Show)

data GrammarV1ReferenceStatementCore
  = GrammarV1ReferenceLetStatement
      GrammarV1ReferencePatternCore
      GrammarV1ReferenceExpressionCore
  | GrammarV1ReferenceReturnStatement GrammarV1ReferenceExpressionCore
  | GrammarV1ReferenceExpressionStatement GrammarV1ReferenceExpressionCore
  deriving (Eq, Show)

newtype GrammarV1ReferenceBlockCore = GrammarV1ReferenceBlockCore
  { grammarV1ReferenceBlockStatements :: [GrammarV1ReferenceStatementCore]
  }
  deriving (Eq, Show)

data GrammarV1ReferenceCaseBindersCore
  = GrammarV1ReferenceTupleCaseBinders [Text]
  | GrammarV1ReferenceRecordCaseBinders [(Text, Maybe Text)]
  deriving (Eq, Show)

data GrammarV1ReferenceCasePatternCore = GrammarV1ReferenceCasePatternCore
  { grammarV1ReferenceCasePatternName :: [Text]
  , grammarV1ReferenceCasePatternBinders :: Maybe GrammarV1ReferenceCaseBindersCore
  }
  deriving (Eq, Show)

data GrammarV1ReferenceMatchArmBodyCore
  = GrammarV1ReferenceMatchArmBlock GrammarV1ReferenceBlockCore
  | GrammarV1ReferenceMatchArmStatement GrammarV1ReferenceStatementCore
  deriving (Eq, Show)

data GrammarV1ReferenceMatchArmCore = GrammarV1ReferenceMatchArmCore
  { grammarV1ReferenceMatchArmPattern :: GrammarV1ReferenceCasePatternCore
  , grammarV1ReferenceMatchArmBody :: GrammarV1ReferenceMatchArmBodyCore
  }
  deriving (Eq, Show)

data GrammarV1ReferenceStateSlotCore = GrammarV1ReferenceStateSlotCore
  { grammarV1ReferenceStateSlotName :: Text
  , grammarV1ReferenceStateSlotType :: GrammarV1ReferenceTypePayload
  }
  deriving (Eq, Show)

data GrammarV1ReferenceJoinClauseCore = GrammarV1ReferenceJoinClauseCore
  { grammarV1ReferenceJoinState :: [GrammarV1ReferenceStateSlotCore]
  , grammarV1ReferenceJoinInvariant :: Maybe GrammarV1ReferencePropositionCore
  }
  deriving (Eq, Show)

data GrammarV1ReferenceStateBindingCore = GrammarV1ReferenceStateBindingCore
  { grammarV1ReferenceStateBindingName :: Text
  , grammarV1ReferenceStateBindingType :: Maybe GrammarV1ReferenceTypePayload
  , grammarV1ReferenceStateBindingInitializer :: GrammarV1ReferenceExpressionCore
  }
  deriving (Eq, Show)

grammarV1ProductionPatternCore :: GrammarV1Pattern -> GrammarV1ReferencePatternCore
grammarV1ProductionPatternCore patternValue = case patternValue of
  GrammarV1IdentifierPattern name ->
    GrammarV1ReferenceIdentifierPattern (locatedValue name)
  GrammarV1TuplePattern values ->
    GrammarV1ReferenceTuplePattern
      (map (grammarV1ProductionPatternCore . locatedValue) values)
  GrammarV1RecordPattern name fields ->
    GrammarV1ReferenceRecordPattern
      (grammarV1QualifiedNameParts (locatedValue name))
      (map (productionFieldPattern . locatedValue) fields)

productionFieldPattern :: GrammarV1FieldPattern -> GrammarV1ReferenceFieldPatternCore
productionFieldPattern field = GrammarV1ReferenceFieldPatternCore
  { grammarV1ReferenceFieldPatternName = locatedValue (grammarV1FieldPatternName field)
  , grammarV1ReferenceFieldPatternValue =
      fmap (grammarV1ProductionPatternCore . locatedValue)
        (grammarV1FieldPatternValue field)
  }

grammarV1ProductionStatementCore
  :: GrammarV1Statement
  -> GrammarV1ReferenceStatementCore
grammarV1ProductionStatementCore statement = case statement of
  GrammarV1LetStatement patternValue expression ->
    GrammarV1ReferenceLetStatement
      (grammarV1ProductionPatternCore (locatedValue patternValue))
      (grammarV1ProductionExpressionCore (locatedValue expression))
  GrammarV1ReturnStatement expression ->
    GrammarV1ReferenceReturnStatement
      (grammarV1ProductionExpressionCore (locatedValue expression))
  GrammarV1ExpressionStatement expression ->
    GrammarV1ReferenceExpressionStatement
      (grammarV1ProductionExpressionCore (locatedValue expression))

grammarV1ProductionBlockCore :: GrammarV1Block -> GrammarV1ReferenceBlockCore
grammarV1ProductionBlockCore block = GrammarV1ReferenceBlockCore
  (map (grammarV1ProductionStatementCore . locatedValue)
    (grammarV1BlockStatements block))

grammarV1ProductionMatchArmCore :: GrammarV1MatchArm -> GrammarV1ReferenceMatchArmCore
grammarV1ProductionMatchArmCore arm = GrammarV1ReferenceMatchArmCore
  { grammarV1ReferenceMatchArmPattern =
      productionCasePattern (locatedValue (grammarV1MatchArmPattern arm))
  , grammarV1ReferenceMatchArmBody = case grammarV1MatchArmBody arm of
      GrammarV1MatchArmBlock block ->
        GrammarV1ReferenceMatchArmBlock
          (grammarV1ProductionBlockCore (locatedValue block))
      GrammarV1MatchArmStatement statement ->
        GrammarV1ReferenceMatchArmStatement
          (grammarV1ProductionStatementCore (locatedValue statement))
  }

productionCasePattern :: GrammarV1CasePattern -> GrammarV1ReferenceCasePatternCore
productionCasePattern patternValue = GrammarV1ReferenceCasePatternCore
  { grammarV1ReferenceCasePatternName =
      grammarV1QualifiedNameParts (locatedValue (grammarV1CasePatternName patternValue))
  , grammarV1ReferenceCasePatternBinders =
      fmap productionCaseBinders (grammarV1CasePatternBinders patternValue)
  }

productionCaseBinders :: GrammarV1CaseBinders -> GrammarV1ReferenceCaseBindersCore
productionCaseBinders binders = case binders of
  GrammarV1TupleCaseBinders names ->
    GrammarV1ReferenceTupleCaseBinders (map locatedValue names)
  GrammarV1RecordCaseBinders fields ->
    GrammarV1ReferenceRecordCaseBinders
      [ ( locatedValue (grammarV1FieldBinderField field)
        , fmap locatedValue (grammarV1FieldBinderAlias field)
        )
      | Located _ field <- fields
      ]

grammarV1ProductionJoinClauseCore
  :: GrammarV1JoinClause
  -> GrammarV1ReferenceJoinClauseCore
grammarV1ProductionJoinClauseCore clause = GrammarV1ReferenceJoinClauseCore
  { grammarV1ReferenceJoinState =
      map (productionStateSlot . locatedValue) (grammarV1JoinState clause)
  , grammarV1ReferenceJoinInvariant =
      fmap (grammarV1ProductionPropositionCore . locatedValue)
        (grammarV1JoinInvariant clause)
  }

productionStateSlot :: GrammarV1StateSlot -> GrammarV1ReferenceStateSlotCore
productionStateSlot slot = GrammarV1ReferenceStateSlotCore
  { grammarV1ReferenceStateSlotName = locatedValue (grammarV1StateSlotName slot)
  , grammarV1ReferenceStateSlotType =
      grammarV1ProductionTypePayload (locatedValue (grammarV1StateSlotType slot))
  }

grammarV1ProductionStateBindingCore
  :: GrammarV1StateBinding
  -> GrammarV1ReferenceStateBindingCore
grammarV1ProductionStateBindingCore binding = GrammarV1ReferenceStateBindingCore
  { grammarV1ReferenceStateBindingName = locatedValue (grammarV1StateBindingName binding)
  , grammarV1ReferenceStateBindingType =
      fmap (grammarV1ProductionTypePayload . locatedValue)
        (grammarV1StateBindingType binding)
  , grammarV1ReferenceStateBindingInitializer =
      grammarV1ProductionExpressionCore
        (locatedValue (grammarV1StateBindingInitializer binding))
  }

grammarV1ReferencePatternCore
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError GrammarV1ReferencePatternCore
grammarV1ReferencePatternCore tree = do
  body <- expectNonterminal "pattern" tree
  case body of
    GrammarV1ReferenceAlternative 0 selected ->
      GrammarV1ReferenceIdentifierPattern <$> parseIdentifier selected
    GrammarV1ReferenceAlternative 1 selected -> parseTuplePattern selected
    GrammarV1ReferenceAlternative 2 selected -> parseRecordPattern selected
    GrammarV1ReferenceAlternative index _ ->
      failBlock ("pattern alternative out of range: " <> showText index)
    _ -> failBlock "pattern body is not an alternative node"

parseTuplePattern
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError GrammarV1ReferencePatternCore
parseTuplePattern tree = do
  fields <- namedSequence "tuple_pattern" tree
  case fields of
    [openParen, firstTree, comma, secondTree, restTree, closeParen] -> do
      expectLiteral "(" openParen
      first <- grammarV1ReferencePatternCore firstTree
      expectLiteral "," comma
      second <- grammarV1ReferencePatternCore secondTree
      rest <- expectRepetition "tuple_pattern suffix" restTree >>= traverse parsePatternSuffix
      expectLiteral ")" closeParen
      pure (GrammarV1ReferenceTuplePattern (first : second : rest))
    _ -> failBlock "tuple_pattern body is not a six-item sequence"

parsePatternSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError GrammarV1ReferencePatternCore
parsePatternSuffix tree = do
  fields <- expectSequence "tuple_pattern suffix item" tree
  case fields of
    [comma, patternTree] -> expectLiteral "," comma >> grammarV1ReferencePatternCore patternTree
    _ -> failBlock "tuple_pattern suffix item is not a two-item sequence"

parseRecordPattern
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError GrammarV1ReferencePatternCore
parseRecordPattern tree = do
  fields <- namedSequence "record_pattern" tree
  case fields of
    [nameTree, openBrace, firstTree, restTree, trailingTree, closeBrace] -> do
      name <- parseQualifiedName nameTree
      expectLiteral "{" openBrace
      first <- parseFieldPattern firstTree
      rest <- expectRepetition "record_pattern suffix" restTree >>= traverse parseFieldPatternSuffix
      parseOptionalLiteral "," trailingTree
      expectLiteral "}" closeBrace
      pure (GrammarV1ReferenceRecordPattern name (first : rest))
    _ -> failBlock "record_pattern body is not a six-item sequence"

parseFieldPatternSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError GrammarV1ReferenceFieldPatternCore
parseFieldPatternSuffix tree = do
  fields <- expectSequence "field_pattern suffix" tree
  case fields of
    [comma, fieldTree] -> expectLiteral "," comma >> parseFieldPattern fieldTree
    _ -> failBlock "field_pattern suffix is not a two-item sequence"

parseFieldPattern
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError GrammarV1ReferenceFieldPatternCore
parseFieldPattern tree = do
  fields <- namedSequence "field_pattern" tree
  case fields of
    [nameTree, valueTree] -> do
      name <- parseIdentifier nameTree
      value <- case valueTree of
        GrammarV1ReferenceOptionalNone -> pure Nothing
        GrammarV1ReferenceOptionalSome payload -> do
          payloadFields <- expectSequence "field_pattern value" payload
          case payloadFields of
            [equals, patternTree] -> do
              expectLiteral "=" equals
              Just <$> grammarV1ReferencePatternCore patternTree
            _ -> failBlock "field_pattern value is not a two-item sequence"
        _ -> failBlock "field_pattern value slot is not optional"
      pure GrammarV1ReferenceFieldPatternCore
        { grammarV1ReferenceFieldPatternName = name
        , grammarV1ReferenceFieldPatternValue = value
        }
    _ -> failBlock "field_pattern body is not a two-item sequence"

grammarV1ReferenceStatementCore
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError GrammarV1ReferenceStatementCore
grammarV1ReferenceStatementCore tree = do
  body <- expectNonterminal "statement" tree
  case body of
    GrammarV1ReferenceAlternative 0 selected -> do
      fields <- expectSequence "let statement" selected
      case fields of
        [keyword, patternTree, equals, expressionTree, semicolon] -> do
          expectLiteral "let" keyword
          patternValue <- grammarV1ReferencePatternCore patternTree
          expectLiteral "=" equals
          expression <- mapExpressionError (grammarV1ReferenceExpressionCore expressionTree)
          expectLiteral ";" semicolon
          pure (GrammarV1ReferenceLetStatement patternValue expression)
        _ -> failBlock "let statement is not a five-item sequence"
    GrammarV1ReferenceAlternative 1 selected -> do
      fields <- expectSequence "return statement" selected
      case fields of
        [keyword, expressionTree, semicolon] -> do
          expectLiteral "return" keyword
          expression <- mapExpressionError (grammarV1ReferenceExpressionCore expressionTree)
          expectLiteral ";" semicolon
          pure (GrammarV1ReferenceReturnStatement expression)
        _ -> failBlock "return statement is not a three-item sequence"
    GrammarV1ReferenceAlternative 2 selected -> do
      fields <- expectSequence "expression statement" selected
      case fields of
        [expressionTree, semicolon] -> do
          expression <- mapExpressionError (grammarV1ReferenceExpressionCore expressionTree)
          expectLiteral ";" semicolon
          pure (GrammarV1ReferenceExpressionStatement expression)
        _ -> failBlock "expression statement is not a two-item sequence"
    GrammarV1ReferenceAlternative index _ ->
      failBlock ("statement alternative out of range: " <> showText index)
    _ -> failBlock "statement body is not an alternative node"

grammarV1ReferenceBlockCore
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError GrammarV1ReferenceBlockCore
grammarV1ReferenceBlockCore tree = do
  fields <- namedSequence "block" tree
  case fields of
    [openBrace, statementsTree, closeBrace] -> do
      expectLiteral "{" openBrace
      statements <- expectRepetition "block statements" statementsTree
        >>= traverse grammarV1ReferenceStatementCore
      expectLiteral "}" closeBrace
      pure (GrammarV1ReferenceBlockCore statements)
    _ -> failBlock "block body is not a three-item sequence"

grammarV1ReferenceMatchArmCore
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError GrammarV1ReferenceMatchArmCore
grammarV1ReferenceMatchArmCore tree = do
  fields <- namedSequence "match_arm" tree
  case fields of
    [patternTree, arrow, bodyTree] -> do
      patternValue <- parseCasePattern patternTree
      expectLiteral "=>" arrow
      body <- case bodyTree of
        GrammarV1ReferenceAlternative 0 selected ->
          GrammarV1ReferenceMatchArmBlock <$> grammarV1ReferenceBlockCore selected
        GrammarV1ReferenceAlternative 1 selected ->
          GrammarV1ReferenceMatchArmStatement <$> grammarV1ReferenceStatementCore selected
        GrammarV1ReferenceAlternative index _ ->
          failBlock ("match_arm body alternative out of range: " <> showText index)
        _ -> failBlock "match_arm body is not an alternative node"
      pure GrammarV1ReferenceMatchArmCore
        { grammarV1ReferenceMatchArmPattern = patternValue
        , grammarV1ReferenceMatchArmBody = body
        }
    _ -> failBlock "match_arm body is not a three-item sequence"

parseCasePattern
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError GrammarV1ReferenceCasePatternCore
parseCasePattern tree = do
  fields <- namedSequence "case_pattern" tree
  case fields of
    [nameTree, bindersTree] -> do
      name <- parseQualifiedName nameTree
      binders <- case bindersTree of
        GrammarV1ReferenceOptionalNone -> pure Nothing
        GrammarV1ReferenceOptionalSome alternative -> case alternative of
          GrammarV1ReferenceAlternative 0 selected ->
            Just <$> parseTupleCaseBinders selected
          GrammarV1ReferenceAlternative 1 selected ->
            Just <$> parseRecordCaseBinders selected
          GrammarV1ReferenceAlternative index _ ->
            failBlock ("case_pattern binder alternative out of range: " <> showText index)
          _ -> failBlock "case_pattern binder payload is not an alternative node"
        _ -> failBlock "case_pattern binder slot is not optional"
      pure GrammarV1ReferenceCasePatternCore
        { grammarV1ReferenceCasePatternName = name
        , grammarV1ReferenceCasePatternBinders = binders
        }
    _ -> failBlock "case_pattern body is not a two-item sequence"

parseTupleCaseBinders
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError GrammarV1ReferenceCaseBindersCore
parseTupleCaseBinders tree = do
  fields <- expectSequence "case_pattern tuple binders" tree
  case fields of
    [openParen, contentsTree, closeParen] -> do
      expectLiteral "(" openParen
      names <- parseOptionalIdentifierList contentsTree
      expectLiteral ")" closeParen
      pure (GrammarV1ReferenceTupleCaseBinders names)
    _ -> failBlock "case_pattern tuple binders are not a three-item sequence"

parseRecordCaseBinders
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError GrammarV1ReferenceCaseBindersCore
parseRecordCaseBinders tree = do
  fields <- expectSequence "case_pattern record binders" tree
  case fields of
    [openBrace, contentsTree, closeBrace] -> do
      expectLiteral "{" openBrace
      values <- case contentsTree of
        GrammarV1ReferenceOptionalNone -> pure []
        GrammarV1ReferenceOptionalSome contents -> do
          contentFields <- expectSequence "case_pattern record binder contents" contents
          case contentFields of
            [firstTree, restTree, trailingTree] -> do
              first <- parseFieldBinder firstTree
              rest <- expectRepetition "case_pattern record binder suffix" restTree
                >>= traverse parseFieldBinderSuffix
              parseOptionalLiteral "," trailingTree
              pure (first : rest)
            _ -> failBlock "case_pattern record binder contents are not a three-item sequence"
        _ -> failBlock "case_pattern record binder contents are not optional"
      expectLiteral "}" closeBrace
      pure (GrammarV1ReferenceRecordCaseBinders values)
    _ -> failBlock "case_pattern record binders are not a three-item sequence"

parseFieldBinderSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError (Text, Maybe Text)
parseFieldBinderSuffix tree = do
  fields <- expectSequence "field_binder suffix" tree
  case fields of
    [comma, binderTree] -> expectLiteral "," comma >> parseFieldBinder binderTree
    _ -> failBlock "field_binder suffix is not a two-item sequence"

parseFieldBinder
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError (Text, Maybe Text)
parseFieldBinder tree = do
  fields <- namedSequence "field_binder" tree
  case fields of
    [fieldTree, aliasTree] -> do
      field <- parseIdentifier fieldTree
      alias <- case aliasTree of
        GrammarV1ReferenceOptionalNone -> pure Nothing
        GrammarV1ReferenceOptionalSome payload -> do
          payloadFields <- expectSequence "field_binder alias" payload
          case payloadFields of
            [asKeyword, identifierTree] -> do
              expectLiteral "as" asKeyword
              Just <$> parseIdentifier identifierTree
            _ -> failBlock "field_binder alias is not a two-item sequence"
        _ -> failBlock "field_binder alias slot is not optional"
      pure (field, alias)
    _ -> failBlock "field_binder body is not a two-item sequence"

grammarV1ReferenceJoinClauseCore
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError GrammarV1ReferenceJoinClauseCore
grammarV1ReferenceJoinClauseCore tree = do
  fields <- namedSequence "join_clause" tree
  case fields of
    [joinKeyword, stateKeyword, openParen, stateTree, closeParen, invariantTree] -> do
      expectLiteral "join" joinKeyword
      expectLiteral "state" stateKeyword
      expectLiteral "(" openParen
      state <- parseOptionalStateSlots stateTree
      expectLiteral ")" closeParen
      invariant <- case invariantTree of
        GrammarV1ReferenceOptionalNone -> pure Nothing
        GrammarV1ReferenceOptionalSome payload -> do
          payloadFields <- expectSequence "join invariant" payload
          case payloadFields of
            [keyword, propositionTree] -> do
              expectLiteral "invariant" keyword
              Just <$> mapPropositionError
                (grammarV1ReferencePropositionCore propositionTree)
            _ -> failBlock "join invariant is not a two-item sequence"
        _ -> failBlock "join invariant slot is not optional"
      pure GrammarV1ReferenceJoinClauseCore
        { grammarV1ReferenceJoinState = state
        , grammarV1ReferenceJoinInvariant = invariant
        }
    _ -> failBlock "join_clause body is not a six-item sequence"

parseOptionalStateSlots
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError [GrammarV1ReferenceStateSlotCore]
parseOptionalStateSlots tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure []
  GrammarV1ReferenceOptionalSome payload -> do
    fields <- expectSequence "join state slots" payload
    case fields of
      [firstTree, restTree] -> do
        first <- parseStateSlot firstTree
        rest <- expectRepetition "join state slot suffix" restTree
          >>= traverse parseStateSlotSuffix
        pure (first : rest)
      _ -> failBlock "join state slots are not a two-item sequence"
  _ -> failBlock "join state slot list is not optional"

parseStateSlotSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError GrammarV1ReferenceStateSlotCore
parseStateSlotSuffix tree = do
  fields <- expectSequence "state_slot suffix" tree
  case fields of
    [comma, slotTree] -> expectLiteral "," comma >> parseStateSlot slotTree
    _ -> failBlock "state_slot suffix is not a two-item sequence"

parseStateSlot
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError GrammarV1ReferenceStateSlotCore
parseStateSlot tree = do
  fields <- namedSequence "state_slot" tree
  case fields of
    [nameTree, colon, typeTree] -> do
      name <- parseIdentifier nameTree
      expectLiteral ":" colon
      sourceType <- mapTypeError (grammarV1ReferenceTypePayload typeTree)
      pure GrammarV1ReferenceStateSlotCore
        { grammarV1ReferenceStateSlotName = name
        , grammarV1ReferenceStateSlotType = sourceType
        }
    _ -> failBlock "state_slot body is not a three-item sequence"

grammarV1ReferenceStateBindingCore
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError GrammarV1ReferenceStateBindingCore
grammarV1ReferenceStateBindingCore tree = do
  fields <- namedSequence "state_binding" tree
  case fields of
    [nameTree, typeTree, equals, expressionTree] -> do
      name <- parseIdentifier nameTree
      sourceType <- case typeTree of
        GrammarV1ReferenceOptionalNone -> pure Nothing
        GrammarV1ReferenceOptionalSome payload -> do
          payloadFields <- expectSequence "state_binding type" payload
          case payloadFields of
            [colon, valueTree] -> do
              expectLiteral ":" colon
              Just <$> mapTypeError (grammarV1ReferenceTypePayload valueTree)
            _ -> failBlock "state_binding type is not a two-item sequence"
        _ -> failBlock "state_binding type slot is not optional"
      expectLiteral "=" equals
      initializer <- mapExpressionError (grammarV1ReferenceExpressionCore expressionTree)
      pure GrammarV1ReferenceStateBindingCore
        { grammarV1ReferenceStateBindingName = name
        , grammarV1ReferenceStateBindingType = sourceType
        , grammarV1ReferenceStateBindingInitializer = initializer
        }
    _ -> failBlock "state_binding body is not a four-item sequence"

parseOptionalIdentifierList
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError [Text]
parseOptionalIdentifierList tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure []
  GrammarV1ReferenceOptionalSome payload -> do
    fields <- expectSequence "identifier list" payload
    case fields of
      [firstTree, restTree] -> do
        first <- parseIdentifier firstTree
        rest <- expectRepetition "identifier list suffix" restTree
          >>= traverse parseIdentifierSuffix
        pure (first : rest)
      _ -> failBlock "identifier list is not a two-item sequence"
  _ -> failBlock "identifier list slot is not optional"

parseIdentifierSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError Text
parseIdentifierSuffix tree = do
  fields <- expectSequence "identifier suffix" tree
  case fields of
    [comma, identifierTree] -> expectLiteral "," comma >> parseIdentifier identifierTree
    _ -> failBlock "identifier suffix is not a two-item sequence"

parseQualifiedName
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError [Text]
parseQualifiedName tree = do
  fields <- namedSequence "qualified_name" tree
  case fields of
    [firstTree, restTree] -> do
      first <- parseIdentifier firstTree
      rest <- expectRepetition "qualified_name suffix" restTree
        >>= traverse parseQualifiedNameSuffix
      pure (first : rest)
    _ -> failBlock "qualified_name body is not a two-item sequence"

parseQualifiedNameSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError Text
parseQualifiedNameSuffix tree = do
  fields <- expectSequence "qualified_name suffix" tree
  case fields of
    [dot, identifierTree] -> expectLiteral "." dot >> parseIdentifier identifierTree
    _ -> failBlock "qualified_name suffix is not a two-item sequence"

parseIdentifier
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError Text
parseIdentifier tree = do
  body <- expectNonterminal "identifier" tree
  case body of
    GrammarV1ReferenceLexical "IDENTIFIER" value -> pure value
    GrammarV1ReferenceLexical className _ ->
      failBlock ("identifier has lexical class " <> className)
    _ -> failBlock "identifier body is not an IDENTIFIER lexical leaf"

parseOptionalLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError ()
parseOptionalLiteral expected tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure ()
  GrammarV1ReferenceOptionalSome value -> expectLiteral expected value
  _ -> failBlock ("optional literal " <> expected <> " is not optional")

namedSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError [GrammarV1ReferenceParseTree]
namedSequence name tree = expectNonterminal name tree >>= expectSequence name

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> pure body
    | otherwise -> failBlock
        ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failBlock ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence values -> pure values
  _ -> failBlock (label <> " is not a sequence node")

expectRepetition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError [GrammarV1ReferenceParseTree]
expectRepetition label tree = case tree of
  GrammarV1ReferenceRepetition values -> pure values
  _ -> failBlock (label <> " is not a repetition node")

expectLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockStructureError ()
expectLiteral expected tree = case tree of
  GrammarV1ReferenceLiteral actual
    | actual == expected -> pure ()
    | otherwise -> failBlock
        ("expected literal " <> expected <> ", got " <> actual)
  _ -> failBlock ("expected literal " <> expected)

mapExpressionError
  :: Either GrammarV1ReferenceExpressionCoreError a
  -> Either GrammarV1ReferenceBlockStructureError a
mapExpressionError = mapLeft
  (GrammarV1ReferenceBlockStructureError . Text.pack . show)

mapPropositionError
  :: Either GrammarV1ReferencePropositionError a
  -> Either GrammarV1ReferenceBlockStructureError a
mapPropositionError = mapLeft
  (GrammarV1ReferenceBlockStructureError . Text.pack . show)

mapTypeError
  :: Either GrammarV1ReferenceTypePayloadError a
  -> Either GrammarV1ReferenceBlockStructureError a
mapTypeError = mapLeft
  (GrammarV1ReferenceBlockStructureError . Text.pack . show)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform value = case value of
  Left errorValue -> Left (transform errorValue)
  Right result -> Right result

showText :: Show a => a -> Text
showText = Text.pack . show

failBlock
  :: Text
  -> Either GrammarV1ReferenceBlockStructureError a
failBlock = Left . GrammarV1ReferenceBlockStructureError
