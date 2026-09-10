{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstBlockCommands
  ( GrammarV1ReferenceBlockCommandError (..)
  , GrammarV1ReferenceStructuralMode (..)
  , GrammarV1ReferenceTermParamCore (..)
  , GrammarV1ReferenceBlockCommand (..)
  , grammarV1ProductionBlockCommand
  , grammarV1ReferenceBlockCommand
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Closure (..)
  , GrammarV1Expression (..)
  , GrammarV1StructuralMode (..)
  , GrammarV1TermParam (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstBlockStructure
  ( GrammarV1ReferenceBlockCore
  , GrammarV1ReferenceBlockStructureError
  , GrammarV1ReferenceJoinClauseCore
  , GrammarV1ReferenceMatchArmCore
  , GrammarV1ReferenceStateBindingCore
  , grammarV1ProductionBlockCore
  , grammarV1ProductionJoinClauseCore
  , grammarV1ProductionMatchArmCore
  , grammarV1ProductionStateBindingCore
  , grammarV1ReferenceBlockCore
  , grammarV1ReferenceJoinClauseCore
  , grammarV1ReferenceMatchArmCore
  , grammarV1ReferenceStateBindingCore
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

newtype GrammarV1ReferenceBlockCommandError =
  GrammarV1ReferenceBlockCommandError Text
  deriving (Eq, Show)

data GrammarV1ReferenceStructuralMode
  = GrammarV1ReferenceUnrestricted
  | GrammarV1ReferenceAffine
  | GrammarV1ReferenceLinear
  deriving (Eq, Ord, Show)

data GrammarV1ReferenceTermParamCore = GrammarV1ReferenceTermParamCore
  { grammarV1ReferenceTermParamName :: Text
  , grammarV1ReferenceTermParamType :: GrammarV1ReferenceTypePayload
  }
  deriving (Eq, Show)

data GrammarV1ReferenceBlockCommand
  = GrammarV1ReferenceBorrow
      GrammarV1ReferenceExpressionCore
      Text
      GrammarV1ReferenceBlockCore
  | GrammarV1ReferenceIf
      GrammarV1ReferenceExpressionCore
      (Maybe GrammarV1ReferenceJoinClauseCore)
      GrammarV1ReferenceBlockCore
      (Maybe GrammarV1ReferenceBlockCore)
  | GrammarV1ReferenceMatch
      GrammarV1ReferenceExpressionCore
      (Maybe GrammarV1ReferenceJoinClauseCore)
      [GrammarV1ReferenceMatchArmCore]
  | GrammarV1ReferenceDecide
      GrammarV1ReferenceExpressionCore
      [GrammarV1ReferenceMatchArmCore]
  | GrammarV1ReferenceClosure
      (Maybe GrammarV1ReferenceStructuralMode)
      [GrammarV1ReferenceTermParamCore]
      GrammarV1ReferenceTypePayload
      (Maybe [Text])
      GrammarV1ReferenceBlockCore
  | GrammarV1ReferenceLoop
      [GrammarV1ReferenceStateBindingCore]
      (Maybe GrammarV1ReferencePropositionCore)
      GrammarV1ReferenceBlockCore
  | GrammarV1ReferenceOffer
      GrammarV1ReferenceExpressionCore
      [GrammarV1ReferenceMatchArmCore]
  deriving (Eq, Show)

grammarV1ProductionBlockCommand
  :: GrammarV1Expression
  -> Maybe GrammarV1ReferenceBlockCommand
grammarV1ProductionBlockCommand expression = case expression of
  GrammarV1BorrowExpression value binder body ->
    Just (GrammarV1ReferenceBorrow
      (productionExpression value)
      (locatedValue binder)
      (grammarV1ProductionBlockCore (locatedValue body)))
  GrammarV1IfExpression condition joinClause thenBlock elseBlock ->
    Just (GrammarV1ReferenceIf
      (productionExpression condition)
      (fmap (grammarV1ProductionJoinClauseCore . locatedValue) joinClause)
      (grammarV1ProductionBlockCore (locatedValue thenBlock))
      (fmap (grammarV1ProductionBlockCore . locatedValue) elseBlock))
  GrammarV1MatchExpression scrutinee joinClause arms ->
    Just (GrammarV1ReferenceMatch
      (productionExpression scrutinee)
      (fmap (grammarV1ProductionJoinClauseCore . locatedValue) joinClause)
      (map (grammarV1ProductionMatchArmCore . locatedValue) arms))
  GrammarV1DecideExpression scrutinee arms ->
    Just (GrammarV1ReferenceDecide
      (productionExpression scrutinee)
      (map (grammarV1ProductionMatchArmCore . locatedValue) arms))
  GrammarV1ClosureExpression closure ->
    Just (productionClosure closure)
  GrammarV1LoopExpression bindings invariant body ->
    Just (GrammarV1ReferenceLoop
      (map (grammarV1ProductionStateBindingCore . locatedValue) bindings)
      (fmap (grammarV1ProductionPropositionCore . locatedValue) invariant)
      (grammarV1ProductionBlockCore (locatedValue body)))
  GrammarV1OfferExpression scrutinee arms ->
    Just (GrammarV1ReferenceOffer
      (productionExpression scrutinee)
      (map (grammarV1ProductionMatchArmCore . locatedValue) arms))
  _ -> Nothing
  where
    productionExpression = grammarV1ProductionExpressionCore . locatedValue

productionClosure :: GrammarV1Closure -> GrammarV1ReferenceBlockCommand
productionClosure closure = GrammarV1ReferenceClosure
  (fmap productionMode (grammarV1ClosureMode closure))
  (map (productionTermParam . locatedValue) (grammarV1ClosureTermParams closure))
  (grammarV1ProductionTypePayload (locatedValue (grammarV1ClosureSatisfies closure)))
  (fmap (map locatedValue) (grammarV1ClosureCaptures closure))
  (grammarV1ProductionBlockCore (locatedValue (grammarV1ClosureBody closure)))

productionMode :: GrammarV1StructuralMode -> GrammarV1ReferenceStructuralMode
productionMode mode = case mode of
  GrammarV1Unrestricted -> GrammarV1ReferenceUnrestricted
  GrammarV1Affine -> GrammarV1ReferenceAffine
  GrammarV1Linear -> GrammarV1ReferenceLinear

productionTermParam :: GrammarV1TermParam -> GrammarV1ReferenceTermParamCore
productionTermParam parameter = GrammarV1ReferenceTermParamCore
  { grammarV1ReferenceTermParamName = locatedValue (grammarV1TermParamName parameter)
  , grammarV1ReferenceTermParamType =
      grammarV1ProductionTypePayload (locatedValue (grammarV1TermParamType parameter))
  }

grammarV1ReferenceBlockCommand
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError (Maybe GrammarV1ReferenceBlockCommand)
grammarV1ReferenceBlockCommand tree = do
  body <- expectNonterminal "command_expression" tree
  case body of
    GrammarV1ReferenceAlternative index selected -> case index of
      1 -> Just <$> parseBorrow selected
      2 -> Just <$> parseIf selected
      3 -> Just <$> parseMatch selected
      4 -> Just <$> parseDecide selected
      5 -> Just <$> parseClosure selected
      6 -> Just <$> parseLoop selected
      17 -> Just <$> parseOffer selected
      _ | index >= 0 && index <= 26 -> pure Nothing
        | otherwise -> failBlockCommand
            ("command_expression alternative out of range: " <> showText index)
    _ -> failBlockCommand "command_expression body is not an alternative node"

parseBorrow
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError GrammarV1ReferenceBlockCommand
parseBorrow tree = do
  fields <- namedSequence "borrow_expression" tree
  case fields of
    [keyword, valueTree, asKeyword, binderTree, bodyTree] -> do
      expectLiteral "borrow" keyword
      value <- parseBase valueTree
      expectLiteral "as" asKeyword
      binder <- parseIdentifier binderTree
      body <- mapBlockError (grammarV1ReferenceBlockCore bodyTree)
      pure (GrammarV1ReferenceBorrow value binder body)
    _ -> failBlockCommand "borrow_expression body is not a five-item sequence"

parseIf
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError GrammarV1ReferenceBlockCommand
parseIf tree = do
  fields <- namedSequence "if_expression" tree
  case fields of
    [keyword, conditionTree, joinTree, thenTree, elseTree] -> do
      expectLiteral "if" keyword
      condition <- parseExpression conditionTree
      joinClause <- parseOptionalJoin joinTree
      thenBlock <- mapBlockError (grammarV1ReferenceBlockCore thenTree)
      elseBlock <- parseOptionalElse elseTree
      pure (GrammarV1ReferenceIf condition joinClause thenBlock elseBlock)
    _ -> failBlockCommand "if_expression body is not a five-item sequence"

parseMatch
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError GrammarV1ReferenceBlockCommand
parseMatch tree = do
  fields <- namedSequence "match_expression" tree
  case fields of
    [keyword, scrutineeTree, joinTree, openBrace, firstArmTree, restTree, closeBrace] -> do
      expectLiteral "match" keyword
      scrutinee <- parseExpression scrutineeTree
      joinClause <- parseOptionalJoin joinTree
      expectLiteral "{" openBrace
      first <- mapBlockError (grammarV1ReferenceMatchArmCore firstArmTree)
      rest <- expectRepetition "match arm suffixes" restTree
        >>= traverse (mapBlockError . grammarV1ReferenceMatchArmCore)
      expectLiteral "}" closeBrace
      pure (GrammarV1ReferenceMatch scrutinee joinClause (first : rest))
    _ -> failBlockCommand "match_expression body is not a seven-item sequence"

parseDecide
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError GrammarV1ReferenceBlockCommand
parseDecide tree = do
  fields <- namedSequence "decide_expression" tree
  case fields of
    [keyword, scrutineeTree, openBrace, firstArmTree, restTree, closeBrace] -> do
      expectLiteral "decide" keyword
      scrutinee <- parseBase scrutineeTree
      expectLiteral "{" openBrace
      first <- mapBlockError (grammarV1ReferenceMatchArmCore firstArmTree)
      rest <- expectRepetition "decide arm suffixes" restTree
        >>= traverse (mapBlockError . grammarV1ReferenceMatchArmCore)
      expectLiteral "}" closeBrace
      pure (GrammarV1ReferenceDecide scrutinee (first : rest))
    _ -> failBlockCommand "decide_expression body is not a six-item sequence"

parseClosure
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError GrammarV1ReferenceBlockCommand
parseClosure tree = do
  fields <- namedSequence "closure_expression" tree
  case fields of
    [keyword, modeTree, paramsTree, satisfiesKeyword, typeTree, capturesTree, bodyTree] -> do
      expectLiteral "closure" keyword
      mode <- parseOptionalMode modeTree
      params <- parseTermParams paramsTree
      expectLiteral "satisfies" satisfiesKeyword
      sourceType <- mapTypeError (grammarV1ReferenceTypePayload typeTree)
      captures <- parseOptionalCaptures capturesTree
      body <- mapBlockError (grammarV1ReferenceBlockCore bodyTree)
      pure (GrammarV1ReferenceClosure mode params sourceType captures body)
    _ -> failBlockCommand "closure_expression body is not a seven-item sequence"

parseLoop
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError GrammarV1ReferenceBlockCommand
parseLoop tree = do
  fields <- namedSequence "loop_expression" tree
  case fields of
    [keyword, stateTree, invariantTree, bodyTree] -> do
      expectLiteral "loop" keyword
      bindings <- parseOptionalLoopState stateTree
      invariant <- parseOptionalInvariant invariantTree
      body <- mapBlockError (grammarV1ReferenceBlockCore bodyTree)
      pure (GrammarV1ReferenceLoop bindings invariant body)
    _ -> failBlockCommand "loop_expression body is not a four-item sequence"

parseOffer
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError GrammarV1ReferenceBlockCommand
parseOffer tree = do
  fields <- namedSequence "offer_expression" tree
  case fields of
    [keyword, scrutineeTree, openBrace, firstArmTree, restTree, closeBrace] -> do
      expectLiteral "offer" keyword
      scrutinee <- parseBase scrutineeTree
      expectLiteral "{" openBrace
      first <- mapBlockError (grammarV1ReferenceMatchArmCore firstArmTree)
      rest <- expectRepetition "offer arm suffixes" restTree
        >>= traverse (mapBlockError . grammarV1ReferenceMatchArmCore)
      expectLiteral "}" closeBrace
      pure (GrammarV1ReferenceOffer scrutinee (first : rest))
    _ -> failBlockCommand "offer_expression body is not a six-item sequence"

parseOptionalJoin
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError (Maybe GrammarV1ReferenceJoinClauseCore)
parseOptionalJoin tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure Nothing
  GrammarV1ReferenceOptionalSome joinTree ->
    Just <$> mapBlockError (grammarV1ReferenceJoinClauseCore joinTree)
  _ -> failBlockCommand "join clause slot is not optional"

parseOptionalElse
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError (Maybe GrammarV1ReferenceBlockCore)
parseOptionalElse tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure Nothing
  GrammarV1ReferenceOptionalSome payload -> do
    fields <- expectSequence "else clause" payload
    case fields of
      [elseKeyword, blockTree] -> do
        expectLiteral "else" elseKeyword
        Just <$> mapBlockError (grammarV1ReferenceBlockCore blockTree)
      _ -> failBlockCommand "else clause is not a two-item sequence"
  _ -> failBlockCommand "else clause slot is not optional"

parseOptionalMode
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError (Maybe GrammarV1ReferenceStructuralMode)
parseOptionalMode tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure Nothing
  GrammarV1ReferenceOptionalSome payload -> do
    fields <- expectSequence "closure mode" payload
    case fields of
      [modeKeyword, modeTree] -> do
        expectLiteral "mode" modeKeyword
        Just <$> parseStructuralMode modeTree
      _ -> failBlockCommand "closure mode is not a two-item sequence"
  _ -> failBlockCommand "closure mode slot is not optional"

parseStructuralMode
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError GrammarV1ReferenceStructuralMode
parseStructuralMode tree = do
  body <- expectNonterminal "structural_mode" tree
  case body of
    GrammarV1ReferenceAlternative 0 selected ->
      expectLiteral "unrestricted" selected >> pure GrammarV1ReferenceUnrestricted
    GrammarV1ReferenceAlternative 1 selected ->
      expectLiteral "affine" selected >> pure GrammarV1ReferenceAffine
    GrammarV1ReferenceAlternative 2 selected ->
      expectLiteral "linear" selected >> pure GrammarV1ReferenceLinear
    GrammarV1ReferenceAlternative index _ ->
      failBlockCommand ("structural_mode alternative out of range: " <> showText index)
    _ -> failBlockCommand "structural_mode body is not an alternative node"

parseTermParams
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError [GrammarV1ReferenceTermParamCore]
parseTermParams tree = do
  fields <- namedSequence "term_params" tree
  case fields of
    [openParen, optionalParams, closeParen] -> do
      expectLiteral "(" openParen
      params <- parseOptionalTermParamList optionalParams
      expectLiteral ")" closeParen
      pure params
    _ -> failBlockCommand "term_params body is not a three-item sequence"

parseOptionalTermParamList
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError [GrammarV1ReferenceTermParamCore]
parseOptionalTermParamList tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure []
  GrammarV1ReferenceOptionalSome payload -> do
    fields <- expectSequence "term parameter list" payload
    case fields of
      [firstTree, restTree] -> do
        first <- parseTermParam firstTree
        suffixes <- expectRepetition "term parameter suffixes" restTree
        rest <- traverse parseTermParamSuffix suffixes
        pure (first : rest)
      _ -> failBlockCommand "term parameter list is not a two-item sequence"
  _ -> failBlockCommand "term parameter list slot is not optional"

parseTermParamSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError GrammarV1ReferenceTermParamCore
parseTermParamSuffix tree = do
  fields <- expectSequence "term parameter suffix" tree
  case fields of
    [comma, parameterTree] -> expectLiteral "," comma >> parseTermParam parameterTree
    _ -> failBlockCommand "term parameter suffix is not a two-item sequence"

parseTermParam
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError GrammarV1ReferenceTermParamCore
parseTermParam tree = do
  fields <- namedSequence "term_param" tree
  case fields of
    [nameTree, colon, typeTree] -> do
      name <- parseIdentifier nameTree
      expectLiteral ":" colon
      sourceType <- mapTypeError (grammarV1ReferenceTypePayload typeTree)
      pure GrammarV1ReferenceTermParamCore
        { grammarV1ReferenceTermParamName = name
        , grammarV1ReferenceTermParamType = sourceType
        }
    _ -> failBlockCommand "term_param body is not a three-item sequence"

parseOptionalCaptures
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError (Maybe [Text])
parseOptionalCaptures tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure Nothing
  GrammarV1ReferenceOptionalSome payload -> do
    fields <- expectSequence "closure captures" payload
    case fields of
      [capturesKeyword, openParen, namesTree, closeParen] -> do
        expectLiteral "captures" capturesKeyword
        expectLiteral "(" openParen
        names <- case namesTree of
          GrammarV1ReferenceOptionalNone -> pure []
          GrammarV1ReferenceOptionalSome listTree -> parseIdentifierList listTree
          _ -> failBlockCommand "closure captures identifier slot is not optional"
        expectLiteral ")" closeParen
        pure (Just names)
      _ -> failBlockCommand "closure captures is not a four-item sequence"
  _ -> failBlockCommand "closure captures slot is not optional"

parseIdentifierList
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError [Text]
parseIdentifierList tree = do
  fields <- namedSequence "identifier_list" tree
  case fields of
    [firstTree, restTree] -> do
      first <- parseIdentifier firstTree
      suffixes <- expectRepetition "identifier_list suffixes" restTree
      rest <- traverse parseIdentifierSuffix suffixes
      pure (first : rest)
    _ -> failBlockCommand "identifier_list body is not a two-item sequence"

parseIdentifierSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError Text
parseIdentifierSuffix tree = do
  fields <- expectSequence "identifier_list suffix" tree
  case fields of
    [comma, identifierTree] -> expectLiteral "," comma >> parseIdentifier identifierTree
    _ -> failBlockCommand "identifier_list suffix is not a two-item sequence"

parseOptionalLoopState
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError [GrammarV1ReferenceStateBindingCore]
parseOptionalLoopState tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure []
  GrammarV1ReferenceOptionalSome payload -> do
    fields <- expectSequence "loop state" payload
    case fields of
      [stateKeyword, openParen, bindingsTree, closeParen] -> do
        expectLiteral "state" stateKeyword
        expectLiteral "(" openParen
        bindings <- case bindingsTree of
          GrammarV1ReferenceOptionalNone -> pure []
          GrammarV1ReferenceOptionalSome listTree -> parseStateBindingList listTree
          _ -> failBlockCommand "loop state binding slot is not optional"
        expectLiteral ")" closeParen
        pure bindings
      _ -> failBlockCommand "loop state is not a four-item sequence"
  _ -> failBlockCommand "loop state slot is not optional"

parseStateBindingList
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError [GrammarV1ReferenceStateBindingCore]
parseStateBindingList tree = do
  fields <- expectSequence "loop state binding list" tree
  case fields of
    [firstTree, restTree] -> do
      first <- mapBlockError (grammarV1ReferenceStateBindingCore firstTree)
      suffixes <- expectRepetition "loop state binding suffixes" restTree
      rest <- traverse parseStateBindingSuffix suffixes
      pure (first : rest)
    _ -> failBlockCommand "loop state binding list is not a two-item sequence"

parseStateBindingSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError GrammarV1ReferenceStateBindingCore
parseStateBindingSuffix tree = do
  fields <- expectSequence "loop state binding suffix" tree
  case fields of
    [comma, bindingTree] -> do
      expectLiteral "," comma
      mapBlockError (grammarV1ReferenceStateBindingCore bindingTree)
    _ -> failBlockCommand "loop state binding suffix is not a two-item sequence"

parseOptionalInvariant
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError (Maybe GrammarV1ReferencePropositionCore)
parseOptionalInvariant tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure Nothing
  GrammarV1ReferenceOptionalSome payload -> do
    fields <- expectSequence "loop invariant" payload
    case fields of
      [invariantKeyword, propositionTree] -> do
        expectLiteral "invariant" invariantKeyword
        Just <$> mapPropositionError (grammarV1ReferencePropositionCore propositionTree)
      _ -> failBlockCommand "loop invariant is not a two-item sequence"
  _ -> failBlockCommand "loop invariant slot is not optional"

parseExpression
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError GrammarV1ReferenceExpressionCore
parseExpression = mapExpressionError . grammarV1ReferenceExpressionCore

parseBase
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError GrammarV1ReferenceExpressionCore
parseBase baseTree =
  parseExpression
    (GrammarV1ReferenceNonterminal "expression"
      (GrammarV1ReferenceSequence
        [baseTree, GrammarV1ReferenceOptionalNone]))

parseIdentifier
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError Text
parseIdentifier tree = do
  body <- expectNonterminal "identifier" tree
  case body of
    GrammarV1ReferenceLexical "IDENTIFIER" value -> pure value
    GrammarV1ReferenceLexical className _ ->
      failBlockCommand ("identifier has lexical class " <> className)
    _ -> failBlockCommand "identifier body is not an IDENTIFIER lexical leaf"

namedSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError [GrammarV1ReferenceParseTree]
namedSequence name tree = expectNonterminal name tree >>= expectSequence name

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> pure body
    | otherwise -> failBlockCommand
        ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failBlockCommand ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence values -> pure values
  _ -> failBlockCommand (label <> " is not a sequence node")

expectRepetition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError [GrammarV1ReferenceParseTree]
expectRepetition label tree = case tree of
  GrammarV1ReferenceRepetition values -> pure values
  _ -> failBlockCommand (label <> " is not a repetition node")

expectLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceBlockCommandError ()
expectLiteral expected tree = case tree of
  GrammarV1ReferenceLiteral actual
    | actual == expected -> pure ()
    | otherwise -> failBlockCommand
        ("expected literal " <> expected <> ", got " <> actual)
  _ -> failBlockCommand ("expected literal " <> expected)

mapExpressionError
  :: Either GrammarV1ReferenceExpressionCoreError a
  -> Either GrammarV1ReferenceBlockCommandError a
mapExpressionError = mapLeft
  (GrammarV1ReferenceBlockCommandError . Text.pack . show)

mapBlockError
  :: Either GrammarV1ReferenceBlockStructureError a
  -> Either GrammarV1ReferenceBlockCommandError a
mapBlockError = mapLeft
  (GrammarV1ReferenceBlockCommandError . Text.pack . show)

mapPropositionError
  :: Either GrammarV1ReferencePropositionError a
  -> Either GrammarV1ReferenceBlockCommandError a
mapPropositionError = mapLeft
  (GrammarV1ReferenceBlockCommandError . Text.pack . show)

mapTypeError
  :: Either GrammarV1ReferenceTypePayloadError a
  -> Either GrammarV1ReferenceBlockCommandError a
mapTypeError = mapLeft
  (GrammarV1ReferenceBlockCommandError . Text.pack . show)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value

showText :: Show a => a -> Text
showText = Text.pack . show

failBlockCommand :: Text -> Either GrammarV1ReferenceBlockCommandError a
failBlockCommand = Left . GrammarV1ReferenceBlockCommandError
