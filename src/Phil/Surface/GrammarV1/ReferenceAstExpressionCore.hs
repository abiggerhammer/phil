{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Phil.Surface.GrammarV1.ReferenceAstExpressionCore
  ( GrammarV1ReferenceExpressionCoreError (..)
  , GrammarV1ReferenceShiftOperator (..)
  , GrammarV1ReferenceBinaryOperator (..)
  , GrammarV1ReferenceFailureTarget (..)
  , GrammarV1ReferenceFallbackCore (..)
  , GrammarV1ReferenceExpressionCore (..)
  , grammarV1ProductionExpressionCore
  , grammarV1ReferenceExpressionCore
  , grammarV1ProductionTypeAliasExpressionCores
  , grammarV1ReferenceTypeAliasExpressionCores
  ) where

import Control.Monad (foldM)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Lexer (runtimeBytesLengthMarker)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1BinaryOperator (..)
  , GrammarV1Declaration (..)
  , GrammarV1Expression (..)
  , GrammarV1FailureTarget (..)
  , GrammarV1Fallback (..)
  , GrammarV1ShiftOperator (..)
  , GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..)
  , GrammarV1Type (..)
  , GrammarV1TypeAliasDecl (..)
  , pattern GrammarV1CharExpression
  , pattern GrammarV1StringExpression
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

newtype GrammarV1ReferenceExpressionCoreError =
  GrammarV1ReferenceExpressionCoreError Text
  deriving (Eq, Show)

data GrammarV1ReferenceShiftOperator
  = GrammarV1ReferenceShiftLeft
  | GrammarV1ReferenceShiftRight
  deriving (Eq, Ord, Show)

data GrammarV1ReferenceBinaryOperator
  = GrammarV1ReferenceAdd
  | GrammarV1ReferenceSubtract
  | GrammarV1ReferenceMultiply
  | GrammarV1ReferenceDivide
  | GrammarV1ReferenceRemainder
  deriving (Eq, Ord, Show)

data GrammarV1ReferenceFailureTarget = GrammarV1ReferenceFailureTarget
  { grammarV1ReferenceFailureTargetReference :: GrammarV1ReferenceStaticReferenceSpine
  , grammarV1ReferenceFailureTargetArguments :: [GrammarV1ReferenceExpressionCore]
  }
  deriving (Eq, Show)

data GrammarV1ReferenceFallbackCore
  = GrammarV1ReferenceFailFallback GrammarV1ReferenceFailureTarget
  | GrammarV1ReferenceRejectFallback GrammarV1ReferenceExpressionCore
  deriving (Eq, Show)

data GrammarV1ReferenceExpressionCore
  = GrammarV1ReferenceNameExpression
      GrammarV1ReferenceStaticReferenceSpine
      [GrammarV1ReferenceExpressionCore]
  | GrammarV1ReferenceBoolExpression Bool
  | GrammarV1ReferenceUnitExpression
  | GrammarV1ReferenceCharExpression Text
  | GrammarV1ReferenceStringExpression Text
  | GrammarV1ReferenceFloatExpression Text
  | GrammarV1ReferenceIntegerExpression Text
  | GrammarV1ReferenceNegateExpression GrammarV1ReferenceExpressionCore
  | GrammarV1ReferenceProjectionExpression GrammarV1ReferenceExpressionCore Text
  | GrammarV1ReferenceShiftExpression
      GrammarV1ReferenceExpressionCore
      GrammarV1ReferenceShiftOperator
      GrammarV1ReferenceExpressionCore
  | GrammarV1ReferenceBinaryExpression
      GrammarV1ReferenceExpressionCore
      GrammarV1ReferenceBinaryOperator
      GrammarV1ReferenceExpressionCore
  | GrammarV1ReferenceFallbackExpression
      GrammarV1ReferenceExpressionCore
      GrammarV1ReferenceFallbackCore
  | GrammarV1ReferenceTupleExpression [GrammarV1ReferenceExpressionCore]
  | GrammarV1ReferenceParenthesizedExpression GrammarV1ReferenceExpressionCore
  | GrammarV1ReferenceCommandExpression Text
  deriving (Eq, Show)

grammarV1ProductionExpressionCore
  :: GrammarV1Expression
  -> GrammarV1ReferenceExpressionCore
grammarV1ProductionExpressionCore expression = case expression of
  GrammarV1NameExpression reference arguments ->
    GrammarV1ReferenceNameExpression
      (grammarV1ProductionStaticReferenceSpine reference)
      (map (grammarV1ProductionExpressionCore . locatedValue) arguments)
  GrammarV1BoolExpression value -> GrammarV1ReferenceBoolExpression value
  GrammarV1UnitExpression -> GrammarV1ReferenceUnitExpression
  GrammarV1CharExpression value -> GrammarV1ReferenceCharExpression value
  GrammarV1StringExpression value -> GrammarV1ReferenceStringExpression value
  GrammarV1IntegerExpression value
    | isDecimalFloatSpelling value -> GrammarV1ReferenceFloatExpression value
    | otherwise -> GrammarV1ReferenceIntegerExpression value
  GrammarV1NegateExpression operand ->
    GrammarV1ReferenceNegateExpression
      (grammarV1ProductionExpressionCore (locatedValue operand))
  GrammarV1ProjectionExpression receiver field ->
    GrammarV1ReferenceProjectionExpression
      (grammarV1ProductionExpressionCore (locatedValue receiver))
      (locatedValue field)
  GrammarV1ShiftExpression left operator right ->
    GrammarV1ReferenceShiftExpression
      (grammarV1ProductionExpressionCore (locatedValue left))
      (productionShiftOperator (locatedValue operator))
      (grammarV1ProductionExpressionCore (locatedValue right))
  GrammarV1BinaryExpression left operator right ->
    GrammarV1ReferenceBinaryExpression
      (grammarV1ProductionExpressionCore (locatedValue left))
      (productionBinaryOperator (locatedValue operator))
      (grammarV1ProductionExpressionCore (locatedValue right))
  GrammarV1FallbackExpression base fallback ->
    GrammarV1ReferenceFallbackExpression
      (grammarV1ProductionExpressionCore (locatedValue base))
      (productionFallback (locatedValue fallback))
  GrammarV1TupleExpression values ->
    GrammarV1ReferenceTupleExpression
      (map (grammarV1ProductionExpressionCore . locatedValue) values)
  GrammarV1ParenthesizedExpression inner ->
    GrammarV1ReferenceParenthesizedExpression
      (grammarV1ProductionExpressionCore (locatedValue inner))
  GrammarV1ConstructExpression _ _ -> command "construct_expression"
  GrammarV1BorrowExpression _ _ _ -> command "borrow_expression"
  GrammarV1IfExpression _ _ _ _ -> command "if_expression"
  GrammarV1MatchExpression _ _ _ -> command "match_expression"
  GrammarV1DecideExpression _ _ -> command "decide_expression"
  GrammarV1ClosureExpression _ -> command "closure_expression"
  GrammarV1LoopExpression _ _ _ -> command "loop_expression"
  GrammarV1ContinueExpression _ -> command "continue_expression"
  GrammarV1BreakExpression _ -> command "break_expression"
  GrammarV1ReceiveFrameExpression _ -> command "receive_frame_expression"
  GrammarV1ReceiveExactExpression _ _ _ -> command "receive_exact_expression"
  GrammarV1ReceiveExpression _ _ -> command "receive_expression"
  GrammarV1RecognizeExpression _ _ -> command "recognize_expression"
  GrammarV1ValidateExpression _ _ _ -> command "validate_expression"
  GrammarV1SendExactExpression _ _ -> command "send_exact_expression"
  GrammarV1SendExpression _ _ -> command "send_expression"
  GrammarV1SelectExpression _ _ _ -> command "select_expression"
  GrammarV1OfferExpression _ _ -> command "offer_expression"
  GrammarV1CommitReceiveExpression _ _ -> command "commit_receive_expression"
  GrammarV1RejectExpression _ -> command "reject_expression"
  GrammarV1FailExpression _ _ -> command "fail_expression"
  GrammarV1CloseExpression _ -> command "close_expression"
  GrammarV1ReleaseExpression _ -> command "release_expression"
  GrammarV1ConvertExpression _ _ -> command "convert_expression"
  GrammarV1TransportExpression _ _ _ -> command "transport_expression"
  GrammarV1AcceptExpression _ _ -> command "accept_expression"
  GrammarV1ProveExpression _ -> command "prove_expression"
  where
    command = GrammarV1ReferenceCommandExpression

productionShiftOperator
  :: GrammarV1ShiftOperator
  -> GrammarV1ReferenceShiftOperator
productionShiftOperator operator = case operator of
  GrammarV1ShiftLeft -> GrammarV1ReferenceShiftLeft
  GrammarV1ShiftRight -> GrammarV1ReferenceShiftRight

productionBinaryOperator
  :: GrammarV1BinaryOperator
  -> GrammarV1ReferenceBinaryOperator
productionBinaryOperator operator = case operator of
  GrammarV1Add -> GrammarV1ReferenceAdd
  GrammarV1Subtract -> GrammarV1ReferenceSubtract
  GrammarV1Multiply -> GrammarV1ReferenceMultiply
  GrammarV1Divide -> GrammarV1ReferenceDivide
  GrammarV1Remainder -> GrammarV1ReferenceRemainder

productionFallback :: GrammarV1Fallback -> GrammarV1ReferenceFallbackCore
productionFallback fallback = case fallback of
  GrammarV1FailFallback target ->
    GrammarV1ReferenceFailFallback (productionFailureTarget (locatedValue target))
  GrammarV1RejectFallback value ->
    GrammarV1ReferenceRejectFallback
      (grammarV1ProductionExpressionCore (locatedValue value))

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

isDecimalFloatSpelling :: Text -> Bool
isDecimalFloatSpelling value = case Text.splitOn "." value of
  [whole, fractional] ->
    not (Text.null whole)
      && not (Text.null fractional)
      && Text.all asciiDigit whole
      && Text.all asciiDigit fractional
  _ -> False
  where
    asciiDigit character = character >= '0' && character <= '9'

grammarV1ReferenceExpressionCore
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError GrammarV1ReferenceExpressionCore
grammarV1ReferenceExpressionCore tree = do
  body <- expectNonterminal "expression" tree
  fields <- expectSequence "expression" body
  case fields of
    [baseTree, fallbackTree] -> do
      base <- parseBaseExpression baseTree
      case fallbackTree of
        GrammarV1ReferenceOptionalNone -> pure base
        GrammarV1ReferenceOptionalSome tailTree -> do
          tailFields <- expectSequence "expression fallback tail" tailTree
          case tailFields of
            [orKeyword, fallbackValue] -> do
              expectLiteral "or" orKeyword
              fallback <- parseFallback fallbackValue
              pure (GrammarV1ReferenceFallbackExpression base fallback)
            _ -> failExpression "expression fallback tail is not a two-item sequence"
        _ -> failExpression "expression fallback slot is not optional"
    _ -> failExpression "expression body is not a two-item sequence"

parseBaseExpression
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError GrammarV1ReferenceExpressionCore
parseBaseExpression tree = do
  body <- expectNonterminal "base_expression" tree
  case body of
    GrammarV1ReferenceAlternative 0 commandTree -> parseCommandExpression commandTree
    GrammarV1ReferenceAlternative 1 shiftTree -> parseShiftExpression shiftTree
    GrammarV1ReferenceAlternative index _ ->
      failExpression ("base_expression alternative out of range: " <> showText index)
    _ -> failExpression "base_expression body is not an alternative node"

parseCommandExpression
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError GrammarV1ReferenceExpressionCore
parseCommandExpression tree = do
  body <- expectNonterminal "command_expression" tree
  case body of
    GrammarV1ReferenceAlternative index selected -> do
      name <- commandAlternativeName index
      expectNamedNode name selected
      pure (GrammarV1ReferenceCommandExpression name)
    _ -> failExpression "command_expression body is not an alternative node"

commandAlternativeName
  :: Int
  -> Either GrammarV1ReferenceExpressionCoreError Text
commandAlternativeName index = case index of
  0 -> pure "construct_expression"
  1 -> pure "borrow_expression"
  2 -> pure "if_expression"
  3 -> pure "match_expression"
  4 -> pure "decide_expression"
  5 -> pure "closure_expression"
  6 -> pure "loop_expression"
  7 -> pure "continue_expression"
  8 -> pure "break_expression"
  9 -> pure "receive_frame_expression"
  10 -> pure "receive_exact_expression"
  11 -> pure "receive_expression"
  12 -> pure "recognize_expression"
  13 -> pure "validate_expression"
  14 -> pure "send_exact_expression"
  15 -> pure "send_expression"
  16 -> pure "select_expression"
  17 -> pure "offer_expression"
  18 -> pure "commit_receive_expression"
  19 -> pure "reject_expression"
  20 -> pure "fail_expression"
  21 -> pure "close_expression"
  22 -> pure "release_expression"
  23 -> pure "convert_expression"
  24 -> pure "transport_expression"
  25 -> pure "accept_expression"
  26 -> pure "prove_expression"
  _ -> failExpression ("command_expression alternative out of range: " <> showText index)

parseShiftExpression
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError GrammarV1ReferenceExpressionCore
parseShiftExpression tree = do
  body <- expectNonterminal "shift_expression" tree
  fields <- expectSequence "shift_expression" body
  case fields of
    [firstTree, restTree] -> do
      first <- parseAdditiveExpression firstTree
      rest <- expectRepetition "shift_expression suffix" restTree
      foldM applyShiftSuffix first rest
    _ -> failExpression "shift_expression body is not a two-item sequence"

applyShiftSuffix
  :: GrammarV1ReferenceExpressionCore
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError GrammarV1ReferenceExpressionCore
applyShiftSuffix left tree = do
  fields <- expectSequence "shift suffix" tree
  case fields of
    [operatorTree, rightTree] -> do
      operator <- parseShiftOperator operatorTree
      right <- parseAdditiveExpression rightTree
      pure (GrammarV1ReferenceShiftExpression left operator right)
    _ -> failExpression "shift suffix is not a two-item sequence"

parseShiftOperator
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError GrammarV1ReferenceShiftOperator
parseShiftOperator tree = case tree of
  GrammarV1ReferenceAlternative 0 selected ->
    expectLiteral "<<" selected >> pure GrammarV1ReferenceShiftLeft
  GrammarV1ReferenceAlternative 1 selected ->
    expectLiteral ">>" selected >> pure GrammarV1ReferenceShiftRight
  GrammarV1ReferenceAlternative index _ ->
    failExpression ("shift operator alternative out of range: " <> showText index)
  _ -> failExpression "shift operator is not an alternative node"

parseAdditiveExpression
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError GrammarV1ReferenceExpressionCore
parseAdditiveExpression tree = do
  body <- expectNonterminal "additive_expression" tree
  fields <- expectSequence "additive_expression" body
  case fields of
    [firstTree, restTree] -> do
      first <- parseMultiplicativeExpression firstTree
      rest <- expectRepetition "additive_expression suffix" restTree
      foldM applyAdditiveSuffix first rest
    _ -> failExpression "additive_expression body is not a two-item sequence"

applyAdditiveSuffix
  :: GrammarV1ReferenceExpressionCore
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError GrammarV1ReferenceExpressionCore
applyAdditiveSuffix left tree = do
  fields <- expectSequence "additive suffix" tree
  case fields of
    [operatorTree, rightTree] -> do
      operator <- parseAdditiveOperator operatorTree
      right <- parseMultiplicativeExpression rightTree
      pure (GrammarV1ReferenceBinaryExpression left operator right)
    _ -> failExpression "additive suffix is not a two-item sequence"

parseAdditiveOperator
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError GrammarV1ReferenceBinaryOperator
parseAdditiveOperator tree = case tree of
  GrammarV1ReferenceAlternative 0 selected ->
    expectLiteral "+" selected >> pure GrammarV1ReferenceAdd
  GrammarV1ReferenceAlternative 1 selected ->
    expectLiteral "-" selected >> pure GrammarV1ReferenceSubtract
  GrammarV1ReferenceAlternative index _ ->
    failExpression ("additive operator alternative out of range: " <> showText index)
  _ -> failExpression "additive operator is not an alternative node"

parseMultiplicativeExpression
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError GrammarV1ReferenceExpressionCore
parseMultiplicativeExpression tree = do
  body <- expectNonterminal "multiplicative_expression" tree
  fields <- expectSequence "multiplicative_expression" body
  case fields of
    [firstTree, restTree] -> do
      first <- parseUnaryExpression firstTree
      rest <- expectRepetition "multiplicative_expression suffix" restTree
      foldM applyMultiplicativeSuffix first rest
    _ -> failExpression "multiplicative_expression body is not a two-item sequence"

applyMultiplicativeSuffix
  :: GrammarV1ReferenceExpressionCore
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError GrammarV1ReferenceExpressionCore
applyMultiplicativeSuffix left tree = do
  fields <- expectSequence "multiplicative suffix" tree
  case fields of
    [operatorTree, rightTree] -> do
      operator <- parseMultiplicativeOperator operatorTree
      right <- parseUnaryExpression rightTree
      pure (GrammarV1ReferenceBinaryExpression left operator right)
    _ -> failExpression "multiplicative suffix is not a two-item sequence"

parseMultiplicativeOperator
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError GrammarV1ReferenceBinaryOperator
parseMultiplicativeOperator tree = case tree of
  GrammarV1ReferenceAlternative 0 selected ->
    expectLiteral "*" selected >> pure GrammarV1ReferenceMultiply
  GrammarV1ReferenceAlternative 1 selected ->
    expectLiteral "/" selected >> pure GrammarV1ReferenceDivide
  GrammarV1ReferenceAlternative 2 selected ->
    expectLiteral "%" selected >> pure GrammarV1ReferenceRemainder
  GrammarV1ReferenceAlternative index _ ->
    failExpression ("multiplicative operator alternative out of range: " <> showText index)
  _ -> failExpression "multiplicative operator is not an alternative node"

parseUnaryExpression
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError GrammarV1ReferenceExpressionCore
parseUnaryExpression tree = do
  body <- expectNonterminal "unary_expression" tree
  case body of
    GrammarV1ReferenceAlternative 0 selected -> do
      fields <- expectSequence "unary negation" selected
      case fields of
        [minus, operandTree] -> do
          expectLiteral "-" minus
          operand <- parseUnaryExpression operandTree
          pure (GrammarV1ReferenceNegateExpression operand)
        _ -> failExpression "unary negation is not a two-item sequence"
    GrammarV1ReferenceAlternative 1 postfixTree -> parsePostfixExpression postfixTree
    GrammarV1ReferenceAlternative index _ ->
      failExpression ("unary_expression alternative out of range: " <> showText index)
    _ -> failExpression "unary_expression body is not an alternative node"

parsePostfixExpression
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError GrammarV1ReferenceExpressionCore
parsePostfixExpression tree = do
  body <- expectNonterminal "postfix_expression" tree
  case body of
    GrammarV1ReferenceAlternative 0 namedTree -> parseNamedPostfixExpression namedTree
    GrammarV1ReferenceAlternative 1 selected -> do
      fields <- expectSequence "primary postfix expression" selected
      case fields of
        [primaryTree, projectionsTree] -> do
          primary <- parsePrimaryExpression primaryTree
          projections <- expectRepetition "primary postfix projections" projectionsTree
          foldM applyProjection primary projections
        _ -> failExpression "primary postfix expression is not a two-item sequence"
    GrammarV1ReferenceAlternative index _ ->
      failExpression ("postfix_expression alternative out of range: " <> showText index)
    _ -> failExpression "postfix_expression body is not an alternative node"

parseNamedPostfixExpression
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError GrammarV1ReferenceExpressionCore
parseNamedPostfixExpression tree = do
  body <- expectNonterminal "named_postfix_expression" tree
  fields <- expectSequence "named_postfix_expression" body
  case fields of
    [nameTree, optionalTail] -> case optionalTail of
      GrammarV1ReferenceOptionalNone -> do
        reference <- referenceFromName nameTree GrammarV1ReferenceOptionalNone
        pure (GrammarV1ReferenceNameExpression reference [])
      GrammarV1ReferenceOptionalSome choice -> case choice of
        GrammarV1ReferenceAlternative 0 selected -> do
          tailFields <- expectSequence "static named postfix tail" selected
          case tailFields of
            [staticArgumentsTree, optionalTerms, projectionsTree] -> do
              reference <- referenceFromName nameTree
                (GrammarV1ReferenceOptionalSome staticArgumentsTree)
              arguments <- parseOptionalTermArguments optionalTerms
              projections <- expectRepetition "named postfix projections" projectionsTree
              foldM applyProjection
                (GrammarV1ReferenceNameExpression reference arguments)
                projections
            _ -> failExpression "static named postfix tail is not a three-item sequence"
        GrammarV1ReferenceAlternative 1 selected -> do
          tailFields <- expectSequence "term named postfix tail" selected
          case tailFields of
            [termArgumentsTree, projectionsTree] -> do
              reference <- referenceFromName nameTree GrammarV1ReferenceOptionalNone
              arguments <- parseTermArguments termArgumentsTree
              projections <- expectRepetition "named postfix projections" projectionsTree
              foldM applyProjection
                (GrammarV1ReferenceNameExpression reference arguments)
                projections
            _ -> failExpression "term named postfix tail is not a two-item sequence"
        GrammarV1ReferenceAlternative index _ ->
          failExpression ("named postfix tail alternative out of range: " <> showText index)
        _ -> failExpression "named postfix tail is not an alternative node"
      _ -> failExpression "named_postfix_expression tail is not optional"
    _ -> failExpression "named_postfix_expression body is not a two-item sequence"

referenceFromName
  :: GrammarV1ReferenceParseTree
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError GrammarV1ReferenceStaticReferenceSpine
referenceFromName nameTree argumentsTree = mapStaticReferenceError
  (grammarV1ReferenceStaticReferenceSpine
    (GrammarV1ReferenceNonterminal
      "static_reference"
      (GrammarV1ReferenceSequence [nameTree, argumentsTree])))

parseOptionalTermArguments
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError [GrammarV1ReferenceExpressionCore]
parseOptionalTermArguments tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure []
  GrammarV1ReferenceOptionalSome termsTree -> parseTermArguments termsTree
  _ -> failExpression "term-argument slot is not optional"

parseTermArguments
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError [GrammarV1ReferenceExpressionCore]
parseTermArguments tree = do
  body <- expectNonterminal "term_arguments" tree
  fields <- expectSequence "term_arguments" body
  case fields of
    [openParen, optionalValues, closeParen] -> do
      expectLiteral "(" openParen
      values <- case optionalValues of
        GrammarV1ReferenceOptionalNone -> pure []
        GrammarV1ReferenceOptionalSome valueTree -> do
          valueFields <- expectSequence "term_arguments values" valueTree
          case valueFields of
            [firstTree, restTree] -> do
              first <- grammarV1ReferenceExpressionCore firstTree
              restItems <- expectRepetition "term_arguments suffix" restTree
              rest <- traverse parseTermArgumentSuffix restItems
              pure (first : rest)
            _ -> failExpression "term_arguments values are not a two-item sequence"
        _ -> failExpression "term_arguments values slot is not optional"
      expectLiteral ")" closeParen
      pure values
    _ -> failExpression "term_arguments body is not a three-item sequence"

parseTermArgumentSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError GrammarV1ReferenceExpressionCore
parseTermArgumentSuffix tree = do
  fields <- expectSequence "term argument suffix" tree
  case fields of
    [comma, expressionTree] -> do
      expectLiteral "," comma
      grammarV1ReferenceExpressionCore expressionTree
    _ -> failExpression "term argument suffix is not a two-item sequence"

applyProjection
  :: GrammarV1ReferenceExpressionCore
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError GrammarV1ReferenceExpressionCore
applyProjection receiver tree = do
  fields <- expectSequence "projection suffix" tree
  case fields of
    [dot, identifierTree] -> do
      expectLiteral "." dot
      field <- parseIdentifier identifierTree
      pure (GrammarV1ReferenceProjectionExpression receiver field)
    _ -> failExpression "projection suffix is not a two-item sequence"

parsePrimaryExpression
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError GrammarV1ReferenceExpressionCore
parsePrimaryExpression tree = do
  body <- expectNonterminal "primary_expression" tree
  case body of
    GrammarV1ReferenceAlternative index selected -> case index of
      0 -> parseTupleExpression selected
      1 -> parseParenthesizedExpression selected
      2 -> expectLiteral "true" selected >> pure (GrammarV1ReferenceBoolExpression True)
      3 -> expectLiteral "false" selected >> pure (GrammarV1ReferenceBoolExpression False)
      4 -> expectLiteral "unit" selected >> pure GrammarV1ReferenceUnitExpression
      5 -> GrammarV1ReferenceCharExpression <$> parseLexicalLiteral "char_literal" "CHAR_LITERAL" selected
      6 -> GrammarV1ReferenceStringExpression <$> parseLexicalLiteral "runtime_string_literal" "STRING_LITERAL" selected
      7 -> GrammarV1ReferenceFloatExpression <$> parseLexicalLiteral "float_literal" "DECIMAL_FLOAT" selected
      8 -> GrammarV1ReferenceIntegerExpression <$> parseLexicalLiteral "integer_literal" "DECIMAL_INTEGER" selected
      _ -> failExpression ("primary_expression alternative out of range: " <> showText index)
    _ -> failExpression "primary_expression body is not an alternative node"

parseTupleExpression
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError GrammarV1ReferenceExpressionCore
parseTupleExpression tree = do
  body <- expectNonterminal "tuple_expression" tree
  fields <- expectSequence "tuple_expression" body
  case fields of
    [openParen, firstTree, firstComma, secondTree, restTree, closeParen] -> do
      expectLiteral "(" openParen
      first <- grammarV1ReferenceExpressionCore firstTree
      expectLiteral "," firstComma
      second <- grammarV1ReferenceExpressionCore secondTree
      restItems <- expectRepetition "tuple_expression suffix" restTree
      rest <- traverse parseTupleSuffix restItems
      expectLiteral ")" closeParen
      pure (GrammarV1ReferenceTupleExpression (first : second : rest))
    _ -> failExpression "tuple_expression body is not a six-item sequence"

parseTupleSuffix
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError GrammarV1ReferenceExpressionCore
parseTupleSuffix tree = do
  fields <- expectSequence "tuple_expression suffix" tree
  case fields of
    [comma, expressionTree] -> do
      expectLiteral "," comma
      grammarV1ReferenceExpressionCore expressionTree
    _ -> failExpression "tuple_expression suffix is not a two-item sequence"

parseParenthesizedExpression
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError GrammarV1ReferenceExpressionCore
parseParenthesizedExpression tree = do
  body <- expectNonterminal "parenthesized_expression" tree
  fields <- expectSequence "parenthesized_expression" body
  case fields of
    [openParen, expressionTree, closeParen] -> do
      expectLiteral "(" openParen
      value <- grammarV1ReferenceExpressionCore expressionTree
      expectLiteral ")" closeParen
      pure (GrammarV1ReferenceParenthesizedExpression value)
    _ -> failExpression "parenthesized_expression body is not a three-item sequence"

parseFallback
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError GrammarV1ReferenceFallbackCore
parseFallback tree = do
  body <- expectNonterminal "fallback" tree
  case body of
    GrammarV1ReferenceAlternative 0 selected -> do
      fields <- expectSequence "fail fallback" selected
      case fields of
        [failKeyword, targetTree] -> do
          expectLiteral "fail" failKeyword
          target <- parseFailureTarget targetTree
          pure (GrammarV1ReferenceFailFallback target)
        _ -> failExpression "fail fallback is not a two-item sequence"
    GrammarV1ReferenceAlternative 1 selected -> do
      fields <- expectSequence "reject fallback" selected
      case fields of
        [rejectKeyword, valueTree] -> do
          expectLiteral "reject" rejectKeyword
          value <- parseBaseExpression valueTree
          pure (GrammarV1ReferenceRejectFallback value)
        _ -> failExpression "reject fallback is not a two-item sequence"
    GrammarV1ReferenceAlternative index _ ->
      failExpression ("fallback alternative out of range: " <> showText index)
    _ -> failExpression "fallback body is not an alternative node"

parseFailureTarget
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError GrammarV1ReferenceFailureTarget
parseFailureTarget tree = do
  body <- expectNonterminal "failure_target" tree
  fields <- expectSequence "failure_target" body
  case fields of
    [referenceTree, optionalArguments] -> do
      reference <- mapStaticReferenceError
        (grammarV1ReferenceStaticReferenceSpine referenceTree)
      arguments <- parseOptionalTermArguments optionalArguments
      pure GrammarV1ReferenceFailureTarget
        { grammarV1ReferenceFailureTargetReference = reference
        , grammarV1ReferenceFailureTargetArguments = arguments
        }
    _ -> failExpression "failure_target body is not a two-item sequence"

parseLexicalLiteral
  :: Text
  -> Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError Text
parseLexicalLiteral nonterminal className tree = do
  body <- expectNonterminal nonterminal tree
  case body of
    GrammarV1ReferenceLexical actualClass value
      | actualClass == className -> pure value
      | otherwise -> failExpression
          (nonterminal <> " uses lexical class " <> actualClass)
    _ -> failExpression (nonterminal <> " body is not a lexical leaf")

parseIdentifier
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError Text
parseIdentifier tree = parseLexicalLiteral "identifier" "IDENTIFIER" tree

grammarV1ProductionTypeAliasExpressionCores
  :: GrammarV1SourceFile
  -> [[GrammarV1ReferenceExpressionCore]]
grammarV1ProductionTypeAliasExpressionCores sourceFile =
  [ collectProductionTypeExpressions (locatedValue (grammarV1TypeAliasTarget alias))
  | locatedTopLevel <- grammarV1TopLevelDecls sourceFile
  , let topLevel = locatedValue locatedTopLevel
  , GrammarV1TypeAliasDeclaration alias <-
      [locatedValue (grammarV1Declaration topLevel)]
  ]

collectProductionTypeExpressions
  :: GrammarV1Type
  -> [GrammarV1ReferenceExpressionCore]
collectProductionTypeExpressions sourceType = case sourceType of
  GrammarV1BytesType expression ->
    case locatedValue expression of
      GrammarV1IntegerExpression marker
        | marker == runtimeBytesLengthMarker -> []
      value -> [grammarV1ProductionExpressionCore value]
  GrammarV1ValidatedType _ first second ->
    [ grammarV1ProductionExpressionCore (locatedValue first)
    , grammarV1ProductionExpressionCore (locatedValue second)
    ]
  GrammarV1RefinementType _ baseType _ ->
    collectProductionTypeExpressions (locatedValue baseType)
  GrammarV1TupleType elements ->
    concatMap (collectProductionTypeExpressions . locatedValue) elements
  _ -> []

grammarV1ReferenceTypeAliasExpressionCores
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError [[GrammarV1ReferenceExpressionCore]]
grammarV1ReferenceTypeAliasExpressionCores tree = do
  sourceBody <- expectNonterminal "source_file" tree
  sourceFields <- expectSequence "source_file" sourceBody
  case sourceFields of
    [_moduleTree, _importTree, topLevelTree] -> do
      topLevels <- expectRepetition "source_file top levels" topLevelTree
      values <- traverse parseTopLevelTypeAliasExpressions topLevels
      pure [value | Just value <- values]
    _ -> failExpression "source_file body is not a three-item sequence"

parseTopLevelTypeAliasExpressions
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError (Maybe [GrammarV1ReferenceExpressionCore])
parseTopLevelTypeAliasExpressions tree = do
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
              Just <$> parseTypeAliasTargetExpressions selected
            _ -> failExpression "type-alias declaration does not occupy alternative 2"
        _ -> pure Nothing
    _ -> failExpression "top_level_decl body is not a two-item sequence"

parseTypeAliasTargetExpressions
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError [GrammarV1ReferenceExpressionCore]
parseTypeAliasTargetExpressions tree = do
  body <- expectNonterminal "type_alias_decl" tree
  fields <- expectSequence "type_alias_decl" body
  case fields of
    [_keyword, _name, _generic, _requirements, _equals, targetTree, _terminator] ->
      collectReferenceTypeExpressions targetTree
    _ -> failExpression "type_alias_decl body is not a seven-item sequence"

collectReferenceTypeExpressions
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError [GrammarV1ReferenceExpressionCore]
collectReferenceTypeExpressions tree = do
  body <- expectNonterminal "type_expression" tree
  case body of
    GrammarV1ReferenceAlternative 0 nonreference -> do
      nonreferenceBody <- expectNonterminal "nonreference_type_expression" nonreference
      case nonreferenceBody of
        GrammarV1ReferenceAlternative 7 bytesTree -> collectBytesExpression bytesTree
        GrammarV1ReferenceAlternative 10 validatedTree -> collectValidatedExpressions validatedTree
        GrammarV1ReferenceAlternative 11 refinementTree -> collectRefinementBaseExpressions refinementTree
        GrammarV1ReferenceAlternative 12 tupleTree -> collectTupleTypeExpressions tupleTree
        GrammarV1ReferenceAlternative _ _ -> pure []
        _ -> failExpression "nonreference_type_expression body is not an alternative node"
    GrammarV1ReferenceAlternative 1 _named -> pure []
    GrammarV1ReferenceAlternative index _ ->
      failExpression ("type_expression alternative out of range: " <> showText index)
    _ -> failExpression "type_expression body is not an alternative node"

collectBytesExpression
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError [GrammarV1ReferenceExpressionCore]
collectBytesExpression tree = do
  fields <- expectSequence "Bytes type" tree
  case fields of
    [bytesKeyword, optionalIndex] -> do
      expectLiteral "Bytes" bytesKeyword
      case optionalIndex of
        GrammarV1ReferenceOptionalNone -> pure []
        GrammarV1ReferenceOptionalSome indexTree -> do
          indexFields <- expectSequence "Bytes index" indexTree
          case indexFields of
            [openBracket, expressionTree, closeBracket] -> do
              expectLiteral "[" openBracket
              value <- grammarV1ReferenceExpressionCore expressionTree
              expectLiteral "]" closeBracket
              pure [value]
            _ -> failExpression "Bytes index is not a three-item sequence"
        _ -> failExpression "Bytes index slot is not optional"
    _ -> failExpression "Bytes type body is not a two-item sequence"

collectValidatedExpressions
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError [GrammarV1ReferenceExpressionCore]
collectValidatedExpressions tree = do
  fields <- expectSequence "Validated type" tree
  case fields of
    [validatedKeyword, openBracket, _referenceTree, firstComma, firstTree, secondComma, secondTree, closeBracket] -> do
      expectLiteral "Validated" validatedKeyword
      expectLiteral "[" openBracket
      expectLiteral "," firstComma
      first <- grammarV1ReferenceExpressionCore firstTree
      expectLiteral "," secondComma
      second <- grammarV1ReferenceExpressionCore secondTree
      expectLiteral "]" closeBracket
      pure [first, second]
    _ -> failExpression "Validated type body is not an eight-item sequence"

collectRefinementBaseExpressions
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError [GrammarV1ReferenceExpressionCore]
collectRefinementBaseExpressions tree = do
  body <- expectNonterminal "refinement_type" tree
  fields <- expectSequence "refinement_type" body
  case fields of
    [_openBrace, _binder, _colon, baseTypeTree, _bar, _proposition, _closeBrace] ->
      collectReferenceTypeExpressions baseTypeTree
    _ -> failExpression "refinement_type body is not a seven-item sequence"

collectTupleTypeExpressions
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError [GrammarV1ReferenceExpressionCore]
collectTupleTypeExpressions tree = do
  body <- expectNonterminal "tuple_type" tree
  fields <- expectSequence "tuple_type" body
  case fields of
    [_openParen, firstTree, _firstComma, secondTree, restTree, _closeParen] -> do
      first <- collectReferenceTypeExpressions firstTree
      second <- collectReferenceTypeExpressions secondTree
      restItems <- expectRepetition "tuple_type suffix" restTree
      rest <- fmap concat (traverse collectTupleTypeSuffixExpressions restItems)
      pure (first <> second <> rest)
    _ -> failExpression "tuple_type body is not a six-item sequence"

collectTupleTypeSuffixExpressions
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError [GrammarV1ReferenceExpressionCore]
collectTupleTypeSuffixExpressions tree = do
  fields <- expectSequence "tuple_type suffix" tree
  case fields of
    [_comma, typeTree] -> collectReferenceTypeExpressions typeTree
    _ -> failExpression "tuple_type suffix is not a two-item sequence"

expectNamedNode
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError ()
expectNamedNode name tree = expectNonterminal name tree >> pure ()

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> pure body
    | otherwise -> failExpression
        ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failExpression ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence items -> pure items
  _ -> failExpression (label <> " is not a sequence node")

expectRepetition
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError [GrammarV1ReferenceParseTree]
expectRepetition label tree = case tree of
  GrammarV1ReferenceRepetition items -> pure items
  _ -> failExpression (label <> " is not a repetition node")

expectLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceExpressionCoreError ()
expectLiteral expected tree = case tree of
  GrammarV1ReferenceLiteral actual
    | actual == expected -> pure ()
    | otherwise -> failExpression
        ("expected literal " <> expected <> ", got " <> actual)
  _ -> failExpression ("expected literal " <> expected)

mapStaticReferenceError
  :: Either GrammarV1ReferenceStaticReferenceError a
  -> Either GrammarV1ReferenceExpressionCoreError a
mapStaticReferenceError = mapLeft
  (GrammarV1ReferenceExpressionCoreError . Text.pack . show)

mapTopLevelError
  :: Show e
  => Either e a
  -> Either GrammarV1ReferenceExpressionCoreError a
mapTopLevelError = mapLeft
  (GrammarV1ReferenceExpressionCoreError . Text.pack . show)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value

showText :: Show a => a -> Text
showText = Text.pack . show

failExpression
  :: Text
  -> Either GrammarV1ReferenceExpressionCoreError a
failExpression = Left . GrammarV1ReferenceExpressionCoreError
