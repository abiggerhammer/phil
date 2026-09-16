{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstCommandClosure
  ( GrammarV1ReferenceCommandClosureError (..)
  , grammarV1CommandClosureCorresponds
  ) where

import Control.Monad (zipWithM_)
import Data.List (sortOn)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..)
  , GrammarV1BranchValue (..)
  , GrammarV1Closure (..)
  , GrammarV1EffectExpression (..)
  , GrammarV1EffectSetExpression (..)
  , GrammarV1Expression (..)
  , GrammarV1FailureTarget (..)
  , GrammarV1Fallback (..)
  , GrammarV1JoinClause (..)
  , GrammarV1MatchArm (..)
  , GrammarV1MatchArmBody (..)
  , GrammarV1Proposition (..)
  , GrammarV1SessionBranch (..)
  , GrammarV1SessionExpression (..)
  , GrammarV1StateBinding (..)
  , GrammarV1StateSlot (..)
  , GrammarV1Statement (..)
  , GrammarV1StaticArgument (..)
  , GrammarV1StaticReference (..)
  , GrammarV1StaticValueExpression (..)
  , GrammarV1TermParam (..)
  , GrammarV1Type (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstBlockCommands
  ( GrammarV1ReferenceBlockCommand
  , GrammarV1ReferenceBlockCommandError
  , grammarV1ProductionBlockCommand
  , grammarV1ReferenceBlockCommand
  )
import Phil.Surface.GrammarV1.ReferenceAstExpressionCore
  ( GrammarV1ReferenceExpressionCoreError
  , grammarV1ProductionExpressionCore
  , grammarV1ReferenceExpressionCore
  )
import Phil.Surface.GrammarV1.ReferenceAstFixedCommandHelpers
  ( GrammarV1ReferenceFixedCommandHelper
  , GrammarV1ReferenceFixedCommandHelperError
  , grammarV1ProductionFixedCommandHelper
  , grammarV1ReferenceFixedCommandHelper
  )
import Phil.Surface.GrammarV1.ReferenceAstFixedCommands
  ( GrammarV1ReferenceFixedCommand
  , GrammarV1ReferenceFixedCommandError
  , grammarV1ProductionFixedCommand
  , grammarV1ReferenceFixedCommand
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( GrammarV1ReferenceParseTree (..)
  )
import Phil.Surface.Syntax
  ( Located (..)
  , SourceSpan (..)
  )

newtype GrammarV1ReferenceCommandClosureError =
  GrammarV1ReferenceCommandClosureError Text
  deriving (Eq, Show)

data ProductionCommand
  = ProductionFixed GrammarV1ReferenceFixedCommand
  | ProductionHelper GrammarV1ReferenceFixedCommandHelper
  | ProductionBlock GrammarV1ReferenceBlockCommand
  deriving (Eq, Show)

-- | Close the command-family opacity deliberately left by #889.
--
-- The outer expression projection must agree first. Then every command reachable
-- through expressions, types, static arguments/references, propositions,
-- sessions, effects, and blocks is paired with the certified parse tree's
-- command_expression nodes in lexical order and checked by the exact wrapper
-- decoder landed in #896, #897, or #900.
grammarV1CommandClosureCorresponds
  :: GrammarV1ReferenceParseTree
  -> Located GrammarV1Expression
  -> Either GrammarV1ReferenceCommandClosureError Int
grammarV1CommandClosureCorresponds referenceExpression productionExpression = do
  referenceCore <- mapExpressionError
    (grammarV1ReferenceExpressionCore referenceExpression)
  let productionCore =
        grammarV1ProductionExpressionCore (locatedValue productionExpression)
  if referenceCore /= productionCore
    then failClosure "outer expression-core correspondence failed before command closure"
    else pure ()

  let referenceCommands = collectReferenceCommands referenceExpression
      productionCommands = collectProductionCommands productionExpression
  if length referenceCommands /= length productionCommands
    then failClosure
      ("command occurrence count mismatch: certified="
        <> showText (length referenceCommands)
        <> ", production=" <> showText (length productionCommands))
    else pure ()
  zipWithM_ compareCommand referenceCommands productionCommands
  pure (length productionCommands)

collectReferenceCommands
  :: GrammarV1ReferenceParseTree
  -> [GrammarV1ReferenceParseTree]
collectReferenceCommands tree = case tree of
  GrammarV1ReferenceNonterminal name body ->
    (if name == "command_expression" then [tree] else [])
      <> collectReferenceCommands body
  GrammarV1ReferenceSequence values -> concatMap collectReferenceCommands values
  GrammarV1ReferenceAlternative _ value -> collectReferenceCommands value
  GrammarV1ReferenceOptionalSome value -> collectReferenceCommands value
  GrammarV1ReferenceRepetition values -> concatMap collectReferenceCommands values
  GrammarV1ReferenceLiteral _ -> []
  GrammarV1ReferenceLexical _ _ -> []
  GrammarV1ReferenceOptionalNone -> []

collectProductionCommands
  :: Located GrammarV1Expression
  -> [Located GrammarV1Expression]
collectProductionCommands =
  sortOn (sourceSpanStart . locatedSpan) . commandsExpression

commandsExpression
  :: Located GrammarV1Expression
  -> [Located GrammarV1Expression]
commandsExpression locatedExpression@(Located _ expression) =
  current <> children
  where
    current = case classifyProductionCommand expression of
      Just _ -> [locatedExpression]
      Nothing -> []
    children = case expression of
      GrammarV1NameExpression reference arguments ->
        commandsStaticReference reference <> concatMap commandsExpression arguments
      GrammarV1BoolExpression _ -> []
      GrammarV1UnitExpression -> []
      GrammarV1IntegerExpression _ -> []
      GrammarV1NegateExpression value -> commandsExpression value
      GrammarV1ProjectionExpression value _ -> commandsExpression value
      GrammarV1ShiftExpression left _ right ->
        commandsExpression left <> commandsExpression right
      GrammarV1BinaryExpression left _ right ->
        commandsExpression left <> commandsExpression right
      GrammarV1FallbackExpression base fallback ->
        commandsExpression base <> commandsFallback fallback
      GrammarV1ConstructExpression target assignments ->
        commandsStaticReference (locatedValue target)
          <> concatMap (commandsExpression . snd) assignments
      GrammarV1BorrowExpression value _ body ->
        commandsExpression value <> commandsBlock body
      GrammarV1MatchExpression scrutinee joinClause arms ->
        commandsExpression scrutinee
          <> maybe [] commandsJoinClause joinClause
          <> concatMap commandsMatchArm arms
      GrammarV1DecideExpression scrutinee arms ->
        commandsExpression scrutinee <> concatMap commandsMatchArm arms
      GrammarV1BreakExpression arguments -> concatMap commandsExpression arguments
      GrammarV1ReceiveFrameExpression source -> commandsExpression source
      GrammarV1ReceiveExactExpression amount endpoint evidence ->
        commandsExpression amount
          <> commandsExpression endpoint
          <> maybe [] commandsExpression evidence
      GrammarV1ReceiveExpression sourceType endpoint ->
        commandsType (locatedValue sourceType) <> commandsExpression endpoint
      GrammarV1RecognizeExpression recognizer source ->
        commandsStaticReference (locatedValue recognizer) <> commandsExpression source
      GrammarV1ValidateExpression validator position endpoint ->
        commandsStaticReference (locatedValue validator)
          <> maybe [] commandsExpression position
          <> commandsExpression endpoint
      GrammarV1SendExactExpression value endpoint ->
        commandsExpression value <> commandsExpression endpoint
      GrammarV1SendExpression value endpoint ->
        commandsExpression value <> commandsExpression endpoint
      GrammarV1SelectExpression branch endpoint evidence ->
        commandsBranchValue branch
          <> commandsExpression endpoint
          <> maybe [] commandsExpression evidence
      GrammarV1CommitReceiveExpression source evidence ->
        commandsExpression source <> commandsExpression evidence
      GrammarV1FailExpression target endpoint ->
        commandsFailureTarget target <> commandsExpression endpoint
      GrammarV1CloseExpression endpoint -> commandsExpression endpoint
      GrammarV1ReleaseExpression value -> commandsExpression value
      GrammarV1ConvertExpression value sourceType ->
        commandsExpression value <> commandsType (locatedValue sourceType)
      GrammarV1AcceptExpression value sourceType ->
        commandsExpression value <> commandsType (locatedValue sourceType)
      GrammarV1ProveExpression proposition -> commandsProposition proposition
      GrammarV1TransportExpression value sourceType evidence ->
        commandsExpression value
          <> commandsType (locatedValue sourceType)
          <> commandsExpression evidence
      GrammarV1TupleExpression values -> concatMap commandsExpression values
      GrammarV1ParenthesizedExpression value -> commandsExpression value
      GrammarV1OfferExpression scrutinee arms ->
        commandsExpression scrutinee <> concatMap commandsMatchArm arms
      GrammarV1IfExpression condition joinClause thenBlock elseBlock ->
        commandsExpression condition
          <> maybe [] commandsJoinClause joinClause
          <> commandsBlock thenBlock
          <> maybe [] commandsBlock elseBlock
      GrammarV1LoopExpression bindings invariant body ->
        concatMap commandsStateBinding bindings
          <> maybe [] commandsProposition invariant
          <> commandsBlock body
      GrammarV1ContinueExpression arguments -> concatMap commandsExpression arguments
      GrammarV1ClosureExpression closure -> commandsClosure closure
      GrammarV1RejectExpression value -> commandsExpression value

commandsFallback :: Located GrammarV1Fallback -> [Located GrammarV1Expression]
commandsFallback (Located _ fallback) = case fallback of
  GrammarV1FailFallback target -> commandsFailureTarget target
  GrammarV1RejectFallback value -> commandsExpression value

commandsFailureTarget
  :: Located GrammarV1FailureTarget
  -> [Located GrammarV1Expression]
commandsFailureTarget (Located _ target) =
  commandsStaticReference (grammarV1FailureTargetReference target)
    <> concatMap commandsExpression (grammarV1FailureTargetArguments target)

commandsBranchValue
  :: Located GrammarV1BranchValue
  -> [Located GrammarV1Expression]
commandsBranchValue (Located _ branch) =
  concatMap commandsExpression (grammarV1BranchValueArguments branch)

commandsClosure :: GrammarV1Closure -> [Located GrammarV1Expression]
commandsClosure closure =
  concatMap commandsTermParam (grammarV1ClosureTermParams closure)
    <> commandsType (locatedValue (grammarV1ClosureSatisfies closure))
    <> commandsBlock (grammarV1ClosureBody closure)

commandsBlock :: Located GrammarV1Block -> [Located GrammarV1Expression]
commandsBlock (Located _ (GrammarV1Block statements)) =
  concatMap commandsStatement statements

commandsStatement :: Located GrammarV1Statement -> [Located GrammarV1Expression]
commandsStatement (Located _ statement) = case statement of
  GrammarV1LetStatement _ value -> commandsExpression value
  GrammarV1ReturnStatement value -> commandsExpression value
  GrammarV1ExpressionStatement value -> commandsExpression value

commandsMatchArm :: Located GrammarV1MatchArm -> [Located GrammarV1Expression]
commandsMatchArm (Located _ arm) = case grammarV1MatchArmBody arm of
  GrammarV1MatchArmBlock block -> commandsBlock block
  GrammarV1MatchArmStatement statement -> commandsStatement statement

commandsJoinClause
  :: Located GrammarV1JoinClause
  -> [Located GrammarV1Expression]
commandsJoinClause (Located _ clause) =
  concatMap commandsStateSlot (grammarV1JoinState clause)
    <> maybe [] commandsProposition (grammarV1JoinInvariant clause)

commandsStateSlot :: Located GrammarV1StateSlot -> [Located GrammarV1Expression]
commandsStateSlot (Located _ slot) =
  commandsType (locatedValue (grammarV1StateSlotType slot))

commandsStateBinding
  :: Located GrammarV1StateBinding
  -> [Located GrammarV1Expression]
commandsStateBinding (Located _ binding) =
  maybe [] (commandsType . locatedValue) (grammarV1StateBindingType binding)
    <> commandsExpression (grammarV1StateBindingInitializer binding)

commandsTermParam :: Located GrammarV1TermParam -> [Located GrammarV1Expression]
commandsTermParam (Located _ parameter) =
  commandsType (locatedValue (grammarV1TermParamType parameter))

commandsType :: GrammarV1Type -> [Located GrammarV1Expression]
commandsType sourceType = case sourceType of
  GrammarV1UnitType -> []
  GrammarV1BoolType -> []
  GrammarV1UnsignedType _ -> []
  GrammarV1BytesType value -> commandsExpression value
  GrammarV1FrameType reference -> commandsStaticReference (locatedValue reference)
  GrammarV1ProofType proposition -> commandsProposition proposition
  GrammarV1ValidatedType validator start end ->
    commandsStaticReference (locatedValue validator)
      <> commandsExpression start
      <> commandsExpression end
  GrammarV1RefinementType _ base proposition ->
    commandsType (locatedValue base) <> commandsProposition proposition
  GrammarV1TupleType values -> concatMap (commandsType . locatedValue) values
  GrammarV1NamedType reference -> commandsStaticReference reference

commandsStaticReference
  :: GrammarV1StaticReference
  -> [Located GrammarV1Expression]
commandsStaticReference reference =
  concatMap commandsStaticArgument (grammarV1StaticReferenceArguments reference)

commandsStaticArgument
  :: GrammarV1StaticArgument
  -> [Located GrammarV1Expression]
commandsStaticArgument argument = case argument of
  GrammarV1StaticTypeArgument sourceType -> commandsType sourceType
  GrammarV1StaticReferenceArgument reference -> commandsStaticReference reference
  GrammarV1StaticBoolArgument _ -> []
  GrammarV1StaticUnitArgument -> []
  GrammarV1StaticIntegerArgument _ -> []
  GrammarV1StaticValueArgument value -> commandsStaticValue value
  GrammarV1StaticEffectSetArgument effectSet -> commandsEffectSet effectSet
  GrammarV1StaticSessionArgument session -> commandsSession session

commandsStaticValue
  :: Located GrammarV1StaticValueExpression
  -> [Located GrammarV1Expression]
commandsStaticValue (Located _ value) = case value of
  GrammarV1StaticValueBool _ -> []
  GrammarV1StaticValueUnit -> []
  GrammarV1StaticValueInteger _ -> []
  GrammarV1StaticValueReference reference ->
    commandsStaticReference (locatedValue reference)
  GrammarV1StaticValueParenthesized nested -> commandsStaticValue nested
  GrammarV1StaticValueProjection nested _ -> commandsStaticValue nested
  GrammarV1StaticValueBinary left _ right ->
    commandsStaticValue left <> commandsStaticValue right

commandsEffectSet
  :: Located GrammarV1EffectSetExpression
  -> [Located GrammarV1Expression]
commandsEffectSet (Located _ effectSet) = case effectSet of
  GrammarV1EffectSetLiteral effects -> concatMap commandsEffect effects
  GrammarV1EffectSetReference reference ->
    commandsStaticReference (locatedValue reference)

commandsEffect
  :: Located GrammarV1EffectExpression
  -> [Located GrammarV1Expression]
commandsEffect (Located _ effect) =
  commandsStaticReference (locatedValue (grammarV1EffectReference effect))
    <> concatMap commandsExpression (grammarV1EffectArguments effect)

commandsProposition
  :: Located GrammarV1Proposition
  -> [Located GrammarV1Expression]
commandsProposition (Located _ proposition) = case proposition of
  GrammarV1TrueProposition -> []
  GrammarV1FalseProposition -> []
  GrammarV1RelationProposition left _ right ->
    commandsExpression left <> commandsExpression right
  GrammarV1ClaimApplicationProposition reference arguments ->
    commandsStaticReference reference <> concatMap commandsExpression arguments
  GrammarV1NotProposition nested -> commandsProposition nested
  GrammarV1AndProposition left right ->
    commandsProposition left <> commandsProposition right
  GrammarV1OrProposition left right ->
    commandsProposition left <> commandsProposition right

commandsSession
  :: Located GrammarV1SessionExpression
  -> [Located GrammarV1Expression]
commandsSession (Located _ session) = case session of
  GrammarV1SessionReference reference -> commandsStaticReference reference
  GrammarV1SessionSend parameter boundary guard continuation ->
    commandsTermParam parameter
      <> maybe [] (commandsStaticReference . locatedValue) boundary
      <> maybe [] commandsProposition guard
      <> commandsSession continuation
  GrammarV1SessionReceive parameter boundary guard continuation ->
    commandsTermParam parameter
      <> maybe [] (commandsStaticReference . locatedValue) boundary
      <> maybe [] commandsProposition guard
      <> commandsSession continuation
  GrammarV1SessionSelect branches -> concatMap commandsSessionBranch branches
  GrammarV1SessionOffer branches -> concatMap commandsSessionBranch branches
  GrammarV1SessionEnd _ -> []
  GrammarV1SessionRecursive _ nested -> commandsSession nested
  GrammarV1SessionContinue _ -> []

commandsSessionBranch
  :: Located GrammarV1SessionBranch
  -> [Located GrammarV1Expression]
commandsSessionBranch (Located _ branch) =
  maybe [] (concatMap commandsTermParam) (grammarV1SessionBranchParams branch)
    <> maybe [] (commandsStaticReference . locatedValue)
      (grammarV1SessionBranchBoundary branch)
    <> maybe [] commandsProposition (grammarV1SessionBranchGuard branch)
    <> commandsSession (grammarV1SessionBranchContinuation branch)

classifyProductionCommand :: GrammarV1Expression -> Maybe ProductionCommand
classifyProductionCommand expression =
  case grammarV1ProductionFixedCommand expression of
    Just value -> Just (ProductionFixed value)
    Nothing -> case grammarV1ProductionFixedCommandHelper expression of
      Just value -> Just (ProductionHelper value)
      Nothing -> ProductionBlock <$> grammarV1ProductionBlockCommand expression

compareCommand
  :: GrammarV1ReferenceParseTree
  -> Located GrammarV1Expression
  -> Either GrammarV1ReferenceCommandClosureError ()
compareCommand referenceTree (Located _ productionExpression) =
  case classifyProductionCommand productionExpression of
    Nothing -> failClosure "production command traversal yielded a non-command expression"
    Just (ProductionFixed expected) -> do
      actual <- mapFixedError (grammarV1ReferenceFixedCommand referenceTree)
      requireProjection "fixed command" expected actual
    Just (ProductionHelper expected) -> do
      actual <- mapHelperError (grammarV1ReferenceFixedCommandHelper referenceTree)
      requireProjection "fixed command helper" expected actual
    Just (ProductionBlock expected) -> do
      actual <- mapBlockError (grammarV1ReferenceBlockCommand referenceTree)
      requireProjection "block command" expected actual

requireProjection
  :: (Eq a, Show a)
  => Text
  -> a
  -> Maybe a
  -> Either GrammarV1ReferenceCommandClosureError ()
requireProjection label expected actual = case actual of
  Just value
    | value == expected -> pure ()
    | otherwise -> failClosure
        (label <> " payload mismatch: certified=" <> showText value
          <> ", production=" <> showText expected)
  Nothing -> failClosure (label <> " decoder did not select the production command family")

mapExpressionError
  :: Either GrammarV1ReferenceExpressionCoreError a
  -> Either GrammarV1ReferenceCommandClosureError a
mapExpressionError = mapLeft
  (GrammarV1ReferenceCommandClosureError . Text.pack . show)

mapFixedError
  :: Either GrammarV1ReferenceFixedCommandError a
  -> Either GrammarV1ReferenceCommandClosureError a
mapFixedError = mapLeft
  (GrammarV1ReferenceCommandClosureError . Text.pack . show)

mapHelperError
  :: Either GrammarV1ReferenceFixedCommandHelperError a
  -> Either GrammarV1ReferenceCommandClosureError a
mapHelperError = mapLeft
  (GrammarV1ReferenceCommandClosureError . Text.pack . show)

mapBlockError
  :: Either GrammarV1ReferenceBlockCommandError a
  -> Either GrammarV1ReferenceCommandClosureError a
mapBlockError = mapLeft
  (GrammarV1ReferenceCommandClosureError . Text.pack . show)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value

showText :: Show a => a -> Text
showText = Text.pack . show

failClosure
  :: Text
  -> Either GrammarV1ReferenceCommandClosureError a
failClosure = Left . GrammarV1ReferenceCommandClosureError
