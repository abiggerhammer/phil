{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstStaticArgumentClosure
  ( GrammarV1ReferenceStaticArgumentClosureError (..)
  , grammarV1StaticArgumentClosureCorresponds
  ) where

import Control.Monad (zipWithM_)
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
import Phil.Surface.GrammarV1.ReferenceAstEffects
  ( GrammarV1ReferenceEffectsError
  , grammarV1ProductionEffectSetSpine
  , grammarV1ReferenceEffectSetSpine
  )
import Phil.Surface.GrammarV1.ReferenceAstSessions
  ( GrammarV1ReferenceSessionError
  , grammarV1ProductionSessionCore
  , grammarV1ReferenceSessionCore
  )
import Phil.Surface.GrammarV1.ReferenceAstStaticReference
  ( GrammarV1ReferenceStaticReferenceError
  , grammarV1ProductionStaticReferenceSpine
  , grammarV1ReferenceStaticReferenceSpine
  )
import Phil.Surface.GrammarV1.ReferenceAstStaticValue
  ( GrammarV1ReferenceStaticValue (..)
  , GrammarV1ReferenceStaticValueError
  , grammarV1ProductionStaticValue
  , grammarV1ReferenceStaticValue
  )
import Phil.Surface.GrammarV1.ReferenceAstTypePayload
  ( GrammarV1ReferenceTypePayloadError
  , grammarV1ProductionTypePayload
  , grammarV1ReferenceTypePayload
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( GrammarV1ReferenceParseTree (..)
  )
import Phil.Surface.Syntax (Located (..))

newtype GrammarV1ReferenceStaticArgumentClosureError =
  GrammarV1ReferenceStaticArgumentClosureError Text
  deriving (Eq, Show)

-- | Replace #883's shallow static-argument tags with transitive payload checks.
--
-- The root static-reference spine must agree first. Every static_argument below
-- that reference is then compared in preorder against the production argument
-- graph. Category-specific payloads reuse the already-landed type/session/
-- static-value/effect correspondences, while this traversal makes nested static
-- arguments visible at every depth.
grammarV1StaticArgumentClosureCorresponds
  :: GrammarV1ReferenceParseTree
  -> GrammarV1StaticReference
  -> Either GrammarV1ReferenceStaticArgumentClosureError Int
grammarV1StaticArgumentClosureCorresponds referenceTree productionReference = do
  referenceSpine <- mapStaticReferenceError
    (grammarV1ReferenceStaticReferenceSpine referenceTree)
  let productionSpine = grammarV1ProductionStaticReferenceSpine productionReference
  if referenceSpine /= productionSpine
    then failClosure "root static-reference spine mismatch before payload closure"
    else pure ()

  let referenceArguments = collectReferenceStaticArguments referenceTree
      productionArguments = collectProductionStaticArguments productionReference
  if length referenceArguments /= length productionArguments
    then failClosure
      ("static-argument occurrence count mismatch: certified="
        <> showText (length referenceArguments)
        <> ", production=" <> showText (length productionArguments))
    else pure ()
  zipWithM_ compareStaticArgument referenceArguments productionArguments
  pure (length productionArguments)

collectReferenceStaticArguments
  :: GrammarV1ReferenceParseTree
  -> [GrammarV1ReferenceParseTree]
collectReferenceStaticArguments tree = case tree of
  GrammarV1ReferenceNonterminal name body ->
    (if name == "static_argument" then [tree] else [])
      <> collectReferenceStaticArguments body
  GrammarV1ReferenceSequence values -> concatMap collectReferenceStaticArguments values
  GrammarV1ReferenceAlternative _ value -> collectReferenceStaticArguments value
  GrammarV1ReferenceOptionalSome value -> collectReferenceStaticArguments value
  GrammarV1ReferenceRepetition values -> concatMap collectReferenceStaticArguments values
  GrammarV1ReferenceLiteral _ -> []
  GrammarV1ReferenceLexical _ _ -> []
  GrammarV1ReferenceOptionalNone -> []

collectProductionStaticArguments
  :: GrammarV1StaticReference
  -> [GrammarV1StaticArgument]
collectProductionStaticArguments reference =
  concatMap argumentAndNested (grammarV1StaticReferenceArguments reference)
  where
    argumentAndNested argument = argument : staticArgumentsArgument argument

staticArgumentsArgument :: GrammarV1StaticArgument -> [GrammarV1StaticArgument]
staticArgumentsArgument argument = case argument of
  GrammarV1StaticTypeArgument sourceType -> staticArgumentsType sourceType
  GrammarV1StaticReferenceArgument reference -> collectProductionStaticArguments reference
  GrammarV1StaticBoolArgument _ -> []
  GrammarV1StaticUnitArgument -> []
  GrammarV1StaticIntegerArgument _ -> []
  GrammarV1StaticValueArgument value -> staticArgumentsStaticValue value
  GrammarV1StaticEffectSetArgument effectSet -> staticArgumentsEffectSet effectSet
  GrammarV1StaticSessionArgument session -> staticArgumentsSession session

staticArgumentsType :: GrammarV1Type -> [GrammarV1StaticArgument]
staticArgumentsType sourceType = case sourceType of
  GrammarV1UnitType -> []
  GrammarV1BoolType -> []
  GrammarV1UnsignedType _ -> []
  GrammarV1BytesType expression -> staticArgumentsExpression expression
  GrammarV1FrameType reference -> collectProductionStaticArguments (locatedValue reference)
  GrammarV1ProofType proposition -> staticArgumentsProposition proposition
  GrammarV1ValidatedType reference first second ->
    collectProductionStaticArguments (locatedValue reference)
      <> staticArgumentsExpression first
      <> staticArgumentsExpression second
  GrammarV1RefinementType _ base proposition ->
    staticArgumentsType (locatedValue base) <> staticArgumentsProposition proposition
  GrammarV1TupleType values -> concatMap (staticArgumentsType . locatedValue) values
  GrammarV1NamedType reference -> collectProductionStaticArguments reference

staticArgumentsExpression :: Located GrammarV1Expression -> [GrammarV1StaticArgument]
staticArgumentsExpression (Located _ expression) = case expression of
  GrammarV1NameExpression reference arguments ->
    collectProductionStaticArguments reference <> concatMap staticArgumentsExpression arguments
  GrammarV1BoolExpression _ -> []
  GrammarV1UnitExpression -> []
  GrammarV1IntegerExpression _ -> []
  GrammarV1NegateExpression value -> staticArgumentsExpression value
  GrammarV1ProjectionExpression value _ -> staticArgumentsExpression value
  GrammarV1ShiftExpression left _ right ->
    staticArgumentsExpression left <> staticArgumentsExpression right
  GrammarV1BinaryExpression left _ right ->
    staticArgumentsExpression left <> staticArgumentsExpression right
  GrammarV1FallbackExpression base fallback ->
    staticArgumentsExpression base <> staticArgumentsFallback fallback
  GrammarV1ConstructExpression target assignments ->
    collectProductionStaticArguments (locatedValue target)
      <> concatMap (staticArgumentsExpression . snd) assignments
  GrammarV1BorrowExpression value _ body ->
    staticArgumentsExpression value <> staticArgumentsBlock body
  GrammarV1MatchExpression scrutinee joinClause arms ->
    staticArgumentsExpression scrutinee
      <> maybe [] staticArgumentsJoinClause joinClause
      <> concatMap staticArgumentsMatchArm arms
  GrammarV1DecideExpression scrutinee arms ->
    staticArgumentsExpression scrutinee <> concatMap staticArgumentsMatchArm arms
  GrammarV1BreakExpression arguments -> concatMap staticArgumentsExpression arguments
  GrammarV1ReceiveFrameExpression source -> staticArgumentsExpression source
  GrammarV1ReceiveExactExpression amount endpoint evidence ->
    staticArgumentsExpression amount
      <> staticArgumentsExpression endpoint
      <> maybe [] staticArgumentsExpression evidence
  GrammarV1ReceiveExpression sourceType endpoint ->
    staticArgumentsType (locatedValue sourceType) <> staticArgumentsExpression endpoint
  GrammarV1RecognizeExpression recognizer source ->
    collectProductionStaticArguments (locatedValue recognizer)
      <> staticArgumentsExpression source
  GrammarV1ValidateExpression validator position endpoint ->
    collectProductionStaticArguments (locatedValue validator)
      <> maybe [] staticArgumentsExpression position
      <> staticArgumentsExpression endpoint
  GrammarV1SendExactExpression value endpoint ->
    staticArgumentsExpression value <> staticArgumentsExpression endpoint
  GrammarV1SendExpression value endpoint ->
    staticArgumentsExpression value <> staticArgumentsExpression endpoint
  GrammarV1SelectExpression branch endpoint evidence ->
    staticArgumentsBranchValue branch
      <> staticArgumentsExpression endpoint
      <> maybe [] staticArgumentsExpression evidence
  GrammarV1CommitReceiveExpression source evidence ->
    staticArgumentsExpression source <> staticArgumentsExpression evidence
  GrammarV1FailExpression target endpoint ->
    staticArgumentsFailureTarget target <> staticArgumentsExpression endpoint
  GrammarV1CloseExpression endpoint -> staticArgumentsExpression endpoint
  GrammarV1ReleaseExpression value -> staticArgumentsExpression value
  GrammarV1ConvertExpression value sourceType ->
    staticArgumentsExpression value <> staticArgumentsType (locatedValue sourceType)
  GrammarV1AcceptExpression value sourceType ->
    staticArgumentsExpression value <> staticArgumentsType (locatedValue sourceType)
  GrammarV1ProveExpression proposition -> staticArgumentsProposition proposition
  GrammarV1TransportExpression value sourceType evidence ->
    staticArgumentsExpression value
      <> staticArgumentsType (locatedValue sourceType)
      <> staticArgumentsExpression evidence
  GrammarV1TupleExpression values -> concatMap staticArgumentsExpression values
  GrammarV1ParenthesizedExpression value -> staticArgumentsExpression value
  GrammarV1OfferExpression scrutinee arms ->
    staticArgumentsExpression scrutinee <> concatMap staticArgumentsMatchArm arms
  GrammarV1IfExpression condition joinClause thenBlock elseBlock ->
    staticArgumentsExpression condition
      <> maybe [] staticArgumentsJoinClause joinClause
      <> staticArgumentsBlock thenBlock
      <> maybe [] staticArgumentsBlock elseBlock
  GrammarV1LoopExpression bindings invariant body ->
    concatMap staticArgumentsStateBinding bindings
      <> maybe [] staticArgumentsProposition invariant
      <> staticArgumentsBlock body
  GrammarV1ContinueExpression arguments -> concatMap staticArgumentsExpression arguments
  GrammarV1ClosureExpression closure -> staticArgumentsClosure closure
  GrammarV1RejectExpression value -> staticArgumentsExpression value

staticArgumentsFallback :: Located GrammarV1Fallback -> [GrammarV1StaticArgument]
staticArgumentsFallback (Located _ fallback) = case fallback of
  GrammarV1FailFallback target -> staticArgumentsFailureTarget target
  GrammarV1RejectFallback value -> staticArgumentsExpression value

staticArgumentsFailureTarget
  :: Located GrammarV1FailureTarget
  -> [GrammarV1StaticArgument]
staticArgumentsFailureTarget (Located _ target) =
  collectProductionStaticArguments (grammarV1FailureTargetReference target)
    <> concatMap staticArgumentsExpression (grammarV1FailureTargetArguments target)

staticArgumentsBranchValue
  :: Located GrammarV1BranchValue
  -> [GrammarV1StaticArgument]
staticArgumentsBranchValue (Located _ branch) =
  concatMap staticArgumentsExpression (grammarV1BranchValueArguments branch)

staticArgumentsClosure :: GrammarV1Closure -> [GrammarV1StaticArgument]
staticArgumentsClosure closure =
  concatMap staticArgumentsTermParam (grammarV1ClosureTermParams closure)
    <> staticArgumentsType (locatedValue (grammarV1ClosureSatisfies closure))
    <> staticArgumentsBlock (grammarV1ClosureBody closure)

staticArgumentsBlock :: Located GrammarV1Block -> [GrammarV1StaticArgument]
staticArgumentsBlock (Located _ (GrammarV1Block statements)) =
  concatMap staticArgumentsStatement statements

staticArgumentsStatement :: Located GrammarV1Statement -> [GrammarV1StaticArgument]
staticArgumentsStatement (Located _ statement) = case statement of
  GrammarV1LetStatement _ value -> staticArgumentsExpression value
  GrammarV1ReturnStatement value -> staticArgumentsExpression value
  GrammarV1ExpressionStatement value -> staticArgumentsExpression value

staticArgumentsMatchArm :: Located GrammarV1MatchArm -> [GrammarV1StaticArgument]
staticArgumentsMatchArm (Located _ arm) = case grammarV1MatchArmBody arm of
  GrammarV1MatchArmBlock block -> staticArgumentsBlock block
  GrammarV1MatchArmStatement statement -> staticArgumentsStatement statement

staticArgumentsJoinClause
  :: Located GrammarV1JoinClause
  -> [GrammarV1StaticArgument]
staticArgumentsJoinClause (Located _ clause) =
  concatMap staticArgumentsStateSlot (grammarV1JoinState clause)
    <> maybe [] staticArgumentsProposition (grammarV1JoinInvariant clause)

staticArgumentsStateSlot :: Located GrammarV1StateSlot -> [GrammarV1StaticArgument]
staticArgumentsStateSlot (Located _ slot) =
  staticArgumentsType (locatedValue (grammarV1StateSlotType slot))

staticArgumentsStateBinding
  :: Located GrammarV1StateBinding
  -> [GrammarV1StaticArgument]
staticArgumentsStateBinding (Located _ binding) =
  maybe [] (staticArgumentsType . locatedValue) (grammarV1StateBindingType binding)
    <> staticArgumentsExpression (grammarV1StateBindingInitializer binding)

staticArgumentsTermParam :: Located GrammarV1TermParam -> [GrammarV1StaticArgument]
staticArgumentsTermParam (Located _ parameter) =
  staticArgumentsType (locatedValue (grammarV1TermParamType parameter))

staticArgumentsStaticValue
  :: Located GrammarV1StaticValueExpression
  -> [GrammarV1StaticArgument]
staticArgumentsStaticValue (Located _ value) = case value of
  GrammarV1StaticValueBool _ -> []
  GrammarV1StaticValueUnit -> []
  GrammarV1StaticValueInteger _ -> []
  GrammarV1StaticValueReference reference ->
    collectProductionStaticArguments (locatedValue reference)
  GrammarV1StaticValueParenthesized nested -> staticArgumentsStaticValue nested
  GrammarV1StaticValueProjection nested _ -> staticArgumentsStaticValue nested
  GrammarV1StaticValueBinary left _ right ->
    staticArgumentsStaticValue left <> staticArgumentsStaticValue right

staticArgumentsEffectSet
  :: Located GrammarV1EffectSetExpression
  -> [GrammarV1StaticArgument]
staticArgumentsEffectSet (Located _ effectSet) = case effectSet of
  GrammarV1EffectSetLiteral effects -> concatMap staticArgumentsEffect effects
  GrammarV1EffectSetReference reference ->
    collectProductionStaticArguments (locatedValue reference)

staticArgumentsEffect
  :: Located GrammarV1EffectExpression
  -> [GrammarV1StaticArgument]
staticArgumentsEffect (Located _ effect) =
  collectProductionStaticArguments (locatedValue (grammarV1EffectReference effect))
    <> concatMap staticArgumentsExpression (grammarV1EffectArguments effect)

staticArgumentsProposition
  :: Located GrammarV1Proposition
  -> [GrammarV1StaticArgument]
staticArgumentsProposition (Located _ proposition) = case proposition of
  GrammarV1TrueProposition -> []
  GrammarV1FalseProposition -> []
  GrammarV1RelationProposition left _ right ->
    staticArgumentsExpression left <> staticArgumentsExpression right
  GrammarV1ClaimApplicationProposition reference arguments ->
    collectProductionStaticArguments reference <> concatMap staticArgumentsExpression arguments
  GrammarV1NotProposition nested -> staticArgumentsProposition nested
  GrammarV1AndProposition left right ->
    staticArgumentsProposition left <> staticArgumentsProposition right
  GrammarV1OrProposition left right ->
    staticArgumentsProposition left <> staticArgumentsProposition right

staticArgumentsSession
  :: Located GrammarV1SessionExpression
  -> [GrammarV1StaticArgument]
staticArgumentsSession (Located _ session) = case session of
  GrammarV1SessionReference reference -> collectProductionStaticArguments reference
  GrammarV1SessionSend parameter boundary guard continuation ->
    staticArgumentsTermParam parameter
      <> maybe [] (collectProductionStaticArguments . locatedValue) boundary
      <> maybe [] staticArgumentsProposition guard
      <> staticArgumentsSession continuation
  GrammarV1SessionReceive parameter boundary guard continuation ->
    staticArgumentsTermParam parameter
      <> maybe [] (collectProductionStaticArguments . locatedValue) boundary
      <> maybe [] staticArgumentsProposition guard
      <> staticArgumentsSession continuation
  GrammarV1SessionSelect branches -> concatMap staticArgumentsSessionBranch branches
  GrammarV1SessionOffer branches -> concatMap staticArgumentsSessionBranch branches
  GrammarV1SessionEnd _ -> []
  GrammarV1SessionRecursive _ nested -> staticArgumentsSession nested
  GrammarV1SessionContinue _ -> []

staticArgumentsSessionBranch
  :: Located GrammarV1SessionBranch
  -> [GrammarV1StaticArgument]
staticArgumentsSessionBranch (Located _ branch) =
  maybe [] (concatMap staticArgumentsTermParam) (grammarV1SessionBranchParams branch)
    <> maybe [] (collectProductionStaticArguments . locatedValue)
      (grammarV1SessionBranchBoundary branch)
    <> maybe [] staticArgumentsProposition (grammarV1SessionBranchGuard branch)
    <> staticArgumentsSession (grammarV1SessionBranchContinuation branch)

compareStaticArgument
  :: GrammarV1ReferenceParseTree
  -> GrammarV1StaticArgument
  -> Either GrammarV1ReferenceStaticArgumentClosureError ()
compareStaticArgument tree productionArgument = do
  body <- expectNonterminal "static_argument" tree
  case body of
    GrammarV1ReferenceAlternative index selected -> case index of
      0 -> compareTypeArgument selected productionArgument
      1 -> compareSessionArgument selected productionArgument
      2 -> compareStaticValueArgument selected productionArgument
      3 -> compareEffectSetArgument selected productionArgument
      _ -> failClosure
        ("static_argument alternative out of range: " <> showText index)
    _ -> failClosure "static_argument body is not an alternative node"

compareTypeArgument
  :: GrammarV1ReferenceParseTree
  -> GrammarV1StaticArgument
  -> Either GrammarV1ReferenceStaticArgumentClosureError ()
compareTypeArgument selected productionArgument = case productionArgument of
  GrammarV1StaticTypeArgument sourceType -> do
    referenceValue <- mapTypePayloadError
      (grammarV1ReferenceTypePayload
        (GrammarV1ReferenceNonterminal
          "type_expression"
          (GrammarV1ReferenceAlternative 0 selected)))
    requireEqual "static type argument" referenceValue
      (grammarV1ProductionTypePayload sourceType)
  _ -> failClosure "certified static type argument paired with different production category"

compareSessionArgument
  :: GrammarV1ReferenceParseTree
  -> GrammarV1StaticArgument
  -> Either GrammarV1ReferenceStaticArgumentClosureError ()
compareSessionArgument selected productionArgument = case productionArgument of
  GrammarV1StaticSessionArgument session -> do
    referenceValue <- mapSessionError
      (grammarV1ReferenceSessionCore
        (GrammarV1ReferenceNonterminal
          "session_expression"
          (GrammarV1ReferenceAlternative 0 selected)))
    requireEqual "static session argument" referenceValue
      (grammarV1ProductionSessionCore (locatedValue session))
  _ -> failClosure "certified static session argument paired with different production category"

compareStaticValueArgument
  :: GrammarV1ReferenceParseTree
  -> GrammarV1StaticArgument
  -> Either GrammarV1ReferenceStaticArgumentClosureError ()
compareStaticValueArgument selected productionArgument = do
  referenceValue <- mapStaticValueError (grammarV1ReferenceStaticValue selected)
  productionValue <- case productionArgument of
    GrammarV1StaticReferenceArgument reference -> pure
      (GrammarV1ReferenceStaticReference
        (grammarV1ProductionStaticReferenceSpine reference))
    GrammarV1StaticBoolArgument value -> pure (GrammarV1ReferenceStaticBool value)
    GrammarV1StaticUnitArgument -> pure GrammarV1ReferenceStaticUnit
    GrammarV1StaticIntegerArgument value -> pure (GrammarV1ReferenceStaticInteger value)
    GrammarV1StaticValueArgument value -> pure
      (grammarV1ProductionStaticValue (locatedValue value))
    _ -> failClosure
      "certified static value argument paired with different production category"
  requireEqual "static value argument" referenceValue productionValue

compareEffectSetArgument
  :: GrammarV1ReferenceParseTree
  -> GrammarV1StaticArgument
  -> Either GrammarV1ReferenceStaticArgumentClosureError ()
compareEffectSetArgument selected productionArgument = case productionArgument of
  GrammarV1StaticEffectSetArgument effectSet -> do
    referenceValue <- mapEffectsError
      (grammarV1ReferenceEffectSetSpine
        (GrammarV1ReferenceNonterminal
          "effect_set_expression"
          (GrammarV1ReferenceAlternative 0 selected)))
    requireEqual "static effect-set argument" referenceValue
      (grammarV1ProductionEffectSetSpine (locatedValue effectSet))
  _ -> failClosure
    "certified static effect-set argument paired with different production category"

requireEqual
  :: (Eq a, Show a)
  => Text
  -> a
  -> a
  -> Either GrammarV1ReferenceStaticArgumentClosureError ()
requireEqual label referenceValue productionValue
  | referenceValue == productionValue = pure ()
  | otherwise = failClosure
      (label <> " mismatch: certified=" <> showText referenceValue
        <> ", production=" <> showText productionValue)

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceStaticArgumentClosureError GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> pure body
    | otherwise -> failClosure
        ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failClosure ("expected nonterminal " <> expected)

mapStaticReferenceError
  :: Either GrammarV1ReferenceStaticReferenceError a
  -> Either GrammarV1ReferenceStaticArgumentClosureError a
mapStaticReferenceError = mapLeft (failText . show)

mapTypePayloadError
  :: Either GrammarV1ReferenceTypePayloadError a
  -> Either GrammarV1ReferenceStaticArgumentClosureError a
mapTypePayloadError = mapLeft (failText . show)

mapSessionError
  :: Either GrammarV1ReferenceSessionError a
  -> Either GrammarV1ReferenceStaticArgumentClosureError a
mapSessionError = mapLeft (failText . show)

mapStaticValueError
  :: Either GrammarV1ReferenceStaticValueError a
  -> Either GrammarV1ReferenceStaticArgumentClosureError a
mapStaticValueError = mapLeft (failText . show)

mapEffectsError
  :: Either GrammarV1ReferenceEffectsError a
  -> Either GrammarV1ReferenceStaticArgumentClosureError a
mapEffectsError = mapLeft (failText . show)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value

failText :: String -> GrammarV1ReferenceStaticArgumentClosureError
failText = GrammarV1ReferenceStaticArgumentClosureError . Text.pack

failClosure
  :: Text
  -> Either GrammarV1ReferenceStaticArgumentClosureError a
failClosure = Left . GrammarV1ReferenceStaticArgumentClosureError

showText :: Show a => a -> Text
showText = Text.pack . show
