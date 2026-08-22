{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.Check.Preflight
  ( preflightComponent
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import Phil.Surface.Check.Types
  ( PrimitiveSemantics (..)
  , RejectionClass (..)
  , SurfaceCheckError (..)
  , SurfaceEnvironment (..)
  )
import Phil.Surface.Syntax
  ( Block (..)
  , BranchValue (..)
  , CaseArm (..)
  , CasePattern (..)
  , Component (..)
  , FailureTarget (..)
  , Fallback (..)
  , Located (..)
  , Parameter (..)
  , Pattern (..)
  , Statement (..)
  , SurfaceExpression (..)
  , SurfaceProposition (..)
  )

-- | Cheap source-level checks whose competence precedes Core execution.
--
-- This pass is intentionally narrow.  It does not duplicate resource or
-- session checking; it only rejects syntactically explicit control after an
-- unconditional terminal operation, and gives evidence-consuming primitive
-- calls an evidence-specific diagnostic when their argument is lexically
-- absent.  The Core-backed engine remains authoritative for everything else.
preflightComponent
  :: SurfaceEnvironment
  -> Located Component
  -> Either SurfaceCheckError ()
preflightComponent environment locatedComponent =
  checkBlock initialBindings (componentBody (locatedValue locatedComponent))
  where
    component = locatedValue locatedComponent
    initialBindings =
      Map.keysSet (surfaceInitialBindings environment)
        `Set.union` Set.fromList
          [ parameterName (locatedValue parameter)
          | parameter <- componentParameters component
          ]

    checkBlock bound locatedBlock =
      checkStatements bound (blockStatements (locatedValue locatedBlock))

    checkStatements _ [] = Right ()
    checkStatements bound (statement : rest) = do
      checkStatement bound statement
      let bound' = bound `Set.union` statementBindings (locatedValue statement)
      if statementTerminates (locatedValue statement)
        then case rest of
          [] -> Right ()
          next : _ -> reject next ControlAfterTerminal
            "statement occurs after an unconditional terminal operation"
        else checkStatements bound' rest

    checkStatement bound locatedStatement =
      case locatedValue locatedStatement of
        LetStatement _ expression -> checkExpression bound expression
        ReturnStatement expression -> checkExpression bound expression
        ExpressionStatement expression -> checkExpression bound expression

    checkExpression bound locatedExpression =
      case locatedValue locatedExpression of
        VariableExpression _ -> Right ()
        IntegerExpression _ -> Right ()
        BooleanExpression _ -> Right ()
        UnitExpression -> Right ()
        TupleExpression values -> mapM_ (checkExpression bound) values
        CallExpression name arguments -> do
          case Map.lookup name (surfacePrimitives environment) of
            Just PrimitiveConsumeBeginPolicyEvidence ->
              mapM_ (requireBoundEvidence bound) arguments
            _ -> Right ()
          mapM_ (checkExpression bound) arguments
        FieldExpression base _ -> checkExpression bound base
        BinaryExpression _ left right ->
          checkExpression bound left >> checkExpression bound right
        ConstructExpression _ fields ->
          mapM_ (checkExpression bound . snd) fields
        ReceiveExpression _ endpoint -> checkExpression bound endpoint
        ReceiveFrameExpression endpoint -> checkExpression bound endpoint
        RecognizeExpression _ raw -> checkExpression bound raw
        ValidateExpression _ context subject -> do
          mapM_ (checkExpression bound) context
          checkExpression bound subject
        SendExpression value endpoint ->
          checkExpression bound value >> checkExpression bound endpoint
        SendExactExpression value endpoint ->
          checkExpression bound value >> checkExpression bound endpoint
        ReceiveExactExpression count endpoint evidence -> do
          checkExpression bound count
          checkExpression bound endpoint
          mapM_ (checkExpression bound) evidence
        SelectExpression branch endpoint evidence -> do
          mapM_ (checkExpression bound) (branchValueArguments branch)
          checkExpression bound endpoint
          mapM_ (checkExpression bound) evidence
        CommitReceiveExpression pending evidence ->
          checkExpression bound pending >> checkExpression bound evidence
        BorrowExpression owner view body -> do
          checkExpression bound owner
          checkBlock (Set.insert view bound) body
        DecideExpression scrutinee arms -> do
          checkExpression bound scrutinee
          mapM_ (checkArm bound) arms
        OfferExpression endpoint arms -> do
          checkExpression bound endpoint
          mapM_ (checkArm bound) arms
        FailExpression target resource -> do
          mapM_ (checkExpression bound) (failureTargetArguments target)
          checkExpression bound resource
        CloseExpression target -> checkExpression bound target
        ReleaseExpression owner -> checkExpression bound owner
        AcceptExpression value _ -> checkExpression bound value
        ProveExpression proposition -> checkProposition bound proposition
        FallbackExpression base fallback -> do
          checkExpression bound base
          case fallback of
            FailFallback _ -> Right ()
            RejectFallback expression -> checkExpression bound expression

    checkArm bound locatedArm =
      let arm = locatedValue locatedArm
          pattern' = caseArmPattern arm
          armBound = bound `Set.union` Set.fromList (casePatternBinders pattern')
      in checkBlock armBound (caseArmBody arm)

    checkProposition bound locatedProposition =
      case locatedValue locatedProposition of
        PropositionTrue -> Right ()
        PropositionFalse -> Right ()
        PropositionEqual left right -> pair left right
        PropositionNotEqual left right -> pair left right
        PropositionLessThan left right -> pair left right
        PropositionLessEqual left right -> pair left right
        PropositionGreaterThan left right -> pair left right
        PropositionGreaterEqual left right -> pair left right
        PropositionAtom _ arguments -> mapM_ (checkExpression bound) arguments
        PropositionConjunction left right -> propPair left right
        PropositionDisjunction left right -> propPair left right
        PropositionNegation inner -> checkProposition bound inner
      where
        pair left right = checkExpression bound left >> checkExpression bound right
        propPair left right = checkProposition bound left >> checkProposition bound right

    requireBoundEvidence bound expression =
      case locatedValue expression of
        VariableExpression name
          | Set.notMember name bound -> reject expression MissingEvidence
              ("required evidence binding is not in scope: " <> name)
        _ -> Right ()

statementBindings :: Statement -> Set Text
statementBindings statement =
  case statement of
    LetStatement pattern' _ -> patternBindings (locatedValue pattern')
    ReturnStatement _ -> Set.empty
    ExpressionStatement _ -> Set.empty

patternBindings :: Pattern -> Set Text
patternBindings pattern' =
  case pattern' of
    BindPattern name -> Set.singleton name
    TuplePattern patterns -> Set.unions (map (patternBindings . locatedValue) patterns)

statementTerminates :: Statement -> Bool
statementTerminates statement =
  case statement of
    ReturnStatement _ -> True
    LetStatement _ expression -> expressionTerminates (locatedValue expression)
    ExpressionStatement expression -> expressionTerminates (locatedValue expression)

expressionTerminates :: SurfaceExpression -> Bool
expressionTerminates expression =
  case expression of
    FailExpression _ _ -> True
    CloseExpression _ -> True
    _ -> False

reject :: Located a -> RejectionClass -> Text -> Either SurfaceCheckError b
reject located rejection detail = Left SurfaceCheckError
  { surfaceErrorSpan = locatedSpan located
  , surfaceErrorClass = rejection
  , surfaceErrorDetail = detail
  }
