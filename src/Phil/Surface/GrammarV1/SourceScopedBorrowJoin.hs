{-# LANGUAGE OverloadedStrings #-}

-- | Bounded FSEM-01: source-resolved borrow expressions inside both branches
-- of a two-arm if with an empty join-state telescope. No generic source
-- operational semantics or universal implementation refinement is claimed.
module Phil.Surface.GrammarV1.SourceScopedBorrowJoin
  ( GrammarV1ScopedBorrowJoinError (..)
  , GrammarV1ScopedBorrowJoinTrace (..)
  , grammarV1CheckedScopedBorrowJoinTrace
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Static (DeclarationKey, StaticContext)
import Phil.Core.Syntax (Mode (..), Name (..), Ty (..))
import Phil.Surface.Check.Engine
  ( SourceBranchBorrowObservation (..), SourceScopedIfJoinRun (..)
  , checkSurfaceScopedSourceIfJoinComponent
  , traceSurfaceScopedSourceIfJoinComponent
  , traceSurfaceSourceBranchBorrow )
import Phil.Surface.Check.Support (emptySurfaceState, shapeForType)
import Phil.Surface.Check.Types
  ( InitialBinding (..), SurfaceCheckError, SurfaceCheckResult
  , SurfaceEnvironment (..), emptySurfaceEnvironment )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderScopeError
  , GrammarV1ResolvedBinder (..)
  , grammarV1EnterLexicalScope, grammarV1LeaveLexicalScope
  , grammarV1FunctionParameterScope )
import Phil.Surface.GrammarV1.BorrowViewScope
  ( GrammarV1BorrowViewScopeError, GrammarV1CheckedBorrowView (..)
  , grammarV1CheckedBorrowViewInScope )
import Phil.Surface.GrammarV1.CheckedType (grammarV1CheckedTypeMode)
import Phil.Surface.GrammarV1.LetPatternScope
  ( GrammarV1CheckedLetScopeStep (..) )
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence (..)
  , grammarV1CheckedLocalValueOccurrenceInScope )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..), GrammarV1Expression (..)
  , GrammarV1FunctionDecl (..), GrammarV1JoinClause (..)
  , GrammarV1Pattern (..), GrammarV1Statement (..)
  , GrammarV1TermParam (..) )
import Phil.Surface.Syntax
  ( Block (..), Component (..), Located (..), Pattern (..)
  , Statement (..), SurfaceExpression (..) )

data GrammarV1ScopedBorrowJoinError
  = ScopedBorrowJoinBinderError GrammarV1BinderScopeError
  | ScopedBorrowJoinBorrowError GrammarV1BorrowViewScopeError
  deriving (Eq, Show)

data GrammarV1ScopedBorrowJoinTrace = GrammarV1ScopedBorrowJoinTrace
  { scopedBorrowJoinFlagBinder :: GrammarV1ResolvedBinder
  , scopedBorrowJoinPayloadBinder :: GrammarV1ResolvedBinder
  , scopedBorrowJoinThenView :: Maybe GrammarV1ResolvedBinder
  , scopedBorrowJoinElseView :: Maybe GrammarV1ResolvedBinder
  , scopedBorrowJoinBodyLocals :: [GrammarV1ResolvedBinder]
  , scopedBorrowJoinRun :: SourceScopedIfJoinRun
  , scopedBorrowJoinThenLoan :: Maybe SourceBranchBorrowObservation
  , scopedBorrowJoinElseLoan :: Maybe SourceBranchBorrowObservation
  , scopedBorrowJoinOutcome :: Either SurfaceCheckError SurfaceCheckResult
  } deriving (Eq, Show)

-- | Admits exactly fn(flag:Bool,payload:Bytes[N])->Bytes[N] with one
-- if flag join state () { unit | borrow } else { unit | borrow }, followed
-- by return payload. Both alternatives are checked, not dynamically chosen.
grammarV1CheckedScopedBorrowJoinTrace
  :: StaticContext -> DeclarationKey -> GrammarV1FunctionDecl
  -> Maybe
       (Either GrammarV1ScopedBorrowJoinError GrammarV1ScopedBorrowJoinTrace)
grammarV1CheckedScopedBorrowJoinTrace staticContext fnKey functionDecl
  | grammarV1FunctionRecursive functionDecl = Nothing
  | not (null (grammarV1FunctionGenericParams functionDecl)) = Nothing
  | not (null (grammarV1FunctionRequirements functionDecl)) = Nothing
  | otherwise = do
      [Located _ flagParam, Located _ payloadParam] <-
        pure (grammarV1FunctionTermParams functionDecl)
      declaredResult <- grammarV1FunctionResultType functionDecl
      flagMode <- grammarV1CheckedTypeMode staticContext emptySurfaceState
        (locatedValue (grammarV1TermParamType flagParam))
      payloadMode <- grammarV1CheckedTypeMode staticContext emptySurfaceState
        (locatedValue (grammarV1TermParamType payloadParam))
      resultMode <- grammarV1CheckedTypeMode staticContext emptySurfaceState
        (locatedValue declaredResult)
      case (flagMode, payloadMode, resultMode) of
        ( Right (CheckedTypeMode TyBool Unrestricted, _)
          , Right (CheckedTypeMode payloadTy Linear, _)
          , Right (CheckedTypeMode resultTy Linear, _))
            | TyBytes _ <- payloadTy, resultTy == payloadTy ->
                checkedSourceBody payloadTy
        _ -> Nothing
  where
    checkedSourceBody payloadTy = do
      [ Located _ (GrammarV1ExpressionStatement sourceIf)
        , Located resultSpan (GrammarV1ReturnStatement sourceResult) ] <-
        pure (grammarV1BlockStatements
          (locatedValue (grammarV1FunctionBody functionDecl)))
      GrammarV1IfExpression condition (Just joinSource) leftSource
          (Just rightSource) <- pure (locatedValue sourceIf)
      let clause = locatedValue joinSource
      if not (null (grammarV1JoinState clause)) ||
         grammarV1JoinInvariant clause /= Nothing
        then Nothing
        else case grammarV1FunctionParameterScope fnKey functionDecl of
          Left err -> Just (Left (ScopedBorrowJoinBinderError err))
          Right ([flagBinder, payloadBinder], sourceScope) -> do
            checkedCondition <- grammarV1CheckedLocalValueOccurrenceInScope
              sourceScope condition
            _ <- if same (grammarV1CheckedLocalValueBinder checkedCondition)
                     flagBinder then Just () else Nothing
            leftResult <- checkedBranch [flagBinder,payloadBinder]
              sourceScope leftSource
            case leftResult of
              Left err -> Just (Left err)
              Right (leftBlock,leftView,leftLocals,afterLeft) -> do
                rightResult <- checkedBranch [flagBinder,payloadBinder]
                  afterLeft rightSource
                case rightResult of
                  Left err -> Just (Left err)
                  Right (rightBlock,rightView,rightLocals,afterRight) -> do
                    checkedReturn <- grammarV1CheckedLocalValueOccurrenceInScope
                      afterRight sourceResult
                    _ <- if same
                       (grammarV1CheckedLocalValueBinder checkedReturn)
                       payloadBinder then Just () else Nothing
                    let flagName = semanticName flagBinder
                        payloadName = semanticName payloadBinder
                        component = Located
                          (locatedSpan (grammarV1FunctionBody functionDecl))
                          (Component
                            { componentName =
                                locatedValue (grammarV1FunctionName functionDecl)
                            , componentParameters = []
                            , componentProvides = Nothing
                            , componentBody = Located
                                (locatedSpan (grammarV1FunctionBody functionDecl))
                                (Block [])
                            })
                        env = (emptySurfaceEnvironment staticContext)
                          { surfaceInitialBindings = Map.fromList
                              [ (flagName, InitialBinding Unrestricted TyBool
                                  (shapeForType TyBool))
                              , (payloadName, InitialBinding Linear payloadTy
                                  (shapeForType payloadTy))
                              ]
                          }
                        returned = Located resultSpan (ReturnStatement
                          (Located (locatedSpan sourceResult)
                            (VariableExpression payloadName)))
                        checked = traceSurfaceScopedSourceIfJoinComponent
                          env component leftBlock rightBlock [returned]
                        ordinary = checkSurfaceScopedSourceIfJoinComponent
                          env component leftBlock rightBlock [returned]
                        leftLoan = traceSurfaceSourceBranchBorrow
                          env component leftBlock
                        rightLoan =
                          if null (scopedIfJoinThenPruned checked)
                            then Nothing
                            else traceSurfaceSourceBranchBorrow
                              env component rightBlock
                        matchesResult observation =
                          case sourceBranchBorrowOutcome observation of
                            Left err -> scopedIfJoinOutcome checked == Left err
                            Right () -> True
                    if scopedIfJoinOutcome checked /= ordinary ||
                       not (maybe True matchesResult leftLoan) ||
                       not (maybe True matchesResult rightLoan)
                      then Nothing
                      else Just (Right GrammarV1ScopedBorrowJoinTrace
                        { scopedBorrowJoinFlagBinder = flagBinder
                        , scopedBorrowJoinPayloadBinder = payloadBinder
                        , scopedBorrowJoinThenView = leftView
                        , scopedBorrowJoinElseView = rightView
                        , scopedBorrowJoinBodyLocals = leftLocals ++ rightLocals
                        , scopedBorrowJoinRun = checked
                        , scopedBorrowJoinThenLoan = leftLoan
                        , scopedBorrowJoinElseLoan = rightLoan
                        , scopedBorrowJoinOutcome = ordinary
                        })
          Right _ -> Nothing

    -- A branch is a lexical child frame, and the borrow view/body occupy
    -- a nested child frame. Leaving each frame advances, never rolls back,
    -- the declaration-wide ordinal for the next sibling.
    checkedBranch parameters scope source =
      case grammarV1BlockStatements (locatedValue source) of
        [Located statementSpan (GrammarV1ExpressionStatement expr)] ->
          case locatedValue expr of
            GrammarV1UnitExpression ->
              case grammarV1LeaveLexicalScope
                   (grammarV1EnterLexicalScope scope) of
                Left err -> Just (Left (ScopedBorrowJoinBinderError err))
                Right next -> Just (Right
                  ( Located (locatedSpan source) (Block
                      [Located statementSpan (ExpressionStatement
                        (Located (locatedSpan expr) UnitExpression))])
                  , Nothing, [], next ))
            GrammarV1BorrowExpression _ _ _ -> do
              result <- grammarV1CheckedBorrowViewInScope
                (grammarV1EnterLexicalScope scope) expr
              case result of
                Left err -> Just (Left (ScopedBorrowJoinBorrowError err))
                Right (trace, afterLoanScope) ->
                  case grammarV1LeaveLexicalScope afterLoanScope of
                    Left err -> Just (Left (ScopedBorrowJoinBinderError err))
                    Right next -> do
                      let owner = grammarV1CheckedBorrowOwner trace
                          viewBinder = grammarV1CheckedBorrowViewBinder trace
                      sourceOwner <- findBinder parameters
                        (grammarV1CheckedLocalValueBinder owner)
                      projected <- bridgeBorrowBody
                        (viewBinder : parameters)
                        (grammarV1CheckedBorrowBodySteps trace)
                      Located _ (GrammarV1BorrowExpression originalOwner _ body) <-
                        pure (grammarV1CheckedBorrowViewSource trace)
                      let borrow = Located (locatedSpan expr)
                            (BorrowExpression
                              (Located (locatedSpan originalOwner)
                                (VariableExpression (semanticName sourceOwner)))
                              (semanticName viewBinder)
                              (Located (locatedSpan body) (Block projected)))
                          synthetic = Located (locatedSpan source)
                            (Block [Located statementSpan
                              (ExpressionStatement borrow)])
                      Just (Right (synthetic, Just viewBinder,
                        newBinders (grammarV1CheckedBorrowBodySteps trace),
                        next))
            _ -> Nothing
        _ -> Nothing

    newBinders steps =
      concat [ names
        | GrammarV1CheckedLetBindingStep _ _ names <- steps ]

    -- Every source occurrence is resolved by the actual Grammar-v1
    -- LetPatternScope first. The projection only substitutes its exact
    -- semantic Core Name. View aliases retain the underlying borrowed
    -- shape so the real checker detects indirect escapes.
    bridgeBorrowBody _ [] = Just []
    bridgeBorrowBody available (step : rest) =
      case step of
        GrammarV1CheckedLetUnitStep
          (Located span' (GrammarV1ExpressionStatement expression))
            | GrammarV1UnitExpression <- locatedValue expression -> do
                later <- bridgeBorrowBody available rest
                Just (Located span' (ExpressionStatement
                  (Located (locatedSpan expression) UnitExpression)) : later)
        GrammarV1CheckedLetOccurrenceStep
          (Located span' (GrammarV1ExpressionStatement _)) occurrence -> do
            binder <- findBinder available
              (grammarV1CheckedLocalValueBinder occurrence)
            later <- bridgeBorrowBody available rest
            Just (Located span' (ExpressionStatement (Located
              (locatedSpan (grammarV1CheckedLocalValueSource occurrence))
              (VariableExpression (semanticName binder)))) : later)
        GrammarV1CheckedLetOccurrenceStep
          (Located span' (GrammarV1ReturnStatement _)) occurrence -> do
            binder <- findBinder available
              (grammarV1CheckedLocalValueBinder occurrence)
            later <- bridgeBorrowBody available rest
            Just (Located span' (ReturnStatement (Located
              (locatedSpan (grammarV1CheckedLocalValueSource occurrence))
              (VariableExpression (semanticName binder)))) : later)
        GrammarV1CheckedLetBindingStep
          (Located span' (GrammarV1LetStatement pattern' initializer))
          occurrence [binder] -> do
            GrammarV1IdentifierPattern _ <- pure (locatedValue pattern')
            original <- findBinder available
              (grammarV1CheckedLocalValueBinder occurrence)
            later <- bridgeBorrowBody (binder : available) rest
            Just (Located span' (LetStatement
              (Located (locatedSpan pattern')
                (BindPattern (semanticName binder)))
              (Located (locatedSpan initializer)
                (VariableExpression (semanticName original)))) : later)
        _ -> Nothing

    findBinder available target =
      case filter (same target) available of
        [binder] -> Just binder
        _ -> Nothing

    semanticName :: GrammarV1ResolvedBinder -> Text
    semanticName = unName . grammarV1ResolvedBinderCoreName

    same a b = grammarV1ResolvedBinderKey a ==
      grammarV1ResolvedBinderKey b
