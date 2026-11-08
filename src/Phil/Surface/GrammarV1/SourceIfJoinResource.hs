{-# LANGUAGE OverloadedStrings #-}

-- | FSEM-01 J-1/J-2: one genuinely parsed if-with-join function, whose
-- source-resolved predecessor blocks are executed by the ordinary production
-- Surface checker and Core.joinContinuing, not in an abstract test harness.
-- This is a bounded fragment, not a general if/CFG elaborator.
module Phil.Surface.GrammarV1.SourceIfJoinResource
  ( GrammarV1SourceIfJoinError (..)
  , GrammarV1SourceIfJoinTrace (..)
  , grammarV1CheckedSourceIfJoinTrace
  ) where

import qualified Data.Map.Strict as Map
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Static (DeclarationKey, StaticContext)
import Phil.Core.Syntax (Mode (..), Name (..), Ty (..))
import Phil.Surface.Check.Engine
  ( SourceIfJoinRun (..), checkSurfaceSourceIfJoinComponent
  , traceSurfaceSourceIfJoinComponent )
import Phil.Surface.Check.Support (emptySurfaceState, shapeForType)
import Phil.Surface.Check.Types
  ( InitialBinding (..), SurfaceCheckError, SurfaceCheckResult
  , SurfaceEnvironment (..), emptySurfaceEnvironment )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderScopeError, GrammarV1ResolvedBinder (..)
  , grammarV1FunctionParameterScope )
import Phil.Surface.GrammarV1.CheckedType (grammarV1CheckedTypeMode)
import Phil.Surface.GrammarV1.JoinStateScope
  ( GrammarV1CheckedIfBranch (..)
  , GrammarV1CheckedJoinClause (..)
  , GrammarV1CheckedJoinExpression (..)
  , GrammarV1JoinStateScopeError
  , grammarV1CheckedJoinExpressionInScope )
import Phil.Surface.GrammarV1.LetPatternScope (GrammarV1CheckedLetScopeStep (..))
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence (..)
  , grammarV1CheckedLocalValueOccurrenceInScope )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..), GrammarV1Expression (..)
  , GrammarV1FunctionDecl (..), GrammarV1Pattern (..)
  , GrammarV1Statement (..), GrammarV1TermParam (..) )
import Phil.Surface.Syntax
  ( Block (..), Component (..), Located (..), Pattern (..)
  , Statement (..), SurfaceExpression (..) )

data GrammarV1SourceIfJoinError
  = SourceIfJoinBinderError GrammarV1BinderScopeError
  | SourceIfJoinScopeError GrammarV1JoinStateScopeError
  deriving (Eq, Show)

-- | No predecessor is fabricated on failure: the production trace records
-- only contexts actually returned by each checked branch.
data GrammarV1SourceIfJoinTrace = GrammarV1SourceIfJoinTrace
  { sourceIfJoinFlagBinder :: GrammarV1ResolvedBinder
  , sourceIfJoinPayloadBinder :: GrammarV1ResolvedBinder
  , sourceIfJoinBranchBinders :: [GrammarV1ResolvedBinder]
  , sourceIfJoinBranchRun :: SourceIfJoinRun
  , sourceIfJoinCheckedOutcome :: Either SurfaceCheckError SurfaceCheckResult
  } deriving (Eq, Show)

-- | Exact supported fragment: nonrecursive fn(flag:Bool,payload:Bytes[N])
-- -> Bytes[N], one if flag join state () { unit | let moved = payload |
-- return payload } else { ... }, then return payload. Real source scope
-- checks and exact source-generated binder IDs precede projection.
--
-- Both predecessors are statically evaluated; a Boolean condition does NOT
-- select one branch in the type checker. A terminal Return predecessor is
-- retained but excluded from the ordinary continuing Core join.
grammarV1CheckedSourceIfJoinTrace
  :: StaticContext
  -> DeclarationKey
  -> GrammarV1FunctionDecl
  -> Maybe (Either GrammarV1SourceIfJoinError GrammarV1SourceIfJoinTrace)
grammarV1CheckedSourceIfJoinTrace staticContext fnKey functionDecl
  | grammarV1FunctionRecursive functionDecl = Nothing
  | not (null (grammarV1FunctionGenericParams functionDecl)) = Nothing
  | not (null (grammarV1FunctionRequirements functionDecl)) = Nothing
  | otherwise = do
      [Located _ flagParam, Located _ payloadParam] <-
        pure (grammarV1FunctionTermParams functionDecl)
      expectedReturn <- grammarV1FunctionResultType functionDecl
      flagChecked <- grammarV1CheckedTypeMode staticContext emptySurfaceState
        (locatedValue (grammarV1TermParamType flagParam))
      payloadChecked <- grammarV1CheckedTypeMode staticContext emptySurfaceState
        (locatedValue (grammarV1TermParamType payloadParam))
      returnChecked <- grammarV1CheckedTypeMode staticContext emptySurfaceState
        (locatedValue expectedReturn)
      case (flagChecked, payloadChecked, returnChecked) of
        (Right (CheckedTypeMode TyBool Unrestricted, _),
         Right (CheckedTypeMode payloadType Linear, _),
         Right (CheckedTypeMode resultType Linear, _))
           | TyBytes _ <- payloadType
           , payloadType == resultType -> checkedSourceBody payloadType
        _ -> Nothing
  where
    checkedSourceBody payloadType = do
      [Located _ (GrammarV1ExpressionStatement ifSource),
       Located returnSpan (GrammarV1ReturnStatement returned)] <-
        pure (grammarV1BlockStatements
          (locatedValue (grammarV1FunctionBody functionDecl)))
      GrammarV1IfExpression _ (Just joinSource) _ (Just _) <-
        pure (locatedValue ifSource)
      let joinClause = locatedValue joinSource
      if not (null (grammarV1JoinState joinClause)) ||
         grammarV1JoinInvariant joinClause /= Nothing
        then Nothing
        else case grammarV1FunctionParameterScope fnKey functionDecl of
          Left err -> Just (Left (SourceIfJoinBinderError err))
          Right ([flagBinder,payloadBinder],initialScope) -> do
            checkedJoin <- grammarV1CheckedJoinExpressionInScope
              initialScope ifSource
            case checkedJoin of
              Left err -> Just (Left (SourceIfJoinScopeError err))
              Right (GrammarV1CheckedIfJoinExpression condition left
                     (Just right) checkedClause, afterJoinScope) -> do
                let same x y = grammarV1ResolvedBinderKey x ==
                      grammarV1ResolvedBinderKey y
                if not (same
                     (grammarV1CheckedLocalValueBinder condition) flagBinder)
                     || not (null (grammarV1CheckedJoinSlots checkedClause))
                  then Nothing
                  else do
                    resultOccurrence <- grammarV1CheckedLocalValueOccurrenceInScope
                      afterJoinScope returned
                    if not (same
                        (grammarV1CheckedLocalValueBinder resultOccurrence)
                        payloadBinder)
                      then Nothing
                      else do
                        (leftBody,leftNames) <- projectBranch payloadBinder left
                        (rightBody,rightNames) <- projectBranch payloadBinder right
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
                            environment = (emptySurfaceEnvironment staticContext)
                              { surfaceInitialBindings = Map.fromList
                                  [ (flagName, InitialBinding
                                      Unrestricted TyBool (shapeForType TyBool))
                                  , (payloadName, InitialBinding
                                      Linear payloadType (shapeForType payloadType))
                                  ]
                              }
                            returnStatement = Located returnSpan
                              (ReturnStatement (Located (locatedSpan returned)
                                (VariableExpression payloadName)))
                            traced = traceSurfaceSourceIfJoinComponent
                              environment component leftBody rightBody
                              returnStatement
                            ordinary = checkSurfaceSourceIfJoinComponent
                              environment component leftBody rightBody
                              returnStatement
                        if sourceIfJoinOutcome traced /= ordinary
                          then Nothing
                          else Just (Right GrammarV1SourceIfJoinTrace
                            { sourceIfJoinFlagBinder = flagBinder
                            , sourceIfJoinPayloadBinder = payloadBinder
                            , sourceIfJoinBranchBinders = leftNames ++ rightNames
                            , sourceIfJoinBranchRun = traced
                            , sourceIfJoinCheckedOutcome = ordinary
                            })
              Right _ -> Nothing

    semanticName = unName . grammarV1ResolvedBinderCoreName

    projectBranch payloadBinder branch = do
      [step] <- pure (grammarV1CheckedIfBranchSteps branch)
      let src = grammarV1CheckedIfBranchSource branch
      case step of
        GrammarV1CheckedLetUnitStep
          (Located span' (GrammarV1ExpressionStatement source))
            | GrammarV1UnitExpression <- locatedValue source ->
                Just (Located (locatedSpan src)
                  (Block [Located span' (ExpressionStatement
                    (Located (locatedSpan source) UnitExpression))]), [])
        GrammarV1CheckedLetBindingStep
          (Located span' (GrammarV1LetStatement pattern' initializer))
          occurrence [binder] -> do
            GrammarV1IdentifierPattern _ <- pure (locatedValue pattern')
            if grammarV1ResolvedBinderKey
                (grammarV1CheckedLocalValueBinder occurrence) /=
                 grammarV1ResolvedBinderKey payloadBinder
              then Nothing
              else Just (Located (locatedSpan src) (Block
                [ Located span' (LetStatement
                    (Located (locatedSpan pattern')
                      (BindPattern (semanticName binder)))
                    (Located (locatedSpan initializer)
                      (VariableExpression (semanticName payloadBinder)))) ]),
                [binder])
        GrammarV1CheckedLetOccurrenceStep
          (Located span' (GrammarV1ReturnStatement returned))
          occurrence ->
            if grammarV1ResolvedBinderKey
                (grammarV1CheckedLocalValueBinder occurrence) /=
                 grammarV1ResolvedBinderKey payloadBinder
              then Nothing
              else Just (Located (locatedSpan src) (Block
                [Located span' (ReturnStatement
                  (Located (locatedSpan returned)
                    (VariableExpression (semanticName payloadBinder))))]), [])
        _ -> Nothing
