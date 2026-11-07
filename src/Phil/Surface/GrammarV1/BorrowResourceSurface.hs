{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.BorrowResourceSurface
  ( GrammarV1BorrowResourceError (..)
  , GrammarV1BorrowResourceTrace (..)
  , grammarV1CheckedBorrowResourceFunction
  , grammarV1CheckedBorrowResourceFunctionTrace
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Focusing (FocusingError)
import Phil.Core.Static (DeclarationKey, StaticContext)
import Phil.Core.Syntax (Control (..), Mode (..), Name (..), Ty (..))
import Phil.Surface.Check.Engine
  ( BorrowTraceCheckpoint
  , BorrowTraceRun (..)
  , checkSurfaceComponent
  , traceSurfaceBorrowComponent
  )
import Phil.Surface.Check.Support (emptySurfaceState, shapeForType)
import Phil.Surface.Check.Types
  ( InitialBinding (..)
  , SurfaceCheckError
  , SurfaceCheckResult (..)
  , SurfaceEnvironment (..)
  , emptySurfaceEnvironment
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderScopeError
  , GrammarV1ResolvedBinder (..)
  , grammarV1FunctionParameterScope
  )
import Phil.Surface.GrammarV1.BorrowViewScope
  ( GrammarV1BorrowViewScopeError
  , GrammarV1CheckedBorrowView (..)
  , grammarV1CheckedBorrowViewInScope
  )
import Phil.Surface.GrammarV1.CheckedType
  ( grammarV1CheckedTypeMode
  )
import Phil.Surface.GrammarV1.LetPatternScope
  ( GrammarV1CheckedLetScopeStep (..)
  )
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence (..)
  , grammarV1CheckedLocalValueOccurrenceInScope
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..)
  , GrammarV1Expression (..)
  , GrammarV1FunctionDecl (..)
  , GrammarV1Statement (..)
  , GrammarV1TermParam (..)
  )
import Phil.Surface.Syntax
  ( Block (..)
  , Component (..)
  , Located (..)
  , Statement (..)
  , SurfaceExpression (..)
  )

-- | One restricted source-to-production-checker bridge. Every missing
-- competence case returns Nothing rather than being reinterpreted as a
-- successful typing judgment or a guessed global/static reference.
data GrammarV1BorrowResourceError
  = GrammarV1BorrowResourceBinderError GrammarV1BinderScopeError
  | GrammarV1BorrowResourceBorrowError GrammarV1BorrowViewScopeError
  | GrammarV1BorrowResourceFocusingError FocusingError
  | GrammarV1BorrowResourceProductionError SurfaceCheckError
  | GrammarV1BorrowResourceResultMismatch Ty [Control]
  deriving (Eq, Show)

-- | Identity-bearing, production-derived observer result. The checker
-- outcome stays inside this record so a rejected escaping view retains its
-- pre-rejection checkpoints. Early scope/type errors have no production trace
-- and remain in the outer Either; unsupported source is Nothing.
data GrammarV1BorrowResourceTrace = GrammarV1BorrowResourceTrace
  { grammarV1TraceOwnerBinder :: GrammarV1ResolvedBinder
  , grammarV1TraceViewBinder :: GrammarV1ResolvedBinder
  , grammarV1TraceCheckpoints :: [BorrowTraceCheckpoint]
  , grammarV1TraceOutcome :: Either GrammarV1BorrowResourceError SurfaceCheckResult
  }
  deriving (Eq, Show)

-- | Existing accepted/rejected checker API. Both this API and the observation
-- API below use precisely the same bounded source projection and checker code.
grammarV1CheckedBorrowResourceFunction
  :: StaticContext
  -> DeclarationKey
  -> GrammarV1FunctionDecl
  -> Maybe (Either GrammarV1BorrowResourceError SurfaceCheckResult)
grammarV1CheckedBorrowResourceFunction =
  grammarV1WithBorrowResourceFunction observe
  where
    observe ty _ _ environment component =
      Just (finalizeProductionOutcome ty
        (checkSurfaceComponent environment component))

-- | Observe the actual production evaluator for the same admitted source
-- fragment. This is neither a general source function checker nor a Rocq
-- simulation proof.
grammarV1CheckedBorrowResourceFunctionTrace
  :: StaticContext
  -> DeclarationKey
  -> GrammarV1FunctionDecl
  -> Maybe (Either GrammarV1BorrowResourceError GrammarV1BorrowResourceTrace)
grammarV1CheckedBorrowResourceFunctionTrace =
  grammarV1WithBorrowResourceFunction observe
  where
    observe ty owner view environment component = do
      observed <- traceSurfaceBorrowComponent environment component
      Just $ Right GrammarV1BorrowResourceTrace
        { grammarV1TraceOwnerBinder = owner
        , grammarV1TraceViewBinder = view
        , grammarV1TraceCheckpoints = traceCheckpoints observed
        , grammarV1TraceOutcome =
            finalizeProductionOutcome ty (traceOutcome observed)
        }

finalizeProductionOutcome
  :: Ty
  -> Either SurfaceCheckError SurfaceCheckResult
  -> Either GrammarV1BorrowResourceError SurfaceCheckResult
finalizeProductionOutcome ty outcome = do
  checked <- mapLeft GrammarV1BorrowResourceProductionError outcome
  if checkedTerminalControls checked == [Return ty]
    then Right checked
    else Left (GrammarV1BorrowResourceResultMismatch ty
      (checkedTerminalControls checked))

-- | Check a deliberately small parameter-bearing Grammar-v1 function body
-- through the existing production surface checker and its *real* shared-loan
-- resource state:
--
--     fn f(owner : Bytes[N]) -> Bytes[N] satisfies C {
--       borrow owner as view { [view;]* [unit;]? };
--       return owner;
--     }
--
-- Both types are independently checked for their intrinsic Linear mode; the
-- generated Core Name for the parameter/view comes from the lexical binder
-- authority. No source spelling is installed into the production checker as
-- an owner identity. Unsupported declarations, body shapes, expressions,
-- unchecked named modes or static references remain non-competence (Nothing).
--
-- This validates the bounded body, *not* the 'satisfies C' contract, complete
-- general source type checking, or a Source -> Core preservation theorem.
grammarV1WithBorrowResourceFunction
  :: (Ty
      -> GrammarV1ResolvedBinder
      -> GrammarV1ResolvedBinder
      -> SurfaceEnvironment
      -> Located Component
      -> Maybe (Either GrammarV1BorrowResourceError result))
  -> StaticContext
  -> DeclarationKey
  -> GrammarV1FunctionDecl
  -> Maybe (Either GrammarV1BorrowResourceError result)
grammarV1WithBorrowResourceFunction observe staticContext declarationKey source
  | not (null (grammarV1FunctionGenericParams source)) = Nothing
  | not (null (grammarV1FunctionRequirements source)) = Nothing
  | otherwise = do
      [Located _ parameter] <- pure (grammarV1FunctionTermParams source)
      resultSource <- grammarV1FunctionResultType source
      let parameterTypeSource = locatedValue (grammarV1TermParamType parameter)
      checkedParameter <- grammarV1CheckedTypeMode
        staticContext emptySurfaceState parameterTypeSource
      checkedResult <- grammarV1CheckedTypeMode
        staticContext emptySurfaceState (locatedValue resultSource)
      case (checkedParameter, checkedResult) of
        (Left errorValue, _) ->
          Just (Left (GrammarV1BorrowResourceFocusingError errorValue))
        (_, Left errorValue) ->
          Just (Left (GrammarV1BorrowResourceFocusingError errorValue))
        (Right (param, _), Right (result, _))
          -> do
              paramTy@(TyBytes _) <- Just (checkedBindingType param)
              (TyBytes _) <- Just (checkedBindingType result)
              if checkedBindingMode param /= Linear
                || checkedBindingMode result /= Linear
                || checkedBindingType result /= paramTy
                then Nothing
                else checkBody paramTy
  where
    checkBody ty = do
      [Located borrowSpan (GrammarV1ExpressionStatement borrow),
       Located returnSpan (GrammarV1ReturnStatement returned)] <-
        pure (grammarV1BlockStatements
          (locatedValue (grammarV1FunctionBody source)))
      case grammarV1FunctionParameterScope declarationKey source of
        Left err -> Just (Left (GrammarV1BorrowResourceBinderError err))
        Right ([parameterBinder], scope) -> do
          checkedBorrow <- grammarV1CheckedBorrowViewInScope scope borrow
          case checkedBorrow of
            Left err -> Just (Left (GrammarV1BorrowResourceBorrowError err))
            Right (borrowTrace, nextScope) -> do
              let owner = grammarV1CheckedBorrowOwner borrowTrace
                  viewBinder = grammarV1CheckedBorrowViewBinder borrowTrace
              -- Verify both lexical occurrences against their *exact* binder
              -- identities. Any global fallback, shadow, or alias is unsupported.
              if grammarV1ResolvedBinderKey
                  (grammarV1CheckedLocalValueBinder owner)
                    /= grammarV1ResolvedBinderKey parameterBinder
                then Nothing
                else do
                  returnOccurrence <-
                    grammarV1CheckedLocalValueOccurrenceInScope nextScope returned
                  if grammarV1ResolvedBinderKey
                       (grammarV1CheckedLocalValueBinder returnOccurrence)
                       /= grammarV1ResolvedBinderKey parameterBinder
                    then Nothing
                    else do
                      let viewText = semanticName viewBinder
                          ownerText = semanticName parameterBinder
                      bodyStatements <- mapM (bridgeStep viewBinder)
                        (grammarV1CheckedBorrowBodySteps borrowTrace)
                      (Located _ (GrammarV1BorrowExpression sourceOwner _ sourceBlock)) <-
                        pure (grammarV1CheckedBorrowViewSource borrowTrace)
                      let ownerSurface = Located (locatedSpan sourceOwner)
                            (VariableExpression ownerText)
                          borrowSurface = Located (locatedSpan borrow)
                            (BorrowExpression ownerSurface viewText
                              (Located (locatedSpan sourceBlock)
                                (Block bodyStatements)))
                          projected = Located (locatedSpan (grammarV1FunctionBody source)) $
                            Block
                              [ Located borrowSpan (ExpressionStatement borrowSurface)
                              , Located returnSpan
                                  (ReturnStatement (Located (locatedSpan returned)
                                    (VariableExpression ownerText)))
                              ]
                          synthetic = Located
                            (locatedSpan (grammarV1FunctionBody source))
                            (Component
                              { componentName = locatedValue (grammarV1FunctionName source)
                              , componentParameters = []
                              , componentProvides = Nothing
                              , componentBody = projected
                              })
                          environment = (emptySurfaceEnvironment staticContext)
                            { surfaceInitialBindings = Map.singleton ownerText
                                (InitialBinding Linear ty (shapeForType ty))
                            }
                      observe ty parameterBinder viewBinder environment synthetic
        Right _ -> Nothing

semanticName :: GrammarV1ResolvedBinder -> Text
semanticName = unName . grammarV1ResolvedBinderCoreName

-- Only an exactly resolved view occurrence or an explicit Unit expression
-- may enter this fragment. Checking borrow owner use/move while loaned and
-- escaping returned runtime values is the production checker's job.
bridgeStep
  :: GrammarV1ResolvedBinder
  -> GrammarV1CheckedLetScopeStep
  -> Maybe (Located Statement)
bridgeStep view (GrammarV1CheckedLetOccurrenceStep
  (Located span' (GrammarV1ExpressionStatement _)) occurrence)
    | sameBinder (grammarV1CheckedLocalValueBinder occurrence) view =
        Just (Located span' (ExpressionStatement
          (Located (locatedSpan (grammarV1CheckedLocalValueSource occurrence))
            (VariableExpression (semanticName view)))))
bridgeStep _ (GrammarV1CheckedLetUnitStep
  (Located span' (GrammarV1ExpressionStatement source)))
    | GrammarV1UnitExpression <- locatedValue source =
        Just (Located span' (ExpressionStatement
          (Located (locatedSpan source) UnitExpression)))
bridgeStep _ _ = Nothing

sameBinder :: GrammarV1ResolvedBinder -> GrammarV1ResolvedBinder -> Bool
sameBinder left right =
  grammarV1ResolvedBinderKey left == grammarV1ResolvedBinderKey right

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
