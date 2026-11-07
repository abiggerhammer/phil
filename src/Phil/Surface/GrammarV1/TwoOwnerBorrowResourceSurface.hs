{-# LANGUAGE OverloadedStrings #-}

-- | FSEM-01: one deliberately narrow *single-source* two-linear-owner bridge.
--
-- The Grammar-v1 source contains two distinct Bytes[N] parameters and returns
-- both via a two-element tuple. We independently check each source tuple type
-- element; the general source tuple type elaborator is still unsupported.
-- Production Surface uses an opaque "Tuple[2]" runtime return carrier, so
-- this bridge must NOT be represented as a general TyProduct elaboration.
module Phil.Surface.GrammarV1.TwoOwnerBorrowResourceSurface
  ( GrammarV1TwoOwnerBorrowTrace (..)
  , grammarV1CheckedTwoOwnerBorrowFunction
  , grammarV1CheckedTwoOwnerBorrowFunctionTrace
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
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
  ( InitialBinding (..), SurfaceCheckError, SurfaceCheckResult (..), SurfaceEnvironment (..)
  , emptySurfaceEnvironment
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1ResolvedBinder (..), grammarV1FunctionParameterScope )
import Phil.Surface.GrammarV1.BorrowResourceSurface
  ( GrammarV1BorrowResourceError (..))
import Phil.Surface.GrammarV1.BorrowViewScope
  ( GrammarV1CheckedBorrowView (..), grammarV1CheckedBorrowViewInScope )
import Phil.Surface.GrammarV1.CheckedType (grammarV1CheckedTypeMode)
import Phil.Surface.GrammarV1.LetPatternScope (GrammarV1CheckedLetScopeStep (..))
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence (..)
  , grammarV1CheckedLocalValueOccurrenceInScope
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..), GrammarV1Expression (..)
  , GrammarV1FunctionDecl (..), GrammarV1Statement (..)
  , GrammarV1TermParam (..), GrammarV1Type (..) )
import Phil.Surface.Syntax
  ( Block (..), Component (..), Located (..)
  , Statement (..), SurfaceExpression (..) )

data GrammarV1TwoOwnerBorrowTrace = GrammarV1TwoOwnerBorrowTrace
  { twoOwnerPrimaryBinder :: GrammarV1ResolvedBinder
  , twoOwnerSpectatorBinder :: GrammarV1ResolvedBinder
  , twoOwnerViewBinder :: GrammarV1ResolvedBinder
  , twoOwnerCheckpoints :: [BorrowTraceCheckpoint]
  , twoOwnerOutcome :: Either GrammarV1BorrowResourceError SurfaceCheckResult
  } deriving (Eq, Show)

-- | Check the exact same projected production component as the traced API.
grammarV1CheckedTwoOwnerBorrowFunction
  :: StaticContext -> DeclarationKey -> GrammarV1FunctionDecl
  -> Maybe (Either GrammarV1BorrowResourceError SurfaceCheckResult)
grammarV1CheckedTwoOwnerBorrowFunction =
  withTwoOwnerBorrowFunction observe
  where
    observe _ _ _ environment component =
      Just (finishResult (checkSurfaceComponent environment component))

grammarV1CheckedTwoOwnerBorrowFunctionTrace
  :: StaticContext -> DeclarationKey -> GrammarV1FunctionDecl
  -> Maybe (Either GrammarV1BorrowResourceError GrammarV1TwoOwnerBorrowTrace)
grammarV1CheckedTwoOwnerBorrowFunctionTrace =
  withTwoOwnerBorrowFunction observe
  where
    observe primary spectator view environment component = do
      run <- traceSurfaceBorrowComponent environment component
      Just $ Right GrammarV1TwoOwnerBorrowTrace
        { twoOwnerPrimaryBinder = primary
        , twoOwnerSpectatorBinder = spectator
        , twoOwnerViewBinder = view
        , twoOwnerCheckpoints = traceCheckpoints run
        , twoOwnerOutcome = finishResult (traceOutcome run)
        }

-- | The general Surface runtime does not yet carry elementwise TyProduct:
-- its tuple runtime type is intentionally an opaque arity marker. This exact
-- test checks both source element types and both resolved return occurrences
-- independently rather than inventing a general source-to-Core product rule.
finishResult
  :: Either SurfaceCheckError SurfaceCheckResult
  -> Either GrammarV1BorrowResourceError SurfaceCheckResult
finishResult outcome = do
  checked <- either
    (Left . GrammarV1BorrowResourceProductionError)
    Right outcome
  if checkedTerminalControls checked == [Return (TyOpaque "Tuple[2]")]
    then Right checked
    else Left (GrammarV1BorrowResourceResultMismatch
      (TyOpaque "Tuple[2]") (checkedTerminalControls checked))

withTwoOwnerBorrowFunction
  :: (GrammarV1ResolvedBinder -> GrammarV1ResolvedBinder
      -> GrammarV1ResolvedBinder -> SurfaceEnvironment
      -> Located Component
      -> Maybe (Either GrammarV1BorrowResourceError result))
  -> StaticContext -> DeclarationKey -> GrammarV1FunctionDecl
  -> Maybe (Either GrammarV1BorrowResourceError result)
withTwoOwnerBorrowFunction observe staticContext declarationKey source
  | not (null (grammarV1FunctionGenericParams source)) = Nothing
  | not (null (grammarV1FunctionRequirements source)) = Nothing
  | otherwise = do
      [Located _ primaryParam, Located _ spectatorParam] <-
        pure (grammarV1FunctionTermParams source)
      Located _ (GrammarV1TupleType [primaryResult, spectatorResult]) <-
        grammarV1FunctionResultType source
      let checkType ty = grammarV1CheckedTypeMode
            staticContext emptySurfaceState ty
      primaryCheck <- checkType
        (locatedValue (grammarV1TermParamType primaryParam))
      spectatorCheck <- checkType
        (locatedValue (grammarV1TermParamType spectatorParam))
      primaryResultCheck <- checkType (locatedValue primaryResult)
      spectatorResultCheck <- checkType (locatedValue spectatorResult)
      case (primaryCheck, spectatorCheck,
            primaryResultCheck, spectatorResultCheck) of
        (Left err, _, _, _) ->
          Just (Left (GrammarV1BorrowResourceFocusingError err))
        (_, Left err, _, _) ->
          Just (Left (GrammarV1BorrowResourceFocusingError err))
        (_, _, Left err, _) ->
          Just (Left (GrammarV1BorrowResourceFocusingError err))
        (_, _, _, Left err) ->
          Just (Left (GrammarV1BorrowResourceFocusingError err))
        (Right (primary, _), Right (spectator, _),
         Right (resultPrimary, _), Right (resultSpectator, _)) -> do
          TyBytes _ <- Just (checkedBindingType primary)
          TyBytes _ <- Just (checkedBindingType spectator)
          if all ((== Linear) . checkedBindingMode)
               [primary, spectator, resultPrimary, resultSpectator]
             && checkedBindingType primary == checkedBindingType resultPrimary
             && checkedBindingType spectator == checkedBindingType resultSpectator
            then sourceBody (checkedBindingType primary)
              (checkedBindingType spectator)
            else Nothing
  where
    sourceBody primaryTy spectatorTy = do
      [Located borrowSpan (GrammarV1ExpressionStatement borrow),
       Located returnSpan (GrammarV1ReturnStatement returned)] <-
        pure (grammarV1BlockStatements
          (locatedValue (grammarV1FunctionBody source)))
      GrammarV1TupleExpression [returnedPrimary, returnedSpectator] <-
        pure (locatedValue returned)
      case grammarV1FunctionParameterScope declarationKey source of
        Left err -> Just (Left (GrammarV1BorrowResourceBinderError err))
        Right ([primary, spectator], scope) -> do
          checkedBorrow <- grammarV1CheckedBorrowViewInScope scope borrow
          case checkedBorrow of
            Left err -> Just (Left (GrammarV1BorrowResourceBorrowError err))
            Right (borrowTrace, finalScope) -> do
              let view = grammarV1CheckedBorrowViewBinder borrowTrace
                  borrowOwner = grammarV1CheckedBorrowOwner borrowTrace
                  exactBinder a b = grammarV1ResolvedBinderKey a ==
                    grammarV1ResolvedBinderKey b
              returnedFirst <- grammarV1CheckedLocalValueOccurrenceInScope
                finalScope returnedPrimary
              returnedSecond <- grammarV1CheckedLocalValueOccurrenceInScope
                finalScope returnedSpectator
              if not
                (exactBinder (grammarV1CheckedLocalValueBinder borrowOwner) primary
                  && exactBinder (grammarV1CheckedLocalValueBinder returnedFirst)
                    primary
                  && exactBinder (grammarV1CheckedLocalValueBinder returnedSecond)
                    spectator
                  && grammarV1ResolvedBinderCoreName primary /=
                     grammarV1ResolvedBinderCoreName spectator)
                then Nothing
                else do
                  steps <- mapM (projectBorrowStep view)
                    (grammarV1CheckedBorrowBodySteps borrowTrace)
                  Located _ (GrammarV1BorrowExpression sourceOwner _ sourceBlock) <-
                    pure (grammarV1CheckedBorrowViewSource borrowTrace)
                  let primaryText = semanticName primary
                      spectatorText = semanticName spectator
                      viewText = semanticName view
                      ownerExpression = Located (locatedSpan sourceOwner)
                        (VariableExpression primaryText)
                      borrowExpression = Located (locatedSpan borrow)
                        (BorrowExpression ownerExpression viewText
                          (Located (locatedSpan sourceBlock) (Block steps)))
                      returnedTuple = Located (locatedSpan returned)
                        (TupleExpression
                          [ Located (locatedSpan returnedPrimary)
                              (VariableExpression primaryText)
                          , Located (locatedSpan returnedSpectator)
                              (VariableExpression spectatorText) ])
                      projected = Located (locatedSpan (grammarV1FunctionBody source)) $
                        Block
                          [ Located borrowSpan
                              (ExpressionStatement borrowExpression)
                          , Located returnSpan (ReturnStatement returnedTuple) ]
                      component = Located
                        (locatedSpan (grammarV1FunctionBody source))
                        (Component
                          { componentName = locatedValue (grammarV1FunctionName source)
                          , componentParameters = []
                          , componentProvides = Nothing
                          , componentBody = projected })
                      environment = (emptySurfaceEnvironment staticContext)
                        { surfaceInitialBindings = Map.fromList
                            [ (primaryText, InitialBinding
                                Linear primaryTy (shapeForType primaryTy))
                            , (spectatorText, InitialBinding
                                Linear spectatorTy (shapeForType spectatorTy)) ]
                        }
                  observe primary spectator view environment component
        Right _ -> Nothing

semanticName :: GrammarV1ResolvedBinder -> Text
semanticName = unName . grammarV1ResolvedBinderCoreName

projectBorrowStep
  :: GrammarV1ResolvedBinder -> GrammarV1CheckedLetScopeStep
  -> Maybe (Located Statement)
projectBorrowStep view
  (GrammarV1CheckedLetOccurrenceStep
    (Located span' (GrammarV1ExpressionStatement _)) occurrence)
  | grammarV1ResolvedBinderKey
      (grammarV1CheckedLocalValueBinder occurrence) ==
        grammarV1ResolvedBinderKey view =
    Just (Located span' (ExpressionStatement
      (Located (locatedSpan (grammarV1CheckedLocalValueSource occurrence))
        (VariableExpression (semanticName view)))))
projectBorrowStep _
  (GrammarV1CheckedLetUnitStep
    (Located span' (GrammarV1ExpressionStatement expression)))
  | GrammarV1UnitExpression <- locatedValue expression =
    Just (Located span' (ExpressionStatement
      (Located (locatedSpan expression) UnitExpression)))
projectBorrowStep _ _ = Nothing
