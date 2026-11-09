{-# LANGUAGE OverloadedStrings #-}

-- | FSEM-01 C-1: bounded source-resolved closure capture ownership.
-- Does NOT implement whole-source callable elaboration or target conversion.
module Phil.Surface.GrammarV1.SourceClosureCapture
  ( SourceClosureError (..)
  , SourceDirectClosureRun (..)
  , SourceBorrowClosureRun (..)
  , grammarV1SourceDirectClosure
  , grammarV1SourceBorrowClosure
  ) where

import Control.Monad (foldM)
import qualified Data.Map.Strict as Map
import qualified Phil.Core.Context as Core
import Phil.Core.Callable
  ( CallableCheckError, CallableOccurrenceKey (..)
  , CaptureOccurrenceKey (..), CaptureTransfer (..)
  , ClosureCapture (..), ClosureCaptureSummary (..), checkClosureCaptures )
import Phil.Core.CallableScope
  ( CallableScopeError, ClosureExtent (..), ClosureScopeCapture (..)
  , LoanScopeKey (..), checkClosureCaptureScope )
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Static (DeclarationKey, StaticContext)
import Phil.Core.Syntax (Mode (..), Name (..), Ty (..))
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKind (GrammarV1BorrowViewBinder)
  , GrammarV1BinderScopeError
  , GrammarV1ResolvedBinder (..), grammarV1BindLocal
  , grammarV1ClosureParameterScope, grammarV1EnterLexicalScope
  , grammarV1FunctionParameterScope, grammarV1ResolveLocal )
import Phil.Surface.GrammarV1.CheckedType (grammarV1CheckedTypeMode)
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence (..)
  , grammarV1CheckedLocalValueOccurrenceInScope )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..), GrammarV1Closure (..)
  , GrammarV1Expression (..), GrammarV1FunctionDecl (..)
  , GrammarV1QualifiedName (..), GrammarV1StaticReference (..)
  , GrammarV1Statement (..), GrammarV1StructuralMode (..)
  , GrammarV1TermParam (..), GrammarV1Type (..) )
import Phil.Surface.Syntax (Located (..))

data SourceClosureError
  = SourceClosureBinderError GrammarV1BinderScopeError
  | SourceClosureCaptureError CallableCheckError
  | SourceClosureCoreError Core.CheckError
  | SourceClosureScopeError CallableScopeError
  | SourceClosureModeMismatch Mode Mode
  | SourceClosureTypeModeMismatch Name Mode Mode
  deriving (Eq, Show)

data SourceDirectClosureRun = SourceDirectClosureRun
  { directParameters :: [GrammarV1ResolvedBinder]
  , directCaptures :: [GrammarV1ResolvedBinder]
  , directInitial :: Core.ResourceContext
  , directSummary :: Maybe ClosureCaptureSummary
  , directFinal :: Maybe Core.ResourceContext
  , directOutcome :: Either SourceClosureError ()
  } deriving (Eq, Show)

data SourceBorrowClosureRun = SourceBorrowClosureRun
  { borrowOwner :: GrammarV1ResolvedBinder
  , borrowView :: GrammarV1ResolvedBinder
  , borrowExtent :: ClosureExtent
  , borrowInitial :: Core.ResourceContext
  , borrowStarted :: Maybe Core.ResourceContext
  , borrowClosed :: Maybe Core.ResourceContext
  , borrowOutcome :: Either SourceClosureError ()
  } deriving (Eq, Show)

-- | Source shape:
-- fn build(flag:Bool,payload:Bytes[8])->OneShot satisfies C {
--   return closure mode linear () satisfies OneShot
--     captures(payload) { unit; };
-- }
-- This certifies capture ownership ONLY; opaque nominal result/callable
-- contract resolution, function terminal typing and invocation are unproved.
grammarV1SourceDirectClosure
  :: StaticContext -> DeclarationKey -> GrammarV1FunctionDecl
  -> Maybe (Either SourceClosureError SourceDirectClosureRun)
grammarV1SourceDirectClosure static key fn = do
  params <- sourceParameters static fn
  resultTy <- grammarV1FunctionResultType fn
  [Located _ (GrammarV1ReturnStatement expression)] <-
    pure (grammarV1BlockStatements (locatedValue (grammarV1FunctionBody fn)))
  GrammarV1ClosureExpression closure <- pure (locatedValue expression)
  if not (sameNominal resultTy (grammarV1ClosureSatisfies closure))
    || not (unitClosure closure) then Nothing else do
      sourceCaptures <- grammarV1ClosureCaptures closure
      if null sourceCaptures then Nothing else
        case grammarV1FunctionParameterScope key fn of
          Left err -> Just (Left (SourceClosureBinderError err))
          Right (binders,outer) -> do
            let typed = zip binders params
            case grammarV1ClosureParameterScope outer closure of
              Left err -> Just (Left (SourceClosureBinderError err))
              Right (inside,scope) | not (null inside) -> Nothing
              Right (_,scope) -> case mapM
                  (\sourceName -> grammarV1ResolveLocal sourceName scope)
                  sourceCaptures of
                Left err -> Just (Left (SourceClosureBinderError err))
                Right resolved
                  | all (hasBinder typed) resolved ->
                      Just (Right (runDirect typed resolved closure))
                  | otherwise -> Nothing

runDirect
  :: [(GrammarV1ResolvedBinder, CheckedTypeMode)]
  -> [GrammarV1ResolvedBinder] -> GrammarV1Closure
  -> SourceDirectClosureRun
runDirect typed resolved closure =
  let initial = contextOf typed
      start = SourceDirectClosureRun
        { directParameters = map fst typed
        , directCaptures = resolved
        , directInitial = initial
        , directSummary = Nothing
        , directFinal = Nothing
        , directOutcome = Right () }
      descriptions = map (makeCapture typed) resolved
  in case sequence descriptions of
    Nothing -> start { directOutcome = Left
      (SourceClosureModeMismatch Unrestricted Linear) }
    Just captures ->
      case checkClosureCaptures captures of
        Left err -> start
          { directOutcome = Left (SourceClosureCaptureError err) }
        Right summary ->
          let observed = start { directSummary = Just summary }
              minimum = closureMinimumStructuralMode summary
          in case sourceMode (grammarV1ClosureMode closure) of
            Just declared | declared /= minimum -> observed
              { directOutcome = Left
                  (SourceClosureModeMismatch minimum declared) }
            _ -> case foldM (consumeCapture typed) initial resolved of
              Left err -> observed { directOutcome = Left err }
              Right final -> observed
                { directFinal = Just final, directOutcome = Right () }

-- | Source shape: borrow payload as view {
--   closure mode unrestricted () satisfies OneShot captures(view) { unit; };
--   unit;
-- };
-- A source-level return of that closure instead of local expression is
-- EscapingClosure and must fail CALL-010. No external extent knob is accepted.
grammarV1SourceBorrowClosure
  :: StaticContext -> DeclarationKey -> GrammarV1FunctionDecl
  -> Maybe (Either SourceClosureError SourceBorrowClosureRun)
grammarV1SourceBorrowClosure static key fn = do
  params <- sourceParameters static fn
  [Located _ (GrammarV1ExpressionStatement borrowed)] <-
    pure (grammarV1BlockStatements (locatedValue (grammarV1FunctionBody fn)))
  GrammarV1BorrowExpression ownerSource viewSource (Located _ body) <-
    pure (locatedValue borrowed)
  (isEscape,closure) <- case grammarV1BlockStatements body of
    [Located _ (GrammarV1ReturnStatement expression)] ->
      fmap ((,) True) (closureExpr expression)
    [Located _ (GrammarV1ExpressionStatement expression),
     Located _ (GrammarV1ExpressionStatement unit)]
      | GrammarV1UnitExpression <- locatedValue unit ->
          fmap ((,) False) (closureExpr expression)
    _ -> Nothing
  captures <- grammarV1ClosureCaptures closure
  if not (unitClosure closure) || length captures /= 1
    then Nothing else
    case grammarV1FunctionParameterScope key fn of
      Left err -> Just (Left (SourceClosureBinderError err))
      Right (binders,outer) -> do
        let typed = zip binders params
        occurrence <- grammarV1CheckedLocalValueOccurrenceInScope outer ownerSource
        let owner = grammarV1CheckedLocalValueBinder occurrence
        if not (sameBinder owner (binders !! 1)) then Nothing
        else case grammarV1BindLocal GrammarV1BorrowViewBinder viewSource
            (grammarV1EnterLexicalScope outer) of
          Left err -> Just (Left (SourceClosureBinderError err))
          Right (view,loanScope) ->
            case grammarV1ClosureParameterScope loanScope closure of
              Left err -> Just (Left (SourceClosureBinderError err))
              Right (inside,scope) | not (null inside) -> Nothing
              Right (_,scope) ->
                case grammarV1ResolveLocal (head captures) scope of
                  Left err -> Just (Left (SourceClosureBinderError err))
                  Right captured | sameBinder view captured ->
                    Just (Right (runBorrow typed owner view isEscape closure))
                  Right _ -> Nothing
  where
    closureExpr (Located _ expr) = case expr of
      GrammarV1ClosureExpression closure -> Just closure
      _ -> Nothing

runBorrow
  :: [(GrammarV1ResolvedBinder, CheckedTypeMode)]
  -> GrammarV1ResolvedBinder -> GrammarV1ResolvedBinder
  -> Bool -> GrammarV1Closure -> SourceBorrowClosureRun
runBorrow typed owner view isEscape closure =
  let initial = contextOf typed
      ownerName = grammarV1ResolvedBinderCoreName owner
      viewName = unName (grammarV1ResolvedBinderCoreName view)
      loanKey = LoanScopeKey ("loan:" <> viewName)
      closureKey = CallableOccurrenceKey ("closure:" <> viewName)
      captureKey = CaptureOccurrenceKey viewName
      extent = if isEscape then EscapingClosure
        else ClosureContainedIn loanKey
      start = SourceBorrowClosureRun
        { borrowOwner = owner, borrowView = view, borrowExtent = extent
        , borrowInitial = initial, borrowStarted = Nothing
        , borrowClosed = Nothing, borrowOutcome = Right () }
  in case Core.startSharedLoan ownerName initial of
    Left err -> start { borrowOutcome = Left (SourceClosureCoreError err) }
    Right loaned ->
      let begun = start { borrowStarted = Just loaned }
          capture = ClosureCapture captureKey CopyCapture Unrestricted
      in case checkClosureCaptures [capture] of
        Left err -> begun
          { borrowOutcome = Left (SourceClosureCaptureError err) }
        Right summary ->
          case sourceMode (grammarV1ClosureMode closure) of
            Just declared
              | declared /= closureMinimumStructuralMode summary ->
                  begun { borrowOutcome = Left
                    (SourceClosureModeMismatch
                      (closureMinimumStructuralMode summary) declared) }
            _ -> case checkClosureCaptureScope closureKey extent
                [ScopedSharedLoanCapture captureKey loanKey] of
              Left err -> begun
                { borrowOutcome = Left (SourceClosureScopeError err) }
              Right () -> case Core.endSharedLoan ownerName loaned of
                Left err -> begun
                  { borrowOutcome = Left (SourceClosureCoreError err) }
                Right closed -> begun
                  { borrowClosed = Just closed, borrowOutcome = Right () }

sourceParameters
  :: StaticContext -> GrammarV1FunctionDecl
  -> Maybe [CheckedTypeMode]
sourceParameters static fn
  | grammarV1FunctionRecursive fn = Nothing
  | not (null (grammarV1FunctionGenericParams fn)) = Nothing
  | not (null (grammarV1FunctionRequirements fn)) = Nothing
  | otherwise = do
      [flag,payload] <- pure (grammarV1FunctionTermParams fn)
      [left,right] <- mapM
        (grammarV1CheckedTypeMode static emptySurfaceState
          . locatedValue . grammarV1TermParamType . locatedValue)
        [flag,payload]
      case (left,right) of
        (Right (a,_),Right (b,_))
          | a == CheckedTypeMode TyBool Unrestricted
          , TyBytes _ <- checkedBindingType b
          , checkedBindingMode b == Linear -> Just [a,b]
        _ -> Nothing

contextOf
  :: [(GrammarV1ResolvedBinder, CheckedTypeMode)] -> Core.ResourceContext
contextOf = foldl insert Core.emptyContext
  where
    insert ctx (binder,checked) =
      let name = grammarV1ResolvedBinderCoreName binder
          ty = checkedBindingType checked
      in case checkedBindingMode checked of
        Unrestricted -> ctx { Core.unrestrictedBindings =
          Map.insert name ty (Core.unrestrictedBindings ctx) }
        Affine -> ctx { Core.affineBindings =
          Map.insert name ty (Core.affineBindings ctx) }
        Linear -> ctx { Core.linearBindings =
          Map.insert name ty (Core.linearBindings ctx) }

makeCapture
  :: [(GrammarV1ResolvedBinder, CheckedTypeMode)]
  -> GrammarV1ResolvedBinder -> Maybe ClosureCapture
makeCapture typed binder = do
  checked <- exactType typed binder
  let mode = checkedBindingMode checked
  Just ClosureCapture
    { closureCaptureOccurrence = CaptureOccurrenceKey
        (unName (grammarV1ResolvedBinderCoreName binder))
    , closureCaptureTransfer = if mode == Unrestricted
        then CopyCapture else MoveCapture
    , closureCaptureStructuralMode = mode }

consumeCapture
  :: [(GrammarV1ResolvedBinder, CheckedTypeMode)]
  -> Core.ResourceContext -> GrammarV1ResolvedBinder
  -> Either SourceClosureError Core.ResourceContext
consumeCapture typed ctx binder = do
  let name = grammarV1ResolvedBinderCoreName binder
      expected = exactType typed binder
  (mode,ty,next) <- either (Left . SourceClosureCoreError) Right
    (Core.useBinding name ctx)
  case expected of
    Just checked | checkedBindingMode checked == mode
                   && checkedBindingType checked == ty -> Right next
    Just checked -> Left
      (SourceClosureTypeModeMismatch name (checkedBindingMode checked) mode)
    Nothing -> Left (SourceClosureCoreError (Core.UnknownBinding name))

hasBinder :: [(GrammarV1ResolvedBinder,a)] -> GrammarV1ResolvedBinder -> Bool
hasBinder xs binder = any (sameBinder binder . fst) xs

exactType :: [(GrammarV1ResolvedBinder,a)] -> GrammarV1ResolvedBinder -> Maybe a
exactType xs binder = case [ value | (other,value) <- xs, sameBinder other binder ] of
  [one] -> Just one
  _ -> Nothing

sameBinder :: GrammarV1ResolvedBinder -> GrammarV1ResolvedBinder -> Bool
sameBinder a b = grammarV1ResolvedBinderKey a == grammarV1ResolvedBinderKey b

sourceMode :: Maybe GrammarV1StructuralMode -> Maybe Mode
sourceMode maybeMode = case maybeMode of
  Nothing -> Nothing
  Just GrammarV1Unrestricted -> Just Unrestricted
  Just GrammarV1Affine -> Just Affine
  Just GrammarV1Linear -> Just Linear

sameNominal :: Located GrammarV1Type -> Located GrammarV1Type -> Bool
sameNominal (Located _ (GrammarV1NamedType a))
    (Located _ (GrammarV1NamedType b)) =
  null (grammarV1StaticReferenceArguments a) &&
  null (grammarV1StaticReferenceArguments b) &&
  grammarV1QualifiedNameParts (grammarV1StaticReferenceName a) ==
    grammarV1QualifiedNameParts (grammarV1StaticReferenceName b)
sameNominal _ _ = False

unitClosure :: GrammarV1Closure -> Bool
unitClosure closure =
  case grammarV1BlockStatements (locatedValue (grammarV1ClosureBody closure)) of
    [Located _ (GrammarV1ExpressionStatement expression)] ->
      case locatedValue expression of
        GrammarV1UnitExpression -> True
        _ -> False
    _ -> False
