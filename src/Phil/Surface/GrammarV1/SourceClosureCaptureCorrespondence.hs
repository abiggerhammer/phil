{-# LANGUAGE OverloadedStrings #-}

-- | FSEM-01 CORR-1: independent native replay of the *bounded* C-1
-- resource cut observations. Does not validate arbitrary Phil source or
-- prove a Haskell-to-Rocq implementation refinement theorem.
module Phil.Surface.GrammarV1.SourceClosureCaptureCorrespondence
  ( SourceClosureCorrespondenceError (..)
  , verifyDirectCaptureCuts
  , verifyBorrowCaptureCuts
  ) where

import qualified Phil.Core.Context as Core
import Phil.Core.Callable
  ( CallableOccurrenceKey (..), CaptureOccurrenceKey (..)
  , CaptureTransfer (..), ClosureCapture (..), checkClosureCaptures )
import qualified Data.Map.Strict as Map
import Phil.Core.CallableScope
  ( ClosureScopeCapture (..), LoanScopeKey (..)
  , checkClosureCaptureScope )
import Phil.Core.Syntax (Mode (..), Name (..))
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.SourceClosureCapture
  ( SourceClosureError (..), SourceClosureFailureStage (..)
  , SourceDirectClosureRun (..), SourceBorrowClosureRun (..))

data SourceClosureCorrespondenceError
  = DirectCutOrErrorMismatch
  | BorrowCutOrErrorMismatch
  deriving (Eq, Show)

-- | Replay the checked source capture occurrences through native
-- Core.useBinding; capture list order is source order, not Map ordering.
-- Failed operations have no native successor context to record.
replayNativeUses
  :: Core.ResourceContext
  -> [GrammarV1ResolvedBinder]
  -> ([Core.ResourceContext], Either Core.CheckError Core.ResourceContext)
replayNativeUses initial = go initial [initial]
  where
    go current reversed [] = (reverse reversed, Right current)
    go current reversed (binder : remaining) =
      case Core.useBinding (grammarV1ResolvedBinderCoreName binder) current of
        Left err -> (reverse reversed, Left err)
        Right (_, _, next) -> go next (next : reversed) remaining

verifyDirectCaptureCuts
  :: SourceDirectClosureRun
  -> Either SourceClosureCorrespondenceError ()
verifyDirectCaptureCuts run =
  if consistent then Right () else Left DirectCutOrErrorMismatch
  where
    initial = directInitial run
    cut = directCuts run
    prechecked = cut == [initial] && directFinal run == Nothing
    (nativeCuts, nativeResult) =
      replayNativeUses initial (directCaptures run)
    describe binder =
      let name = grammarV1ResolvedBinderCoreName binder
          key = CaptureOccurrenceKey (unName name)
          capture transfer mode = ClosureCapture key transfer mode
      in case Map.lookup name (Core.unrestrictedBindings initial) of
           Just _ -> Just (capture CopyCapture Unrestricted)
           Nothing -> case Map.lookup name (Core.affineBindings initial) of
             Just _ -> Just (capture MoveCapture Affine)
             Nothing -> case Map.lookup name (Core.linearBindings initial) of
               Just _ -> Just (capture MoveCapture Linear)
               Nothing -> Nothing
    nativeSummary = case mapM describe (directCaptures run) of
      Just descriptions -> Just (checkClosureCaptures descriptions)
      Nothing -> Nothing
    consistent = case directOutcome run of
      Right () ->
        directFailureStage run == Nothing &&
        case nativeSummary of
          Just (Right summary) ->
            directSummary run == Just summary && cut == nativeCuts &&
            case nativeResult of
              Right next -> directFinal run == Just next
              Left _ -> False
          _ -> False
      Left (SourceClosureCaptureError err) ->
        directFailureStage run == Just ClosureCaptureValidation &&
        directSummary run == Nothing && prechecked &&
        nativeSummary == Just (Left err)
      Left (SourceClosureModeMismatch _ _) ->
        directFailureStage run == Just ClosureModeValidation &&
        prechecked &&
        case nativeSummary of
          Just (Right summary) -> directSummary run == Just summary
          _ -> False
      Left (SourceClosureCoreError err) ->
        directFailureStage run == Just ClosureNativeUse &&
        directFinal run == Nothing &&
        cut == nativeCuts && nativeResult == Left err &&
        case nativeSummary of
          Just (Right summary) -> directSummary run == Just summary
          _ -> False
      _ -> False

-- | Reconstruct the exact production native loan start and (where
-- genuinely accepted) closure. The source-derived loan-scope witness
-- is rechecked using the native CallableScope authority. Rejections
-- retain only the successful prefix, not an imagined loan-close state.
verifyBorrowCaptureCuts
  :: SourceBorrowClosureRun
  -> Either SourceClosureCorrespondenceError ()
verifyBorrowCaptureCuts run =
  if consistent then Right () else Left BorrowCutOrErrorMismatch
  where
    initial = borrowInitial run
    owner = grammarV1ResolvedBinderCoreName (borrowOwner run)
    view = unName (grammarV1ResolvedBinderCoreName (borrowView run))
    scopeKey = LoanScopeKey ("loan:" <> view)
    callable = CallableOccurrenceKey ("closure:" <> view)
    captured = ScopedSharedLoanCapture (CaptureOccurrenceKey view) scopeKey
    nativeStart = Core.startSharedLoan owner initial
    consistent = case nativeStart of
      Left err ->
        borrowStarted run == Nothing &&
        borrowClosed run == Nothing &&
        borrowCuts run == [initial] &&
        borrowFailureStage run == Just ClosureLoanStart &&
        borrowOutcome run == Left (SourceClosureCoreError err)
      Right loaned ->
        let started = borrowStarted run == Just loaned
            baseCuts = borrowCuts run == [initial, loaned]
            scoped = checkClosureCaptureScope
              callable (borrowExtent run) [captured]
        in started && case borrowOutcome run of
          Right () ->
            borrowFailureStage run == Nothing &&
            scoped == Right () &&
            case Core.endSharedLoan owner loaned of
              Right closed ->
                borrowClosed run == Just closed &&
                borrowCuts run == [initial, loaned, closed]
              Left _ -> False
          Left (SourceClosureScopeError err) ->
            borrowFailureStage run == Just ClosureLoanScope &&
            borrowClosed run == Nothing && baseCuts &&
            scoped == Left err
          Left (SourceClosureModeMismatch _ _) ->
            borrowFailureStage run == Just ClosureModeValidation &&
            borrowClosed run == Nothing && baseCuts
          Left (SourceClosureCaptureError _) ->
            borrowFailureStage run == Just ClosureCaptureValidation &&
            borrowClosed run == Nothing && baseCuts
          Left (SourceClosureCoreError err) ->
            borrowFailureStage run == Just ClosureLoanClose &&
            borrowClosed run == Nothing && baseCuts &&
            Core.endSharedLoan owner loaned == Left err
          _ -> False
