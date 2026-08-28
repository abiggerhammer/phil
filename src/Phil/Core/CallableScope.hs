{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.CallableScope
  ( LoanScopeKey (..)
  , ClosureExtent (..)
  , ClosureScopeCapture (..)
  , ClosureRecursionNode (..)
  , CallableScopeError (..)
  , checkClosureCaptureScope
  , checkRestrictedRecursiveClosureCycles
  ) where

import qualified CallableScopeKernel as CallableScopeKernel
import Data.Graph (SCC (..), stronglyConnComp)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Callable
  ( CallableOccurrenceKey
  , CaptureOccurrenceKey
  )

-- | Stable lexical validity scope for one scoped shared-loan view.
newtype LoanScopeKey = LoanScopeKey
  { unLoanScopeKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | Bounded Phase 1 lifetime classification for a constructed closure.
-- Exact-scope containment is intentionally conservative; this is not a general
-- lifetime/subscope calculus.
data ClosureExtent
  = EscapingClosure
  | ClosureContainedIn LoanScopeKey
  deriving (Eq, Ord, Show)

-- | Scope-relevant capture facts kept separate from ordinary structural capture
-- ownership. A structurally valid capture may still fail the lifetime check.
data ClosureScopeCapture
  = ScopeIndependentCapture CaptureOccurrenceKey
  | ScopedSharedLoanCapture CaptureOccurrenceKey LoanScopeKey
  deriving (Eq, Ord, Show)

-- | One node in the checked closure-environment reference graph. Restricted
-- captures name exact moved affine/linear occurrences hidden by that environment.
data ClosureRecursionNode = ClosureRecursionNode
  { closureRecursionOccurrence :: CallableOccurrenceKey
  , closureRecursionReferences :: Set.Set CallableOccurrenceKey
  , closureRecursionRestrictedCaptures :: Set.Set CaptureOccurrenceKey
  }
  deriving (Eq, Ord, Show)

data CallableScopeError
  = EscapingClosureCapturesScopedLoan
      CallableOccurrenceKey
      CaptureOccurrenceKey
      LoanScopeKey
  | ClosureOutsideScopedLoanValidity
      CallableOccurrenceKey
      CaptureOccurrenceKey
      LoanScopeKey
      LoanScopeKey
  | DuplicateRecursiveClosureNode CallableOccurrenceKey
  | UnknownRecursiveClosureReference
      CallableOccurrenceKey
      CallableOccurrenceKey
  | RestrictedRecursiveClosureCycle
      (Set.Set CallableOccurrenceKey)
      (Set.Set CaptureOccurrenceKey)
  | CallableScopeKernelBridgeMismatch
  deriving (Eq, Ord, Show)

-- | Enforce the bounded Phase 1 closure-loan rule. Concrete key equality remains
-- native, but the final accept/reject classification is owned by the exact
-- extracted CALL-SCOPE kernel.
checkClosureCaptureScope
  :: CallableOccurrenceKey
  -> ClosureExtent
  -> [ClosureScopeCapture]
  -> Either CallableScopeError ()
checkClosureCaptureScope closureKey extent = mapM_ checkCapture
  where
    checkCapture capture =
      let isEscaping = case extent of
            EscapingClosure -> True
            ClosureContainedIn _ -> False
          isScopedLoan = case capture of
            ScopeIndependentCapture _ -> False
            ScopedSharedLoanCapture _ _ -> True
          sameScope = case (extent, capture) of
            (ClosureContainedIn closureScope, ScopedSharedLoanCapture _ loanScope) ->
              closureScope == loanScope
            _ -> False
          decision = CallableScopeKernel.decideScopeCaptureByFacts
            isEscaping
            isScopedLoan
            sameScope
      in case (decision, capture, extent) of
          (CallableScopeKernel.ScopeCaptureAccepted, _, _) -> Right ()
          ( CallableScopeKernel.ScopeCaptureEscapingLoan
            , ScopedSharedLoanCapture captureKey loanScope
            , EscapingClosure
            ) -> Left
              (EscapingClosureCapturesScopedLoan closureKey captureKey loanScope)
          ( CallableScopeKernel.ScopeCaptureOutsideLoanValidity
            , ScopedSharedLoanCapture captureKey loanScope
            , ClosureContainedIn closureScope
            ) -> Left
              (ClosureOutsideScopedLoanValidity
                closureKey
                captureKey
                loanScope
                closureScope)
          _ -> Left CallableScopeKernelBridgeMismatch

-- | Reject closure-environment cycles that hide any restricted capture. Native
-- Map/Set/SCC machinery discovers exact witness payloads; the extracted kernel
-- owns the ordered duplicate -> unknown reference -> restricted cycle -> accept
-- classification. Any category disagreement fails closed.
checkRestrictedRecursiveClosureCycles
  :: [ClosureRecursionNode]
  -> Either CallableScopeError ()
checkRestrictedRecursiveClosureCycles nodes =
  case buildNodeMap nodes of
    Left duplicateError ->
      case CallableScopeKernel.decideRecursiveClosureGraphFacts False False False of
        CallableScopeKernel.RecursiveClosureDuplicateNode -> Left duplicateError
        _ -> Left CallableScopeKernelBridgeMismatch
    Right nodeMap ->
      case firstUnknownReference nodeMap of
        Just unknownError ->
          case CallableScopeKernel.decideRecursiveClosureGraphFacts True False False of
            CallableScopeKernel.RecursiveClosureUnknownReference -> Left unknownError
            _ -> Left CallableScopeKernelBridgeMismatch
        Nothing ->
          case firstRestrictedCycle nodeMap of
            Just cycleError ->
              case CallableScopeKernel.decideRecursiveClosureGraphFacts True True False of
                CallableScopeKernel.RecursiveClosureRestrictedCycle -> Left cycleError
                _ -> Left CallableScopeKernelBridgeMismatch
            Nothing ->
              case CallableScopeKernel.decideRecursiveClosureGraphFacts True True True of
                CallableScopeKernel.RecursiveClosureGraphAccepted -> Right ()
                _ -> Left CallableScopeKernelBridgeMismatch
  where
    buildNodeMap = foldl insertNode (Right Map.empty)

    insertNode accumulated node = do
      result <- accumulated
      let key = closureRecursionOccurrence node
      if Map.member key result
        then Left (DuplicateRecursiveClosureNode key)
        else Right (Map.insert key node result)

    firstUnknownReference nodeMap = checkNodes (Map.elems nodeMap)
      where
        checkNodes [] = Nothing
        checkNodes (node : rest) =
          case checkReferences
              (closureRecursionOccurrence node)
              (Set.toAscList (closureRecursionReferences node)) of
            Just err -> Just err
            Nothing -> checkNodes rest

        checkReferences _ [] = Nothing
        checkReferences source (target : rest)
          | Map.member target nodeMap = checkReferences source rest
          | otherwise = Just (UnknownRecursiveClosureReference source target)

    firstRestrictedCycle nodeMap = checkSccs
      (stronglyConnComp
        [ (node, key, Set.toAscList (closureRecursionReferences node))
        | (key, node) <- Map.toAscList nodeMap
        ])
      where
        checkSccs [] = Nothing
        checkSccs (AcyclicSCC _ : rest) = checkSccs rest
        checkSccs (CyclicSCC members : rest) =
          let closureKeys = Set.fromList (map closureRecursionOccurrence members)
              restrictedCaptures = Set.unions
                (map closureRecursionRestrictedCaptures members)
          in if Set.null restrictedCaptures
              then checkSccs rest
              else Just
                (RestrictedRecursiveClosureCycle closureKeys restrictedCaptures)
