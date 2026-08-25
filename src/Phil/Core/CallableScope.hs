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
  deriving (Eq, Ord, Show)

-- | Enforce the bounded Phase 1 closure-loan rule. Escaping closures may not
-- capture scoped shared views. A non-escaping local closure is admitted only
-- when its declared containment scope exactly matches the loan validity scope.
checkClosureCaptureScope
  :: CallableOccurrenceKey
  -> ClosureExtent
  -> [ClosureScopeCapture]
  -> Either CallableScopeError ()
checkClosureCaptureScope closureKey extent = mapM_ checkCapture
  where
    checkCapture capture = case capture of
      ScopeIndependentCapture _ -> Right ()
      ScopedSharedLoanCapture captureKey loanScope -> case extent of
        EscapingClosure -> Left
          (EscapingClosureCapturesScopedLoan closureKey captureKey loanScope)
        ClosureContainedIn closureScope
          | closureScope == loanScope -> Right ()
          | otherwise -> Left
              (ClosureOutsideScopedLoanValidity
                closureKey
                captureKey
                loanScope
                closureScope)

-- | Reject closure-environment cycles that hide any restricted capture. Named
-- recursive callables with no cyclic restricted environment remain outside this
-- rejection: this graph is specifically the runtime closure-environment graph.
checkRestrictedRecursiveClosureCycles
  :: [ClosureRecursionNode]
  -> Either CallableScopeError ()
checkRestrictedRecursiveClosureCycles nodes = do
  nodeMap <- foldl insertNode (Right Map.empty) nodes
  mapM_ (validateReferences nodeMap) (Map.elems nodeMap)
  mapM_ rejectRestrictedCycle
    (stronglyConnComp
      [ (node, key, Set.toAscList (closureRecursionReferences node))
      | (key, node) <- Map.toAscList nodeMap
      ])
  where
    insertNode accumulated node = do
      result <- accumulated
      let key = closureRecursionOccurrence node
      if Map.member key result
        then Left (DuplicateRecursiveClosureNode key)
        else Right (Map.insert key node result)

    validateReferences nodeMap node =
      mapM_ (validateReference nodeMap (closureRecursionOccurrence node))
        (Set.toAscList (closureRecursionReferences node))

    validateReference nodeMap source target
      | Map.member target nodeMap = Right ()
      | otherwise = Left (UnknownRecursiveClosureReference source target)

    rejectRestrictedCycle scc = case scc of
      AcyclicSCC _ -> Right ()
      CyclicSCC members ->
        let closureKeys = Set.fromList (map closureRecursionOccurrence members)
            restrictedCaptures = Set.unions
              (map closureRecursionRestrictedCaptures members)
        in if Set.null restrictedCaptures
            then Right ()
            else Left
              (RestrictedRecursiveClosureCycle closureKeys restrictedCaptures)
