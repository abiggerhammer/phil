{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.Callable
  ( CaptureOccurrenceKey (..)
  , CaptureTransfer (..)
  , ClosureCapture (..)
  , ClosureCaptureSummary (..)
  , CallableOccurrenceKey (..)
  , CallableStateKey (..)
  , CalleeTransition (..)
  , SemanticEffect (..)
  , CallableContract (..)
  , CallableOccurrence (..)
  , CallableResourceState (..)
  , CallableInvocationBodySummary (..)
  , CallableUse (..)
  , CallableCheckError (..)
  , checkClosureCaptures
  , closureStructuralMode
  , inferReachableCallableEffects
  , singletonCallableResourceState
  , lookupCallableOccurrence
  , invokeCallableOccurrence
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Static (InterfaceRevision)
import Phil.Core.Syntax (Mode (..))

-- | Stable term-occurrence identity for one source value captured by a closure.
-- Source spelling and target environment slot are deliberately absent.
newtype CaptureOccurrenceKey = CaptureOccurrenceKey
  { unCaptureOccurrenceKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | Whether closure construction copies an unrestricted value or transfers an
-- ownership occurrence into the sealed closure environment.
data CaptureTransfer
  = CopyCapture
  | MoveCapture
  deriving (Eq, Ord, Show)

-- | Canonical checker-facing capture description for the first Phase 1 slice.
data ClosureCapture = ClosureCapture
  { closureCaptureOccurrence :: CaptureOccurrenceKey
  , closureCaptureTransfer :: CaptureTransfer
  , closureCaptureStructuralMode :: Mode
  }
  deriving (Eq, Ord, Show)

-- | Normalized closure capture state. Restricted moves are listed explicitly so
-- the outer checker can remove those predecessor ownership occurrences.
data ClosureCaptureSummary = ClosureCaptureSummary
  { closureCapturesByOccurrence :: Map.Map CaptureOccurrenceKey ClosureCapture
  , closureMovedRestrictedOccurrences :: Set.Set CaptureOccurrenceKey
  , closureMinimumStructuralMode :: Mode
  }
  deriving (Eq, Ord, Show)

-- | Stable ownership occurrence for one first-class callable value.
newtype CallableOccurrenceKey = CallableOccurrenceKey
  { unCallableOccurrenceKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | Explicit source-semantic state carried by a state-indexed callable when the
-- public transition needs more than the callable interface revision itself.
newtype CallableStateKey = CallableStateKey
  { unCallableStateKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | Normative callee-transition distinctions. ReplaceCallee names both the exact
-- successor callable interface and its explicit state index, if one is present.
data CalleeTransition
  = PreserveCallee
  | ConsumeCallee
  | ReplaceCallee InterfaceRevision (Maybe CallableStateKey)
  deriving (Eq, Ord, Show)

newtype SemanticEffect = SemanticEffect
  { unSemanticEffect :: Text
  }
  deriving (Eq, Ord, Show)

-- | Bounded callable contract surface. Effect bound is a may-effect upper bound
-- for invocation; callee transition describes the callable owner's own residue.
data CallableContract = CallableContract
  { callableContractInterfaceRevision :: InterfaceRevision
  , callableContractCalleeTransition :: CalleeTransition
  , callableContractEffectBound :: Set.Set SemanticEffect
  }
  deriving (Eq, Ord, Show)

-- | One exact runtime/term-level callable ownership occurrence. Equal contracts
-- do not identify equal callable occurrences.
data CallableOccurrence = CallableOccurrence
  { callableOccurrenceKey :: CallableOccurrenceKey
  , callableOccurrenceContract :: CallableContract
  , callableOccurrenceCaptures :: ClosureCaptureSummary
  , callableOccurrenceStateKey :: Maybe CallableStateKey
  }
  deriving (Eq, Ord, Show)

-- | Ordinary resource-state view of currently available callable occurrences.
newtype CallableResourceState = CallableResourceState
  { callableResourceOccurrences :: Map.Map CallableOccurrenceKey CallableOccurrence
  }
  deriving (Eq, Ord, Show)

-- | Result supplied by checked callable-body/resource analysis to the callee
-- transition checker. For PreserveCallee, the exact restricted capture residue
-- must be present after the body. For ReplaceCallee, the successor occurrence
-- carries the replacement capture/state lineage.
data CallableInvocationBodySummary = CallableInvocationBodySummary
  { invocationRestrictedCaptureResidue :: Set.Set CaptureOccurrenceKey
  , invocationSuccessorCallable :: Maybe CallableOccurrence
  }
  deriving (Eq, Ord, Show)

-- | Reachable higher-order operations observed by body checking. Possession,
-- forwarding, storage, and return carry no invocation effect by themselves.
data CallableUse
  = PossessCallable CallableContract
  | PassCallable CallableContract
  | StoreCallable CallableContract
  | ReturnCallable CallableContract
  | InvokeCallable CallableContract
  deriving (Eq, Ord, Show)

data CallableCheckError
  = RestrictedCaptureMustMove CaptureOccurrenceKey Mode
  | DuplicateRestrictedCapture CaptureOccurrenceKey Mode
  | UnavailableCallableOccurrence CallableOccurrenceKey
  | PreserveCalleeRestrictedStateMismatch
      CallableOccurrenceKey
      (Set.Set CaptureOccurrenceKey)
      (Set.Set CaptureOccurrenceKey)
  | PreserveCalleeProducedSuccessor CallableOccurrenceKey CallableOccurrenceKey
  | ConsumeCalleeRetainedRestrictedState CallableOccurrenceKey (Set.Set CaptureOccurrenceKey)
  | ConsumeCalleeProducedSuccessor CallableOccurrenceKey CallableOccurrenceKey
  | ReplaceCalleeRetainedPredecessorState CallableOccurrenceKey (Set.Set CaptureOccurrenceKey)
  | ReplaceCalleeMissingSuccessor CallableOccurrenceKey
  | ReplaceCalleeReusedPredecessorKey CallableOccurrenceKey
  | ReplaceCalleeSuccessorAlreadyAvailable CallableOccurrenceKey
  | ReplaceCalleeInterfaceMismatch InterfaceRevision InterfaceRevision
  | ReplaceCalleeStateMismatch (Maybe CallableStateKey) (Maybe CallableStateKey)
  deriving (Eq, Ord, Show)

-- | Normalize closure capture ownership. Repeated unrestricted mentions collapse
-- to one canonical free-variable capture; affine/linear capture must be an exact
-- ownership move and may occur at most once. If the same stable occurrence is
-- described inconsistently and either description is restricted, fail closed.
checkClosureCaptures
  :: [ClosureCapture]
  -> Either CallableCheckError ClosureCaptureSummary
checkClosureCaptures captures = do
  normalized <- foldl addCapture (Right Map.empty) captures
  let movedRestricted = Set.fromList
        [ key
        | (key, capture) <- Map.toAscList normalized
        , closureCaptureTransfer capture == MoveCapture
        , closureCaptureStructuralMode capture /= Unrestricted
        ]
  Right ClosureCaptureSummary
    { closureCapturesByOccurrence = normalized
    , closureMovedRestrictedOccurrences = movedRestricted
    , closureMinimumStructuralMode = closureStructuralMode (Map.elems normalized)
    }
  where
    addCapture accumulated capture = do
      result <- accumulated
      let key = closureCaptureOccurrence capture
          mode = closureCaptureStructuralMode capture
      case Map.lookup key result of
        Just previous
          | mode /= Unrestricted
              || closureCaptureStructuralMode previous /= Unrestricted ->
              Left (DuplicateRestrictedCapture key mode)
          | otherwise -> Right result
        Nothing -> case mode of
          Unrestricted -> Right (Map.insert key capture result)
          _
            | closureCaptureTransfer capture /= MoveCapture ->
                Left (RestrictedCaptureMustMove key mode)
            | otherwise -> Right (Map.insert key capture result)

-- | Closure structural mode is the least upper bound of the modes of values it
-- owns: unrestricted < affine < linear.
closureStructuralMode :: [ClosureCapture] -> Mode
closureStructuralMode = foldl joinMode Unrestricted . map closureCaptureStructuralMode
  where
    joinMode Linear _ = Linear
    joinMode _ Linear = Linear
    joinMode Affine _ = Affine
    joinMode _ Affine = Affine
    joinMode Unrestricted Unrestricted = Unrestricted

-- | Infer effects from reachable checked callable uses. Merely possessing,
-- passing, storing, or returning a callable does not import its invocation
-- effects; an actual reachable invocation contributes the exact public bound.
inferReachableCallableEffects :: [CallableUse] -> Set.Set SemanticEffect
inferReachableCallableEffects = foldl addUse Set.empty
  where
    addUse effects use = case use of
      InvokeCallable contract -> Set.union effects (callableContractEffectBound contract)
      PossessCallable _ -> effects
      PassCallable _ -> effects
      StoreCallable _ -> effects
      ReturnCallable _ -> effects

singletonCallableResourceState :: CallableOccurrence -> CallableResourceState
singletonCallableResourceState occurrence = CallableResourceState
  (Map.singleton (callableOccurrenceKey occurrence) occurrence)

lookupCallableOccurrence
  :: CallableOccurrenceKey
  -> CallableResourceState
  -> Maybe CallableOccurrence
lookupCallableOccurrence key = Map.lookup key . callableResourceOccurrences

-- | Apply the callable owner's declared transition to ordinary resource state.
-- This function deliberately keys availability by exact ownership occurrence:
-- a successor with an equal contract never makes the predecessor live again.
invokeCallableOccurrence
  :: CallableOccurrenceKey
  -> CallableInvocationBodySummary
  -> CallableResourceState
  -> Either CallableCheckError CallableResourceState
invokeCallableOccurrence predecessorKey body state = do
  predecessor <- maybe
    (Left (UnavailableCallableOccurrence predecessorKey))
    Right
    (lookupCallableOccurrence predecessorKey state)
  case callableContractCalleeTransition (callableOccurrenceContract predecessor) of
    PreserveCallee -> preserve predecessor
    ConsumeCallee -> consume predecessor
    ReplaceCallee expectedInterface expectedState ->
      replace predecessor expectedInterface expectedState
  where
    occurrences = callableResourceOccurrences state

    preserve predecessor = do
      let expected = closureMovedRestrictedOccurrences
            (callableOccurrenceCaptures predecessor)
          actual = invocationRestrictedCaptureResidue body
      if actual /= expected
        then Left (PreserveCalleeRestrictedStateMismatch predecessorKey expected actual)
        else case invocationSuccessorCallable body of
          Nothing -> Right state
          Just successor -> Left
            (PreserveCalleeProducedSuccessor predecessorKey (callableOccurrenceKey successor))

    consume _predecessor
      | not (Set.null (invocationRestrictedCaptureResidue body)) =
          Left (ConsumeCalleeRetainedRestrictedState
            predecessorKey
            (invocationRestrictedCaptureResidue body))
      | otherwise = case invocationSuccessorCallable body of
          Just successor -> Left
            (ConsumeCalleeProducedSuccessor predecessorKey (callableOccurrenceKey successor))
          Nothing -> Right (CallableResourceState (Map.delete predecessorKey occurrences))

    replace _predecessor expectedInterface expectedState
      | not (Set.null (invocationRestrictedCaptureResidue body)) =
          Left (ReplaceCalleeRetainedPredecessorState
            predecessorKey
            (invocationRestrictedCaptureResidue body))
      | otherwise = case invocationSuccessorCallable body of
          Nothing -> Left (ReplaceCalleeMissingSuccessor predecessorKey)
          Just successor -> do
            let successorKey = callableOccurrenceKey successor
                actualInterface = callableContractInterfaceRevision
                  (callableOccurrenceContract successor)
                actualState = callableOccurrenceStateKey successor
            if successorKey == predecessorKey
              then Left (ReplaceCalleeReusedPredecessorKey predecessorKey)
              else if Map.member successorKey occurrences
                then Left (ReplaceCalleeSuccessorAlreadyAvailable successorKey)
                else if actualInterface /= expectedInterface
                  then Left (ReplaceCalleeInterfaceMismatch expectedInterface actualInterface)
                  else if actualState /= expectedState
                    then Left (ReplaceCalleeStateMismatch expectedState actualState)
                    else Right (CallableResourceState
                      (Map.insert successorKey successor (Map.delete predecessorKey occurrences)))
