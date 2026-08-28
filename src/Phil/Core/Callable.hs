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
  , CheckedCallableEffects (..)
  , CallableOccurrence (..)
  , CallableResourceState (..)
  , CallableInvocationBodySummary (..)
  , CallableUse (..)
  , CallableCheckError (..)
  , checkClosureCaptures
  , closureStructuralMode
  , inferReachableCallableEffects
  , checkCallableEffectBound
  , singletonCallableResourceState
  , lookupCallableOccurrence
  , invokeCallableOccurrence
  ) where

import qualified CallableEffectKernel as CallableEffectKernel
import qualified CallableLifecycleKernel as CallableLifecycleKernel
import qualified CallableModeKernel as CallableModeKernel
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

-- | Successful comparison of one checked implementation footprint with its
-- stabilized public may-effect bound. The two sets remain separate because a
-- narrower current body does not silently narrow the public callable interface.
data CheckedCallableEffects = CheckedCallableEffects
  { checkedCallableInterfaceRevision :: InterfaceRevision
  , checkedCallableInferredEffects :: Set.Set SemanticEffect
  , checkedCallablePublicEffectBound :: Set.Set SemanticEffect
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
  | CallableModeKernelBridgeMismatch
  | CallableEffectKernelBridgeMismatch
  | CallableLifecycleKernelBridgeMismatch
  | CallableEffectBoundExceeded
      InterfaceRevision
      (Set.Set SemanticEffect)
      (Set.Set SemanticEffect)
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
        , CallableModeKernel.captureMovedRestrictedByMode
            (toCallableModeKernelMode (closureCaptureStructuralMode capture))
            (toCallableModeKernelTransfer (closureCaptureTransfer capture))
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
          kernelMode = toCallableModeKernelMode mode
          kernelTransfer = toCallableModeKernelTransfer
            (closureCaptureTransfer capture)
      case Map.lookup key result of
        Just previous ->
          let sameOccurrence = key == closureCaptureOccurrence previous
              duplicateDecision = CallableModeKernel.decideCallableDuplicateCapture
                sameOccurrence
                kernelMode
                (toCallableModeKernelMode
                  (closureCaptureStructuralMode previous))
          in if not sameOccurrence
              then Left CallableModeKernelBridgeMismatch
              else case duplicateDecision of
                CallableModeKernel.CallableDuplicateCaptureAccepted -> Right result
                CallableModeKernel.CallableDuplicateRestrictedCapture ->
                  Left (DuplicateRestrictedCapture key mode)
        Nothing ->
          case CallableModeKernel.decideCallableCaptureTransfer
              kernelMode kernelTransfer of
            CallableModeKernel.CallableCaptureTransferAccepted ->
              Right (Map.insert key capture result)
            CallableModeKernel.CallableRestrictedCaptureMustMove ->
              Left (RestrictedCaptureMustMove key mode)

-- | Closure structural mode is the least upper bound of the modes of values it
-- owns: unrestricted < affine < linear.
closureStructuralMode :: [ClosureCapture] -> Mode
closureStructuralMode captures =
  fromCallableModeKernelMode
    (CallableModeKernel.closureStructuralModeFromModes
      (toCallableModeKernelModeList
        (map closureCaptureStructuralMode captures)))

-- | Infer effects from reachable checked callable uses. The extracted CALL-EFFECT
-- kernel owns the use-kind decision; native Set union remains the concrete finite
-- effect-set representation.
inferReachableCallableEffects :: [CallableUse] -> Set.Set SemanticEffect
inferReachableCallableEffects = foldl addUse Set.empty
  where
    addUse effects use =
      let (kind, publicBound) = callableUseEffectKernelFacts use
      in if CallableEffectKernel.callableUseEffectKindContributesPublicBound kind
          then Set.union effects publicBound
          else effects

-- | Check one implementation's inferred reachable semantic effects against the
-- stabilized public may-effect bound. Native Set subset/difference supply finite
-- representation facts, while the extracted kernel owns accept/reject and every
-- undeclared-effect classification used in the widening diagnostic.
checkCallableEffectBound
  :: CallableContract
  -> Set.Set SemanticEffect
  -> Either CallableCheckError CheckedCallableEffects
checkCallableEffectBound contract inferred =
  case CallableEffectKernel.decideCallableEffectBound subsetFact of
    CallableEffectKernel.CallableEffectBoundAccepted -> Right CheckedCallableEffects
      { checkedCallableInterfaceRevision = callableContractInterfaceRevision contract
      , checkedCallableInferredEffects = inferred
      , checkedCallablePublicEffectBound = publicBound
      }
    CallableEffectKernel.CallableEffectBoundExceeded ->
      let extra = Set.difference inferred publicBound
      in if callableEffectDeltaAgrees inferred publicBound extra
          then Left (CallableEffectBoundExceeded
            (callableContractInterfaceRevision contract)
            extra
            publicBound)
          else Left CallableEffectKernelBridgeMismatch
  where
    publicBound = callableContractEffectBound contract
    subsetFact = inferred `Set.isSubsetOf` publicBound

callableUseEffectKernelFacts
  :: CallableUse
  -> (CallableEffectKernel.CallableUseEffectKind, Set.Set SemanticEffect)
callableUseEffectKernelFacts use = case use of
  PossessCallable contract ->
    (CallableEffectKernel.PossessEffectUse, callableContractEffectBound contract)
  PassCallable contract ->
    (CallableEffectKernel.PassEffectUse, callableContractEffectBound contract)
  StoreCallable contract ->
    (CallableEffectKernel.StoreEffectUse, callableContractEffectBound contract)
  ReturnCallable contract ->
    (CallableEffectKernel.ReturnEffectUse, callableContractEffectBound contract)
  InvokeCallable contract ->
    (CallableEffectKernel.InvokeEffectUse, callableContractEffectBound contract)

callableEffectDeltaAgrees
  :: Set.Set SemanticEffect
  -> Set.Set SemanticEffect
  -> Set.Set SemanticEffect
  -> Bool
callableEffectDeltaAgrees inferred publicBound extra =
  all effectAgrees (Set.toAscList (Set.union inferred publicBound))
  where
    effectAgrees effect =
      Set.member effect extra
        == CallableEffectKernel.effectDeltaBit
          (Set.member effect inferred)
          (Set.member effect publicBound)

singletonCallableResourceState :: CallableOccurrence -> CallableResourceState
singletonCallableResourceState occurrence = CallableResourceState
  (Map.singleton (callableOccurrenceKey occurrence) occurrence)

lookupCallableOccurrence
  :: CallableOccurrenceKey
  -> CallableResourceState
  -> Maybe CallableOccurrence
lookupCallableOccurrence key = Map.lookup key . callableResourceOccurrences

-- | Apply the callable owner's declared transition to ordinary resource state.
-- The extracted CALL-LIFE kernel owns transition acceptance/failure precedence;
-- concrete Map/Set facts and state mutation remain the representation boundary.
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

    preserve predecessor =
      let expected = closureMovedRestrictedOccurrences
            (callableOccurrenceCaptures predecessor)
          actual = invocationRestrictedCaptureResidue body
          successor = invocationSuccessorCallable body
          successorAbsent = case successor of
            Nothing -> True
            Just _ -> False
      in case CallableLifecycleKernel.decideCallablePreserve
          (actual == expected) successorAbsent of
        CallableLifecycleKernel.CallablePreserveAccepted -> Right state
        CallableLifecycleKernel.CallablePreserveResidueMismatch ->
          Left (PreserveCalleeRestrictedStateMismatch predecessorKey expected actual)
        CallableLifecycleKernel.CallablePreserveProducedSuccessor ->
          case successor of
            Just replacement -> Left
              (PreserveCalleeProducedSuccessor
                predecessorKey
                (callableOccurrenceKey replacement))
            Nothing -> Left CallableLifecycleKernelBridgeMismatch

    consume _predecessor =
      let actual = invocationRestrictedCaptureResidue body
          successor = invocationSuccessorCallable body
          successorAbsent = case successor of
            Nothing -> True
            Just _ -> False
      in case CallableLifecycleKernel.decideCallableConsume
          (Set.null actual) successorAbsent of
        CallableLifecycleKernel.CallableConsumeAccepted ->
          Right (CallableResourceState (Map.delete predecessorKey occurrences))
        CallableLifecycleKernel.CallableConsumeRetainedResidue ->
          Left (ConsumeCalleeRetainedRestrictedState predecessorKey actual)
        CallableLifecycleKernel.CallableConsumeProducedSuccessor ->
          case successor of
            Just replacement -> Left
              (ConsumeCalleeProducedSuccessor
                predecessorKey
                (callableOccurrenceKey replacement))
            Nothing -> Left CallableLifecycleKernelBridgeMismatch

    replace _predecessor expectedInterface expectedState =
      let actual = invocationRestrictedCaptureResidue body
          successor = invocationSuccessorCallable body
          residueEmpty = Set.null actual
          ( successorPresent
            , successorDistinct
            , successorFresh
            , interfaceMatches
            , stateMatches
            ) = case successor of
              Nothing -> (False, False, False, False, False)
              Just replacement ->
                let successorKey = callableOccurrenceKey replacement
                    actualInterface = callableContractInterfaceRevision
                      (callableOccurrenceContract replacement)
                    actualState = callableOccurrenceStateKey replacement
                in ( True
                   , successorKey /= predecessorKey
                   , not (Map.member successorKey occurrences)
                   , actualInterface == expectedInterface
                   , actualState == expectedState
                   )
          decision = CallableLifecycleKernel.decideCallableReplace
            residueEmpty
            successorPresent
            successorDistinct
            successorFresh
            interfaceMatches
            stateMatches
      in case decision of
        CallableLifecycleKernel.CallableReplaceRetainedResidue ->
          Left (ReplaceCalleeRetainedPredecessorState predecessorKey actual)
        CallableLifecycleKernel.CallableReplaceMissingSuccessor ->
          Left (ReplaceCalleeMissingSuccessor predecessorKey)
        CallableLifecycleKernel.CallableReplaceReusedPredecessor ->
          Left (ReplaceCalleeReusedPredecessorKey predecessorKey)
        CallableLifecycleKernel.CallableReplaceSuccessorAlreadyAvailable ->
          case successor of
            Just replacement -> Left
              (ReplaceCalleeSuccessorAlreadyAvailable
                (callableOccurrenceKey replacement))
            Nothing -> Left CallableLifecycleKernelBridgeMismatch
        CallableLifecycleKernel.CallableReplaceInterfaceMismatch ->
          case successor of
            Just replacement -> Left
              (ReplaceCalleeInterfaceMismatch
                expectedInterface
                (callableContractInterfaceRevision
                  (callableOccurrenceContract replacement)))
            Nothing -> Left CallableLifecycleKernelBridgeMismatch
        CallableLifecycleKernel.CallableReplaceStateMismatch ->
          case successor of
            Just replacement -> Left
              (ReplaceCalleeStateMismatch
                expectedState
                (callableOccurrenceStateKey replacement))
            Nothing -> Left CallableLifecycleKernelBridgeMismatch
        CallableLifecycleKernel.CallableReplaceAccepted ->
          case successor of
            Just replacement ->
              let successorKey = callableOccurrenceKey replacement
              in Right (CallableResourceState
                (Map.insert
                  successorKey
                  replacement
                  (Map.delete predecessorKey occurrences)))
            Nothing -> Left CallableLifecycleKernelBridgeMismatch

toCallableModeKernelMode :: Mode -> CallableModeKernel.Mode
toCallableModeKernelMode mode = case mode of
  Unrestricted -> CallableModeKernel.Unrestricted
  Affine -> CallableModeKernel.Affine
  Linear -> CallableModeKernel.Linear

fromCallableModeKernelMode :: CallableModeKernel.Mode -> Mode
fromCallableModeKernelMode mode = case mode of
  CallableModeKernel.Unrestricted -> Unrestricted
  CallableModeKernel.Affine -> Affine
  CallableModeKernel.Linear -> Linear

toCallableModeKernelTransfer :: CaptureTransfer -> CallableModeKernel.CaptureTransfer
toCallableModeKernelTransfer transfer = case transfer of
  CopyCapture -> CallableModeKernel.CopyCapture
  MoveCapture -> CallableModeKernel.MoveCapture

toCallableModeKernelModeList :: [Mode] -> CallableModeKernel.List CallableModeKernel.Mode
toCallableModeKernelModeList modes = case modes of
  [] -> CallableModeKernel.Nil
  mode : rest -> CallableModeKernel.Cons
    (toCallableModeKernelMode mode)
    (toCallableModeKernelModeList rest)
