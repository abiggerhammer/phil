{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.ControlStateProjection
  ( ControlStateStageRevision (..)
  , StateBoundaryKey (..)
  , StateSlotKey (..)
  , StateProjectionKey (..)
  , CaptureCarrierKey (..)
  , StateBoundaryKind (..)
  , StateSubjectRequirement (..)
  , StateSlotContract (..)
  , StateBoundaryContract (..)
  , StateProjectionKind (..)
  , StateProjection (..)
  , ClosureCaptureProjection (..)
  , ControlStateStageBundle (..)
  , ControlStateProjectionError (..)
  , deriveControlStateStageRevision
  , makeControlStateStageBundle
  , verifyControlStateStageBundle
  , checkStateProjection
  , checkStateBoundaryProjections
  , checkClosureCaptureProjection
  ) where

import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Callable (CaptureOccurrenceKey (..))
import Phil.Core.CallableRefinement (CallableAuthorityRequirement (..))
import Phil.Core.Static
  ( SemanticForm (..)
  , canonicalSemanticForm
  )
import Phil.Core.Syntax (Mode (..))
import Phil.Systems.AuthorityEffectCorrespondence
  ( AuthorityEffectStageBundle (..)
  )
import Phil.Systems.BranchResourceFailure
  ( BranchResourceStageBundle (..)
  , BranchResourceStageRevision (..)
  , BranchResourceStageVerificationError
  , verifyBranchResourceStageBundle
  )
import Phil.Systems.CallableLowering
  ( CallableCaptureSemantic (..)
  )
import Phil.Systems.IR
  ( BlockId (..)
  , SystemsArtifact (..)
  , SystemsBlock (..)
  , SystemsChoiceArm (..)
  , SystemsFunction (..)
  , SystemsProgram (..)
  , SystemsRuntimeChoiceArm (..)
  , SystemsTerminator (..)
  , SystemsValue (..)
  , SystemsValueRole (..)
  , ValueId (..)
  )
import Phil.Systems.Phase1Stage
  ( Phase1StageBundle (..)
  )
import Phil.Systems.ProviderCallCorrespondence
  ( ProviderCallStageBundle (..)
  )
import Phil.Systems.SubjectCorrespondence
  ( SourceSubjectKey (..)
  , SubjectCorrespondence (..)
  , SubjectStageBundle (..)
  , SystemsValueRef (..)
  )
import qualified ResourceJoinKernel as ResourceJoinKernel
import qualified ResourceScopeKernel as ResourceScopeKernel
import qualified SystemsControlPreservationKernel as Kernel

newtype ControlStateStageRevision = ControlStateStageRevision
  { unControlStateStageRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype StateBoundaryKey = StateBoundaryKey
  { unStateBoundaryKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype StateSlotKey = StateSlotKey
  { unStateSlotKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype StateProjectionKey = StateProjectionKey
  { unStateProjectionKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype CaptureCarrierKey = CaptureCarrierKey
  { unCaptureCarrierKey :: Text
  }
  deriving (Eq, Ord, Show)

data StateBoundaryKind
  = OrdinaryJoinBoundary
  | LoopStateBoundary
  deriving (Eq, Ord, Show)

data StateSubjectRequirement
  = AnyStateSubject
  | FixedStateSubject SourceSubjectKey
  deriving (Eq, Ord, Show)

data StateSlotContract = StateSlotContract
  { stateSlotKey :: StateSlotKey
  , stateSlotMode :: Mode
  , stateSlotSubjectRequirement :: StateSubjectRequirement
  }
  deriving (Eq, Ord, Show)

data StateBoundaryContract = StateBoundaryContract
  { stateBoundaryKey :: StateBoundaryKey
  , stateBoundaryKind :: StateBoundaryKind
  , stateBoundaryFunction :: Text
  , stateBoundaryTargetBlock :: BlockId
  , stateBoundarySlots :: Map StateSlotKey StateSlotContract
  }
  deriving (Eq, Ord, Show)

data StateProjectionKind
  = OrdinaryJoinPredecessor
  | LoopInitialEntry
  | LoopBackedge
  deriving (Eq, Ord, Show)

data StateProjection = StateProjection
  { stateProjectionKey :: StateProjectionKey
  , stateProjectionKind :: StateProjectionKind
  , stateProjectionBoundary :: StateBoundaryKey
  , stateProjectionFromBlock :: BlockId
  , stateProjectionEdgeLabel :: Text
  , stateProjectionIncomingRestricted :: Map SystemsValueRef Mode
  , stateProjectionBindings :: Map StateSlotKey SystemsValueRef
  }
  deriving (Eq, Ord, Show)

data ClosureCaptureProjection = ClosureCaptureProjection
  { closureCaptureProjectionKey :: Text
  , closureCaptureProjectionCaptures
      :: Map CaptureOccurrenceKey CallableCaptureSemantic
  , closureCaptureProjectionCarriers
      :: Map CaptureOccurrenceKey [CaptureCarrierKey]
  }
  deriving (Eq, Ord, Show)

data ControlStateStageBundle = ControlStateStageBundle
  { controlStateStageBase :: BranchResourceStageBundle
  , controlStateStageRevision :: ControlStateStageRevision
  , controlStateStageBoundaries :: Map StateBoundaryKey StateBoundaryContract
  , controlStateStageProjections :: Map StateProjectionKey StateProjection
  , controlStateStageClosureCaptures :: Map Text ClosureCaptureProjection
  }
  deriving (Eq, Show)

data ControlStateProjectionError
  = ControlStateBaseStageError BranchResourceStageVerificationError
  | ControlStateStageRevisionMismatch ControlStateStageRevision ControlStateStageRevision
  | StateBoundaryMapKeyMismatch StateBoundaryKey StateBoundaryKey
  | StateBoundaryEmptyFunction StateBoundaryKey
  | StateBoundaryUnknownFunction StateBoundaryKey Text
  | StateBoundaryUnknownBlock StateBoundaryKey BlockId
  | StateBoundaryEmptySlots StateBoundaryKey
  | StateSlotMapKeyMismatch StateBoundaryKey StateSlotKey StateSlotKey
  | StateProjectionMapKeyMismatch StateProjectionKey StateProjectionKey
  | StateProjectionUnknownBoundary StateProjectionKey StateBoundaryKey
  | StateProjectionKindMismatch StateProjectionKey StateBoundaryKind StateProjectionKind
  | StateProjectionUnknownFromBlock StateProjectionKey BlockId
  | StateProjectionEdgeLabelUnknown StateProjectionKey Text
  | StateProjectionEdgeTargetMismatch StateProjectionKey BlockId BlockId
  | StateProjectionBindingDomainMismatch StateProjectionKey (Set StateSlotKey) (Set StateSlotKey)
  | StateProjectionValueFunctionMismatch StateProjectionKey SystemsValueRef Text
  | StateProjectionUnknownValue StateProjectionKey SystemsValueRef
  | StateProjectionScopedLoanEscape StateProjectionKey SystemsValueRef
  | StateProjectionIncomingOwnerModeInvalid StateProjectionKey SystemsValueRef Mode
  | StateProjectionIncomingValueNotOwning StateProjectionKey SystemsValueRef SystemsValueRole
  | StateProjectionRestrictedSlotMissingOwner StateProjectionKey StateSlotKey SystemsValueRef
  | StateProjectionModeMismatch StateProjectionKey StateSlotKey Mode Mode
  | StateProjectionFixedSubjectUnknown StateProjectionKey StateSlotKey SourceSubjectKey
  | StateProjectionFixedSubjectMismatch StateProjectionKey StateSlotKey SourceSubjectKey SystemsValueRef
  | StateProjectionRestrictedOwnerDuplicated StateProjectionKey SystemsValueRef Int
  | StateProjectionUnaccountedLinearOwners StateProjectionKey (Set SystemsValueRef)
  | StateBoundaryProjectionShapeMismatch StateBoundaryKey StateBoundaryKind Int Int Int
  | ClosureCaptureMapKeyMismatch Text Text
  | ClosureCarrierDomainMismatch Text (Set CaptureOccurrenceKey) (Set CaptureOccurrenceKey)
  | ClosureRestrictedCaptureCardinality Text CaptureOccurrenceKey Int
  | ClosureRestrictedCarrierShared Text CaptureCarrierKey (Set CaptureOccurrenceKey)
  deriving (Eq, Show)

deriveControlStateStageRevision
  :: ControlStateStageBundle
  -> ControlStateStageRevision
deriveControlStateStageRevision bundle = ControlStateStageRevision
  ("phil.phase1.control-state-stage.canonical.v1:"
    <> canonicalSemanticForm (SemanticRecord (Map.fromList
      [ ("base_stage", SemanticAtom
          (unBranchResourceStageRevision
            (branchResourceStageRevision (controlStateStageBase bundle))))
      , ("boundaries", SemanticRecord (Map.fromList
          [ (unStateBoundaryKey key, semanticBoundary boundary)
          | (key, boundary) <- Map.toAscList (controlStateStageBoundaries bundle)
          ]))
      , ("projections", SemanticRecord (Map.fromList
          [ (unStateProjectionKey key, semanticProjection projection)
          | (key, projection) <- Map.toAscList (controlStateStageProjections bundle)
          ]))
      , ("closure_captures", SemanticRecord (Map.fromList
          [ (key, semanticClosureCapture projection)
          | (key, projection) <- Map.toAscList (controlStateStageClosureCaptures bundle)
          ]))
      ])))

makeControlStateStageBundle
  :: BranchResourceStageBundle
  -> Map StateBoundaryKey StateBoundaryContract
  -> Map StateProjectionKey StateProjection
  -> Map Text ClosureCaptureProjection
  -> ControlStateStageBundle
makeControlStateStageBundle base boundaries projections closureCaptures =
  provisional
    { controlStateStageRevision = deriveControlStateStageRevision provisional }
  where
    provisional = ControlStateStageBundle
      { controlStateStageBase = base
      , controlStateStageRevision = ControlStateStageRevision "pending"
      , controlStateStageBoundaries = boundaries
      , controlStateStageProjections = projections
      , controlStateStageClosureCaptures = closureCaptures
      }

verifyControlStateStageBundle
  :: ControlStateStageBundle
  -> Either ControlStateProjectionError ()
verifyControlStateStageBundle bundle = do
  mapLeft ControlStateBaseStageError $
    verifyBranchResourceStageBundle (controlStateStageBase bundle)
  requireEqual ControlStateStageRevisionMismatch
    (deriveControlStateStageRevision bundle)
    (controlStateStageRevision bundle)
  let subjectStage = subjectStageFromBranch (controlStateStageBase bundle)
      program = systemsArtifactProgram
        (phase1StageSystemsArtifact (subjectStageBase subjectStage))
      subjectIndex = Map.map subjectCorrespondenceSystemsValues
        (subjectStageCorrespondences subjectStage)
  mapM_ (checkBoundary program)
    (Map.toAscList (controlStateStageBoundaries bundle))
  mapM_ (checkProjectionMapKey bundle)
    (Map.toAscList (controlStateStageProjections bundle))
  mapM_ (checkBoundaryGroup program subjectIndex bundle)
    (Map.toAscList (controlStateStageBoundaries bundle))
  mapM_ checkClosureMapKey
    (Map.toAscList (controlStateStageClosureCaptures bundle))
  where
    checkClosureMapKey (key, projection) = do
      requireEqual ClosureCaptureMapKeyMismatch key (closureCaptureProjectionKey projection)
      checkClosureCaptureProjection projection

checkBoundary
  :: SystemsProgram
  -> (StateBoundaryKey, StateBoundaryContract)
  -> Either ControlStateProjectionError ()
checkBoundary program (key, boundary) = do
  requireEqual StateBoundaryMapKeyMismatch key (stateBoundaryKey boundary)
  if Text.null (stateBoundaryFunction boundary)
    then Left (StateBoundaryEmptyFunction key)
    else Right ()
  function <- case Map.lookup (stateBoundaryFunction boundary)
      (systemsProgramFunctions program) of
    Just value -> Right value
    Nothing -> Left (StateBoundaryUnknownFunction key (stateBoundaryFunction boundary))
  if Map.member (stateBoundaryTargetBlock boundary) (systemsFunctionBlocks function)
    then Right ()
    else Left (StateBoundaryUnknownBlock key (stateBoundaryTargetBlock boundary))
  if Map.null (stateBoundarySlots boundary)
    then Left (StateBoundaryEmptySlots key)
    else mapM_ checkSlot (Map.toAscList (stateBoundarySlots boundary))
  where
    checkSlot (slotKey, slot) =
      requireEqual (StateSlotMapKeyMismatch key) slotKey (stateSlotKey slot)

checkProjectionMapKey
  :: ControlStateStageBundle
  -> (StateProjectionKey, StateProjection)
  -> Either ControlStateProjectionError ()
checkProjectionMapKey bundle (key, projection) = do
  requireEqual StateProjectionMapKeyMismatch key (stateProjectionKey projection)
  case Map.lookup (stateProjectionBoundary projection)
      (controlStateStageBoundaries bundle) of
    Just _ -> Right ()
    Nothing -> Left (StateProjectionUnknownBoundary key (stateProjectionBoundary projection))

checkBoundaryGroup
  :: SystemsProgram
  -> Map SourceSubjectKey (Set SystemsValueRef)
  -> ControlStateStageBundle
  -> (StateBoundaryKey, StateBoundaryContract)
  -> Either ControlStateProjectionError ()
checkBoundaryGroup program subjectIndex bundle (key, boundary) =
  checkStateBoundaryProjections program subjectIndex boundary projections
  where
    projections =
      [ projection
      | projection <- Map.elems (controlStateStageProjections bundle)
      , stateProjectionBoundary projection == key
      ]

checkStateBoundaryProjections
  :: SystemsProgram
  -> Map SourceSubjectKey (Set SystemsValueRef)
  -> StateBoundaryContract
  -> [StateProjection]
  -> Either ControlStateProjectionError ()
checkStateBoundaryProjections program subjectIndex boundary projections = do
  mapM_ (checkStateProjection program subjectIndex boundary) projections
  let ordinaryCount = length
        [ () | projection <- projections
             , stateProjectionKind projection == OrdinaryJoinPredecessor ]
      initialCount = length
        [ () | projection <- projections
             , stateProjectionKind projection == LoopInitialEntry ]
      backedgeCount = length
        [ () | projection <- projections
             , stateProjectionKind projection == LoopBackedge ]
  case stateBoundaryKind boundary of
    OrdinaryJoinBoundary
      | ordinaryCount >= 2 && initialCount == 0 && backedgeCount == 0 -> Right ()
      | otherwise -> Left (StateBoundaryProjectionShapeMismatch
          (stateBoundaryKey boundary) OrdinaryJoinBoundary
          ordinaryCount initialCount backedgeCount)
    LoopStateBoundary
      | ordinaryCount == 0 && initialCount >= 1 && backedgeCount >= 1 -> Right ()
      | otherwise -> Left (StateBoundaryProjectionShapeMismatch
          (stateBoundaryKey boundary) LoopStateBoundary
          ordinaryCount initialCount backedgeCount)
  checkResourceScopeBranchDisposition
  where
    checkResourceScopeBranchDisposition =
      case ResourceScopeKernel.decideBranchDispositionByFacts
          terminalExcluded continuingExact of
        ResourceScopeKernel.BranchDispositionAcceptedDecision -> Right ()
        _ -> resourceScopeKernelInvariant "branch-disposition"

    terminalExcluded = all hasContinuingTarget projections
    continuingExact = all edgeTargetsBoundary projections

    hasContinuingTarget projection = case projectionBlock projection of
      Nothing -> False
      Just block -> not (Map.null (terminatorTargets (systemsBlockTerminator block)))

    edgeTargetsBoundary projection = case projectionBlock projection of
      Nothing -> False
      Just block ->
        Map.lookup (stateProjectionEdgeLabel projection)
          (terminatorTargets (systemsBlockTerminator block))
          == Just (stateBoundaryTargetBlock boundary)

    projectionBlock projection = do
      function <- Map.lookup (stateBoundaryFunction boundary)
        (systemsProgramFunctions program)
      Map.lookup (stateProjectionFromBlock projection)
        (systemsFunctionBlocks function)

checkStateProjection
  :: SystemsProgram
  -> Map SourceSubjectKey (Set SystemsValueRef)
  -> StateBoundaryContract
  -> StateProjection
  -> Either ControlStateProjectionError ()
checkStateProjection program subjectIndex boundary projection = do
  checkProjectionKind
  function <- case Map.lookup (stateBoundaryFunction boundary)
      (systemsProgramFunctions program) of
    Just value -> Right value
    Nothing -> Left (StateBoundaryUnknownFunction
      (stateBoundaryKey boundary) (stateBoundaryFunction boundary))
  fromBlock <- case Map.lookup (stateProjectionFromBlock projection)
      (systemsFunctionBlocks function) of
    Just value -> Right value
    Nothing -> Left (StateProjectionUnknownFromBlock
      (stateProjectionKey projection) (stateProjectionFromBlock projection))
  let targets = terminatorTargets (systemsBlockTerminator fromBlock)
  actualTarget <- case Map.lookup (stateProjectionEdgeLabel projection) targets of
    Just value -> Right value
    Nothing -> Left (StateProjectionEdgeLabelUnknown
      (stateProjectionKey projection) (stateProjectionEdgeLabel projection))
  requireEqual (StateProjectionEdgeTargetMismatch (stateProjectionKey projection))
    (stateBoundaryTargetBlock boundary) actualTarget
  let expectedSlots = Map.keysSet (stateBoundarySlots boundary)
      actualSlots = Map.keysSet (stateProjectionBindings projection)
  case Kernel.decideStateProjectionByFacts
      True (expectedSlots == actualSlots) True True True True True True True of
    Kernel.StateProjectionAcceptedDecision -> Right ()
    Kernel.StateSlotDomainDecision ->
      Left (StateProjectionBindingDomainMismatch (stateProjectionKey projection)
        expectedSlots actualSlots)
    _ -> kernelInvariant "state-slot-domain"
  mapM_ (checkIncoming function)
    (Map.toAscList (stateProjectionIncomingRestricted projection))
  mapM_ (checkBinding function)
    (Map.toAscList (stateProjectionBindings projection))
  checkRestrictedMultiplicity
  checkLinearCoverage
  checkResourceJoinKernel
  checkResourceScopeProjectionKernel function
  where
    projectionKey = stateProjectionKey projection

    checkProjectionKind =
      case Kernel.decideStateProjectionByFacts
          projectionKindExact True True True True True True True True of
        Kernel.StateProjectionAcceptedDecision -> Right ()
        Kernel.StateProjectionKindDecision ->
          Left (StateProjectionKindMismatch projectionKey
            (stateBoundaryKind boundary) (stateProjectionKind projection))
        _ -> kernelInvariant "state-projection-kind"

    projectionKindExact = case (stateBoundaryKind boundary, stateProjectionKind projection) of
      (OrdinaryJoinBoundary, OrdinaryJoinPredecessor) -> True
      (LoopStateBoundary, LoopInitialEntry) -> True
      (LoopStateBoundary, LoopBackedge) -> True
      _ -> False

    checkIncoming function (ref, mode) = do
      case Kernel.decideStateProjectionByFacts
          True True (mode /= Unrestricted) True True True True True True of
        Kernel.StateProjectionAcceptedDecision -> Right ()
        Kernel.StateRestrictedOwnerModeDecision ->
          Left (StateProjectionIncomingOwnerModeInvalid projectionKey ref mode)
        _ -> kernelInvariant "state-incoming-owner-mode"
      value <- lookupValue projectionKey function ref
      case systemsValueRole value of
        BorrowedSlice _ ->
          case Kernel.decideStateProjectionByFacts
              True True True True True True False True True of
            Kernel.StateScopedLoanEscapeDecision ->
              Left (StateProjectionScopedLoanEscape projectionKey ref)
            _ -> kernelInvariant "state-incoming-loan"
        role
          | isOwningRole role -> Right ()
          | otherwise -> Left (StateProjectionIncomingValueNotOwning projectionKey ref role)

    checkBinding function (slotKey, ref) = do
      slot <- case Map.lookup slotKey (stateBoundarySlots boundary) of
        Just value -> Right value
        Nothing -> Left (StateProjectionBindingDomainMismatch projectionKey
          (Map.keysSet (stateBoundarySlots boundary))
          (Map.keysSet (stateProjectionBindings projection)))
      value <- lookupValue projectionKey function ref
      case systemsValueRole value of
        BorrowedSlice _ ->
          case Kernel.decideStateProjectionByFacts
              True True True True True True False True True of
            Kernel.StateScopedLoanEscapeDecision ->
              Left (StateProjectionScopedLoanEscape projectionKey ref)
            _ -> kernelInvariant "state-binding-loan"
        _ -> Right ()
      let nativeModeResult = case stateSlotMode slot of
            Unrestricted ->
              case Map.lookup ref (stateProjectionIncomingRestricted projection) of
                Nothing -> Right ()
                Just actualMode -> Left
                  (StateProjectionModeMismatch projectionKey slotKey Unrestricted actualMode)
            expectedMode -> case Map.lookup ref (stateProjectionIncomingRestricted projection) of
              Nothing -> Left (StateProjectionRestrictedSlotMissingOwner projectionKey slotKey ref)
              Just actualMode -> requireEqual
                (StateProjectionModeMismatch projectionKey slotKey)
                expectedMode actualMode
      case Kernel.decideStateProjectionByFacts
          True True (nativeModeResult == Right ()) True True True True True True of
        Kernel.StateProjectionAcceptedDecision -> Right ()
        Kernel.StateRestrictedOwnerModeDecision -> nativeModeResult
        _ -> kernelInvariant "state-binding-mode"
      checkSubject slotKey ref (stateSlotSubjectRequirement slot)

    checkSubject _ _ AnyStateSubject = Right ()
    checkSubject slotKey ref (FixedStateSubject subject) =
      let nativeSubjectResult = case Map.lookup subject subjectIndex of
            Nothing -> Left (StateProjectionFixedSubjectUnknown projectionKey slotKey subject)
            Just refs
              | Set.member ref refs -> Right ()
              | otherwise -> Left
                  (StateProjectionFixedSubjectMismatch projectionKey slotKey subject ref)
      in case Kernel.decideStateProjectionByFacts
          True True True (nativeSubjectResult == Right ()) True True True True True of
        Kernel.StateProjectionAcceptedDecision -> Right ()
        Kernel.StateFixedSubjectDecision -> nativeSubjectResult
        _ -> kernelInvariant "state-fixed-subject"

    checkRestrictedMultiplicity =
      let nativeMultiplicity = case
            [ (ref, count)
            | (ref, count) <- Map.toAscList counts
            , Map.member ref (stateProjectionIncomingRestricted projection)
            , count > 1
            ] of
            [] -> Right ()
            (ref, count) : _ -> Left
              (StateProjectionRestrictedOwnerDuplicated projectionKey ref count)
      in case Kernel.decideStateProjectionByFacts
          True True True True (nativeMultiplicity == Right ()) True True True True of
        Kernel.StateProjectionAcceptedDecision -> Right ()
        Kernel.StateRestrictedOwnerUniqueDecision -> nativeMultiplicity
        _ -> kernelInvariant "state-restricted-unique"
      where
        counts = Map.fromListWith (+)
          [ (ref, 1 :: Int)
          | ref <- Map.elems (stateProjectionBindings projection)
          ]

    checkLinearCoverage =
      let boundRefs = Set.fromList (Map.elems (stateProjectionBindings projection))
          incomingLinear = Set.fromList
            [ ref
            | (ref, mode) <- Map.toAscList (stateProjectionIncomingRestricted projection)
            , mode == Linear
            ]
          unaccounted = Set.difference incomingLinear boundRefs
      in case Kernel.decideStateProjectionByFacts
          True True True True True (Set.null unaccounted) True True True of
        Kernel.StateProjectionAcceptedDecision -> Right ()
        Kernel.StateLinearOwnersCoveredDecision ->
          Left (StateProjectionUnaccountedLinearOwners projectionKey unaccounted)
        _ -> kernelInvariant "state-linear-coverage"

    checkResourceScopeProjectionKernel function = do
      scopeValues <- mapM (lookupValue projectionKey function) scopedRefs
      case ResourceScopeKernel.decideScopedBoundaryByFacts
          True (all lexicalLoanClosed scopeValues) of
        ResourceScopeKernel.ScopedBoundaryAcceptedDecision -> Right ()
        _ -> resourceScopeKernelInvariant "scoped-boundary"
      case ResourceScopeKernel.decideAffineProjectionByFact
          explicitAffineCarriers of
        ResourceScopeKernel.AffineProjectionAcceptedDecision -> Right ()
        _ -> resourceScopeKernelInvariant "affine-projection"
      where
        scopedRefs = Set.toList (Set.fromList
          (Map.keys (stateProjectionIncomingRestricted projection)
            <> Map.elems (stateProjectionBindings projection)))
        lexicalLoanClosed value = case systemsValueRole value of
          BorrowedSlice _ -> False
          _ -> True
        explicitAffineCarriers = all
          (\(slotKey, slot) ->
            stateSlotMode slot /= Affine
              || Map.member slotKey (stateProjectionBindings projection))
          (Map.toAscList (stateBoundarySlots boundary))

    checkResourceJoinKernel =
      case ResourceJoinKernel.decideResourceProjectionByFacts
          allIncomingLinearExactlyOnceBound
          noInventedLinearOwners
          allBoundLinearSubjectsAdmissible of
        ResourceJoinKernel.ResourceProjectionAcceptedDecision -> Right ()
        _ -> kernelInvariant "resource-join"
      where
        bindingCounts = Map.fromListWith (+)
          [ (ref, 1 :: Int)
          | ref <- Map.elems (stateProjectionBindings projection)
          ]
        incomingLinear = Set.fromList
          [ ref
          | (ref, mode) <- Map.toAscList
              (stateProjectionIncomingRestricted projection)
          , mode == Linear
          ]
        linearBindings =
          [ (slotKey, ref)
          | (slotKey, ref) <- Map.toAscList
              (stateProjectionBindings projection)
          , Just slot <- [Map.lookup slotKey (stateBoundarySlots boundary)]
          , stateSlotMode slot == Linear
          ]
        allIncomingLinearExactlyOnceBound = all
          (\ref -> Map.findWithDefault 0 ref bindingCounts == 1)
          (Set.toList incomingLinear)
        noInventedLinearOwners = all
          (\(_, ref) ->
            Map.lookup ref (stateProjectionIncomingRestricted projection)
              == Just Linear)
          linearBindings
        allBoundLinearSubjectsAdmissible = all subjectAdmissible linearBindings
        subjectAdmissible (slotKey, ref) =
          case Map.lookup slotKey (stateBoundarySlots boundary) of
            Nothing -> False
            Just slot -> case stateSlotSubjectRequirement slot of
              AnyStateSubject -> True
              FixedStateSubject subject ->
                maybe False (Set.member ref) (Map.lookup subject subjectIndex)

checkClosureCaptureProjection
  :: ClosureCaptureProjection
  -> Either ControlStateProjectionError ()
checkClosureCaptureProjection projection = do
  requireEqual (ClosureCarrierDomainMismatch key)
    (Map.keysSet captures) (Map.keysSet carriers)
  mapM_ checkRestricted (Map.toAscList captures)
  checkCarrierSharing
  where
    key = closureCaptureProjectionKey projection
    captures = closureCaptureProjectionCaptures projection
    carriers = closureCaptureProjectionCarriers projection

    checkRestricted (captureKey, semantic)
      | callableCaptureSemanticMode semantic == Unrestricted = Right ()
      | otherwise =
          let count = length (Map.findWithDefault [] captureKey carriers)
          in case Kernel.decideStateProjectionByFacts
              True True True True True True True (count == 1) True of
            Kernel.StateProjectionAcceptedDecision -> Right ()
            Kernel.ClosureCaptureCarrierDecision ->
              Left (ClosureRestrictedCaptureCardinality key captureKey count)
            _ -> kernelInvariant "closure-capture-carrier"

    checkCarrierSharing =
      let nativeSharing = case
            [ (carrier, owners)
            | (carrier, owners) <- Map.toAscList reverseBindings
            , Set.size owners > 1
            ] of
            [] -> Right ()
            (carrier, owners) : _ -> Left
              (ClosureRestrictedCarrierShared key carrier owners)
      in case Kernel.decideStateProjectionByFacts
          True True True True True True True True (nativeSharing == Right ()) of
        Kernel.StateProjectionAcceptedDecision -> Right ()
        Kernel.ClosureCarrierSharingDecision -> nativeSharing
        _ -> kernelInvariant "closure-carrier-sharing"
      where
        reverseBindings = Map.fromListWith Set.union
          [ (carrier, Set.singleton captureKey)
          | (captureKey, semantic) <- Map.toAscList captures
          , callableCaptureSemanticMode semantic /= Unrestricted
          , carrier <- Map.findWithDefault [] captureKey carriers
          ]

lookupValue
  :: StateProjectionKey
  -> SystemsFunction
  -> SystemsValueRef
  -> Either ControlStateProjectionError SystemsValue
lookupValue projectionKey function ref
  | systemsValueRefFunction ref /= systemsFunctionName function =
      Left (StateProjectionValueFunctionMismatch projectionKey ref (systemsFunctionName function))
  | otherwise = case Map.lookup (systemsValueRefValue ref) (systemsFunctionValues function) of
      Just value -> Right value
      Nothing -> Left (StateProjectionUnknownValue projectionKey ref)

terminatorTargets :: SystemsTerminator -> Map Text BlockId
terminatorTargets terminator = case terminator of
  TermJump target -> Map.singleton "jump" target
  TermBranch _ trueTarget falseTarget -> Map.fromList
    [("true", trueTarget), ("false", falseTarget)]
  TermRecognize { recognizeSuccess = success, recognizeFailure = failure } ->
    successFailure success failure
  TermRuntimeCheck { checkSuccess = success, checkFailure = failure } ->
    successFailure success failure
  TermReceiveExact { exactSuccess = success, exactFailure = failure } ->
    successFailure success failure
  TermSendExact { sendExactSuccess = success, sendExactFailure = failure } ->
    successFailure success failure
  TermStore { storeSuccess = success, storeFailure = failure } ->
    successFailure success failure
  TermSessionOffer { sessionOfferArms = arms } ->
    Map.map choiceArmTarget arms
  TermRuntimeChoice { runtimeChoiceArms = arms } ->
    Map.map runtimeChoiceArmTarget arms
  _ -> Map.empty
  where
    successFailure success failure = Map.fromList
      [("success", success), ("failure", failure)]

isOwningRole :: SystemsValueRole -> Bool
isOwningRole role = case role of
  TransportHandle -> True
  PendingIngress _ -> True
  FrameOwner _ -> True
  OwnedBuffer _ -> True
  _ -> False

subjectStageFromBranch :: BranchResourceStageBundle -> SubjectStageBundle
subjectStageFromBranch =
  providerCallStageBase . authorityEffectStageBase . branchResourceStageBase

semanticBoundary :: StateBoundaryContract -> SemanticForm
semanticBoundary boundary = SemanticRecord (Map.fromList
  [ ("key", SemanticAtom (unStateBoundaryKey (stateBoundaryKey boundary)))
  , ("kind", SemanticAtom (boundaryKindText (stateBoundaryKind boundary)))
  , ("function", SemanticAtom (stateBoundaryFunction boundary))
  , ("target", SemanticAtom (unBlockId (stateBoundaryTargetBlock boundary)))
  , ("slots", SemanticRecord (Map.fromList
      [ (unStateSlotKey key, semanticSlot slot)
      | (key, slot) <- Map.toAscList (stateBoundarySlots boundary)
      ]))
  ])

semanticSlot :: StateSlotContract -> SemanticForm
semanticSlot slot = SemanticRecord (Map.fromList
  [ ("key", SemanticAtom (unStateSlotKey (stateSlotKey slot)))
  , ("mode", SemanticAtom (modeText (stateSlotMode slot)))
  , ("subject", semanticSubjectRequirement (stateSlotSubjectRequirement slot))
  ])

semanticProjection :: StateProjection -> SemanticForm
semanticProjection projection = SemanticRecord (Map.fromList
  [ ("key", SemanticAtom (unStateProjectionKey (stateProjectionKey projection)))
  , ("kind", SemanticAtom (projectionKindText (stateProjectionKind projection)))
  , ("boundary", SemanticAtom (unStateBoundaryKey (stateProjectionBoundary projection)))
  , ("from", SemanticAtom (unBlockId (stateProjectionFromBlock projection)))
  , ("edge", SemanticAtom (stateProjectionEdgeLabel projection))
  , ("incoming_restricted", SemanticRecord (Map.fromList
      [ (systemsRefKey ref, SemanticAtom (modeText mode))
      | (ref, mode) <- Map.toAscList (stateProjectionIncomingRestricted projection)
      ]))
  , ("bindings", SemanticRecord (Map.fromList
      [ (unStateSlotKey key, semanticSystemsRef ref)
      | (key, ref) <- Map.toAscList (stateProjectionBindings projection)
      ]))
  ])

semanticClosureCapture :: ClosureCaptureProjection -> SemanticForm
semanticClosureCapture projection = SemanticRecord (Map.fromList
  [ ("key", SemanticAtom (closureCaptureProjectionKey projection))
  , ("captures", SemanticRecord (Map.fromList
      [ (unCaptureOccurrenceKey key, semanticCapture semantic)
      | (key, semantic) <- Map.toAscList (closureCaptureProjectionCaptures projection)
      ]))
  , ("carriers", SemanticRecord (Map.fromList
      [ (unCaptureOccurrenceKey key, SemanticOrdered
          [ SemanticAtom (unCaptureCarrierKey carrier)
          | carrier <- sort carrierList
          ])
      | (key, carrierList) <- Map.toAscList (closureCaptureProjectionCarriers projection)
      ]))
  ])

semanticCapture :: CallableCaptureSemantic -> SemanticForm
semanticCapture semantic = SemanticRecord (Map.fromList
  [ ("mode", SemanticAtom (modeText (callableCaptureSemanticMode semantic)))
  , ("subject", maybe (SemanticAtom "none") SemanticAtom
      (callableCaptureSemanticSubject semantic))
  , ("authority", SemanticUnordered (Set.map
      (SemanticAtom . unCallableAuthorityRequirement)
      (callableCaptureSemanticAuthority semantic)))
  ])

semanticSubjectRequirement :: StateSubjectRequirement -> SemanticForm
semanticSubjectRequirement requirement = case requirement of
  AnyStateSubject -> SemanticAtom "any"
  FixedStateSubject subject -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "fixed")
    , ("subject", SemanticAtom (unSourceSubjectKey subject))
    ])

semanticSystemsRef :: SystemsValueRef -> SemanticForm
semanticSystemsRef ref = SemanticRecord (Map.fromList
  [ ("function", SemanticAtom (systemsValueRefFunction ref))
  , ("value", SemanticAtom (unValueId (systemsValueRefValue ref)))
  ])

systemsRefKey :: SystemsValueRef -> Text
systemsRefKey ref = systemsValueRefFunction ref <> "::" <> unValueId (systemsValueRefValue ref)

boundaryKindText :: StateBoundaryKind -> Text
boundaryKindText kind = case kind of
  OrdinaryJoinBoundary -> "join"
  LoopStateBoundary -> "loop"

projectionKindText :: StateProjectionKind -> Text
projectionKindText kind = case kind of
  OrdinaryJoinPredecessor -> "join-predecessor"
  LoopInitialEntry -> "loop-initial"
  LoopBackedge -> "loop-backedge"

modeText :: Mode -> Text
modeText mode = case mode of
  Unrestricted -> "unrestricted"
  Affine -> "affine"
  Linear -> "linear"

requireEqual :: Eq a => (a -> a -> e) -> a -> a -> Either e ()
requireEqual mkError expected actual
  | expected == actual = Right ()
  | otherwise = Left (mkError expected actual)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right

kernelInvariant :: String -> Either e a
kernelInvariant label =
  error ("SystemsControlPreservationKernel mismatch: " <> label)

resourceScopeKernelInvariant :: String -> Either e a
resourceScopeKernelInvariant label =
  error ("ResourceScopeKernel mismatch: " <> label)
