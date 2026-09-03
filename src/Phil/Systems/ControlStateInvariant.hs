{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.ControlStateInvariant
  ( StateInvariantContract (..)
  , StateInvariantSlotWitness (..)
  , StateInvariantPredecessor (..)
  , StateInvariantError (..)
  , checkStateBoundaryInvariant
  ) where

import Control.Monad (foldM)
import Data.List (sortOn)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Text as Text
import Phil.Core.Checker (CheckState (..))
import Phil.Core.Context (ResourceContext (..))
import Phil.Core.Decision
  ( AssumptionRef (..)
  , CertificateError
  , SolverAssumption (..)
  , checkDecisionCertificate
  , proposeDecisionCertificate
  )
import Phil.Core.Focusing
  ( FocusMechanism (..)
  , FocusPlan (..)
  , FocusedRequirement (..)
  , FocusingError
  , canonicalizeProposition
  , focusProposition
  )
import Phil.Core.Refinement (bindingEvidencePropositions)
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax
  ( Name
  , ObligationId (..)
  , Proposition (..)
  , RefTerm (..)
  )
import Phil.Systems.ControlStateProjection
  ( ControlStateProjectionError
  , StateBoundaryContract (..)
  , StateBoundaryKey
  , StateProjection (..)
  , StateProjectionKey (..)
  , StateSlotKey
  , checkStateBoundaryProjections
  )
import Phil.Systems.IR (SystemsProgram)
import Phil.Systems.SubjectCorrespondence
  ( SourceSubjectKey
  , SystemsValueRef
  )
import qualified ResourceInvariantKernel as ResourceInvariantKernel

-- | Logical invariant layered over one already-checked structural state
-- boundary.  The binder map names the logical variables corresponding to the
-- exact state slots; it does not create another state telescope.
data StateInvariantContract = StateInvariantContract
  { stateInvariantBoundary :: StateBoundaryKey
  , stateInvariantBinders :: Map StateSlotKey Name
  , stateInvariantProposition :: Proposition
  }
  deriving (Eq, Ord, Show)

-- | Refinement-visible term for the exact Systems value feeding one state
-- slot on one predecessor.  The checker verifies the value reference against
-- the structural projection before using the term in the invariant.
data StateInvariantSlotWitness = StateInvariantSlotWitness
  { stateInvariantSlotValue :: SystemsValueRef
  , stateInvariantSlotTerm :: RefTerm
  }
  deriving (Eq, Ord, Show)

-- | Per-predecessor logical evidence state.  Evidence is deliberately kept
-- separate for every edge so a proof available on one branch cannot become an
-- unconditional fact at the join or loop header.
data StateInvariantPredecessor = StateInvariantPredecessor
  { stateInvariantPredecessorProjection :: StateProjectionKey
  , stateInvariantPredecessorSlots :: Map StateSlotKey StateInvariantSlotWitness
  , stateInvariantPredecessorState :: CheckState
  }
  deriving (Eq, Show)

data StateInvariantError
  = StateInvariantStructuralError ControlStateProjectionError
  | StateInvariantBoundaryMismatch StateBoundaryKey StateBoundaryKey
  | StateInvariantBinderDomainMismatch
      StateBoundaryKey
      (Set StateSlotKey)
      (Set StateSlotKey)
  | StateInvariantDuplicateBinder StateBoundaryKey Name
  | StateInvariantDuplicateProjectionKey StateProjectionKey
  | StateInvariantPredecessorDomainMismatch
      StateBoundaryKey
      (Set StateProjectionKey)
      (Set StateProjectionKey)
  | StateInvariantPredecessorKeyMismatch
      StateProjectionKey
      StateProjectionKey
  | StateInvariantSlotDomainMismatch
      StateProjectionKey
      (Set StateSlotKey)
      (Set StateSlotKey)
  | StateInvariantSlotValueMismatch
      StateProjectionKey
      StateSlotKey
      SystemsValueRef
      SystemsValueRef
  | StateInvariantFocusingError StateProjectionKey FocusingError
  | StateInvariantDecisionUnavailable StateProjectionKey Proposition
  | StateInvariantCertificateError StateProjectionKey CertificateError
  | StateInvariantExplicitMechanismRequired StateProjectionKey Proposition
  deriving (Eq, Show)

-- | Check one logical JoinContract/LoopContract invariant over exactly the same
-- predecessor set admitted by the structural RES-009 state projection.  The
-- structural telescope is checked first.  Only then is the invariant
-- instantiated with each predecessor's exact state-slot witnesses and proved
-- independently in that predecessor's CheckState.
checkStateBoundaryInvariant
  :: StaticContext
  -> SystemsProgram
  -> Map SourceSubjectKey (Set SystemsValueRef)
  -> StateBoundaryContract
  -> [StateProjection]
  -> StateInvariantContract
  -> Map StateProjectionKey StateInvariantPredecessor
  -> Either StateInvariantError ()
checkStateBoundaryInvariant staticContext program subjectIndex boundary projections invariant predecessors = do
  mapLeft StateInvariantStructuralError $
    checkStateBoundaryProjections program subjectIndex boundary projections
  requireEqual StateInvariantBoundaryMismatch
    (stateBoundaryKey boundary)
    (stateInvariantBoundary invariant)
  let expectedSlots = Map.keysSet (stateBoundarySlots boundary)
      actualBinderSlots = Map.keysSet (stateInvariantBinders invariant)
  requireEqual (StateInvariantBinderDomainMismatch (stateBoundaryKey boundary))
    expectedSlots actualBinderSlots
  case firstDuplicate (Map.elems (stateInvariantBinders invariant)) of
    Just binder -> Left (StateInvariantDuplicateBinder (stateBoundaryKey boundary) binder)
    Nothing -> Right ()
  case firstDuplicate (map stateProjectionKey projections) of
    Just key -> Left (StateInvariantDuplicateProjectionKey key)
    Nothing -> Right ()
  let expectedPredecessors = Set.fromList (map stateProjectionKey projections)
      actualPredecessors = Map.keysSet predecessors
  requireEqual (StateInvariantPredecessorDomainMismatch (stateBoundaryKey boundary))
    expectedPredecessors actualPredecessors
  establishedProjectionKeys <- mapM checkOne (sortOn stateProjectionKey projections)
  let predecessorsDistinct =
        firstDuplicate (map stateProjectionKey projections) == Nothing
      -- This fact is sequenced only after the real structural checker above
      -- returned Right ().  No structural success is fabricated here.
      structuralAccepted = True
      expectedSlotsForKernel = Map.keysSet (stateBoundarySlots boundary)
      witnessesExact = all
        (\projection ->
          case Map.lookup (stateProjectionKey projection) predecessors of
            Nothing -> False
            Just predecessor ->
              Map.keysSet (stateInvariantPredecessorSlots predecessor)
                == expectedSlotsForKernel)
        projections
      invariantEstablished =
        Set.fromList establishedProjectionKeys == expectedPredecessors
  case ResourceInvariantKernel.decideInvariantBoundaryByFacts
      predecessorsDistinct structuralAccepted witnessesExact invariantEstablished of
    ResourceInvariantKernel.InvariantBoundaryAcceptedDecision -> Right ()
    _ -> resourceInvariantKernelInvariant
  where
    checkOne projection = do
      let projectionKey = stateProjectionKey projection
      predecessor <- case Map.lookup projectionKey predecessors of
        Just value -> Right value
        Nothing -> Left (StateInvariantPredecessorDomainMismatch
          (stateBoundaryKey boundary)
          (Set.fromList (map stateProjectionKey projections))
          (Map.keysSet predecessors))
      requireEqual StateInvariantPredecessorKeyMismatch
        projectionKey
        (stateInvariantPredecessorProjection predecessor)
      let expectedSlots = Map.keysSet (stateBoundarySlots boundary)
          actualSlots = Map.keysSet (stateInvariantPredecessorSlots predecessor)
      requireEqual (StateInvariantSlotDomainMismatch projectionKey)
        expectedSlots actualSlots
      mapM_ (checkSlotWitness projection predecessor)
        (Map.toAscList (stateInvariantPredecessorSlots predecessor))
      let terms = Map.map stateInvariantSlotTerm
            (stateInvariantPredecessorSlots predecessor)
          instantiated = instantiateInvariant
            (stateInvariantBinders invariant)
            terms
            (stateInvariantProposition invariant)
      establishInvariant
        staticContext
        projectionKey
        (stateInvariantPredecessorState predecessor)
        instantiated
      Right projectionKey

checkSlotWitness
  :: StateProjection
  -> StateInvariantPredecessor
  -> (StateSlotKey, StateInvariantSlotWitness)
  -> Either StateInvariantError ()
checkSlotWitness projection _ (slotKey, witness) =
  case Map.lookup slotKey (stateProjectionBindings projection) of
    Nothing -> Left (StateInvariantSlotDomainMismatch
      (stateProjectionKey projection)
      (Map.keysSet (stateProjectionBindings projection))
      Set.empty)
    Just expectedRef -> requireEqual
      (StateInvariantSlotValueMismatch (stateProjectionKey projection) slotKey)
      expectedRef
      (stateInvariantSlotValue witness)

establishInvariant
  :: StaticContext
  -> StateProjectionKey
  -> CheckState
  -> Proposition
  -> Either StateInvariantError ()
establishInvariant staticContext projectionKey state proposition = do
  plan <- mapLeft (StateInvariantFocusingError projectionKey) $
    focusProposition staticContext state proposition
  baseAssumptions <- evidenceAssumptions staticContext projectionKey state
  (assumptions, _) <- foldM
    (establishPrerequisite projectionKey state)
    (baseAssumptions, 1 :: Int)
    (focusPrerequisites plan)
  establishRequirement projectionKey state assumptions (focusGoal plan)

establishPrerequisite
  :: StateProjectionKey
  -> CheckState
  -> ([SolverAssumption], Int)
  -> FocusedRequirement
  -> Either StateInvariantError ([SolverAssumption], Int)
establishPrerequisite projectionKey state (assumptions, index) requirement = do
  establishRequirement projectionKey state assumptions requirement
  let prerequisiteId = ObligationId
        ("res013."
          <> unStateProjectionKey projectionKey
          <> ".prerequisite."
          <> Text.pack (show index))
      prerequisite = SolverAssumption
        { solverAssumptionRef = PrerequisiteFact prerequisiteId
        , solverAssumptionProposition = focusedCanonical requirement
        }
  Right (prerequisite : assumptions, index + 1)

establishRequirement
  :: StateProjectionKey
  -> CheckState
  -> [SolverAssumption]
  -> FocusedRequirement
  -> Either StateInvariantError ()
establishRequirement projectionKey state assumptions requirement =
  case focusedMechanism requirement of
    FocusByDefinition -> Right ()
    FocusByEvidence _ -> Right ()
    FocusNeedsExplicitMechanism -> Left
      (StateInvariantExplicitMechanismRequired
        projectionKey
        (focusedCanonical requirement))
    FocusNeedsDecisionProcedure ->
      case proposeDecisionCertificate state assumptions (focusedCanonical requirement) of
        Nothing -> Left
          (StateInvariantDecisionUnavailable
            projectionKey
            (focusedCanonical requirement))
        Just certificate -> mapLeft (StateInvariantCertificateError projectionKey) $
          checkDecisionCertificate
            state
            assumptions
            (focusedCanonical requirement)
            certificate

evidenceAssumptions
  :: StaticContext
  -> StateProjectionKey
  -> CheckState
  -> Either StateInvariantError [SolverAssumption]
evidenceAssumptions staticContext projectionKey state =
  fmap concat $ mapM assumptionsForBinding
    (Map.toAscList (unrestrictedBindings (resourceContext state)))
  where
    assumptionsForBinding (bindingName, bindingType) =
      mapM (makeAssumption bindingName) $ zip [0 ..]
        (bindingEvidencePropositions bindingName bindingType)

    makeAssumption bindingName (index, proposition) = do
      (canonical, _) <- mapLeft (StateInvariantFocusingError projectionKey) $
        canonicalizeProposition staticContext state proposition
      Right SolverAssumption
        { solverAssumptionRef = EvidenceFact bindingName index
        , solverAssumptionProposition = canonical
        }

instantiateInvariant
  :: Map StateSlotKey Name
  -> Map StateSlotKey RefTerm
  -> Proposition
  -> Proposition
instantiateInvariant binders terms = substitutePropositionSimultaneously replacements
  where
    replacements = Map.fromList
      [ (binder, term)
      | (slotKey, binder) <- Map.toAscList binders
      , Just term <- [Map.lookup slotKey terms]
      ]

substitutePropositionSimultaneously
  :: Map Name RefTerm
  -> Proposition
  -> Proposition
substitutePropositionSimultaneously replacements proposition =
  case proposition of
    Truth -> Truth
    Falsehood -> Falsehood
    Equal left right -> Equal (term left) (term right)
    NotEqual left right -> NotEqual (term left) (term right)
    LessThan left right -> LessThan (term left) (term right)
    LessEqual left right -> LessEqual (term left) (term right)
    Member value collection -> Member (term value) (term collection)
    Disjoint left right -> Disjoint (term left) (term right)
    Conjunction left right -> Conjunction (recur left) (recur right)
    Disjunction left right -> Disjunction (recur left) (recur right)
    Negation inner -> Negation (recur inner)
    Atom claim arguments -> Atom claim (map term arguments)
  where
    term = substituteTermSimultaneously replacements
    recur = substitutePropositionSimultaneously replacements

substituteTermSimultaneously
  :: Map Name RefTerm
  -> RefTerm
  -> RefTerm
substituteTermSimultaneously replacements refTerm =
  case refTerm of
    RefVar name -> Map.findWithDefault refTerm name replacements
    RefField base field sort -> RefField (recur base) field sort
    RefLen value -> RefLen (recur value)
    RefToNat value -> RefToNat (recur value)
    RefAdd left right -> RefAdd (recur left) (recur right)
    RefSub left right -> RefSub (recur left) (recur right)
    RefScale coefficient value -> RefScale coefficient (recur value)
    _ -> refTerm
  where
    recur = substituteTermSimultaneously replacements

resourceInvariantKernelInvariant :: a
resourceInvariantKernelInvariant =
  error "ResourceInvariantKernel mismatch: accepted invariant boundary rejected"

firstDuplicate :: Ord a => [a] -> Maybe a
firstDuplicate = go Set.empty
  where
    go _ [] = Nothing
    go seen (value : rest)
      | Set.member value seen = Just value
      | otherwise = go (Set.insert value seen) rest

requireEqual :: Eq a => (a -> a -> e) -> a -> a -> Either e ()
requireEqual mkError expected actual
  | expected == actual = Right ()
  | otherwise = Left (mkError expected actual)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
