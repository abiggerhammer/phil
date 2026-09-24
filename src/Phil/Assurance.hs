module Phil.Assurance
  ( OriginalCheckEventError (..)
  , resolveOriginalCheckEvent
  , handoffOriginalCheckEvent
  , module Phil.Assurance.Types
  , module Phil.Assurance.Handoff
  , module Phil.Assurance.Verify
  , module Phil.Assurance.Phase0
  , module Phil.Assurance.Rocq
  , module Phil.Assurance.RocqRecognizedRecord
  , module Phil.Assurance.RocqExactReceive
  , module Phil.Assurance.RocqDigestValidation
  , module Phil.Assurance.RocqStorage
  ) where

import Control.Monad (foldM, unless)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Phil.Assurance.Handoff
import Phil.Assurance.Phase0
import Phil.Assurance.Rocq
import Phil.Assurance.RocqDigestValidation
import Phil.Assurance.RocqExactReceive
import Phil.Assurance.RocqRecognizedRecord
import Phil.Assurance.RocqStorage
import Phil.Assurance.Types
import Phil.Assurance.Verify
import Phil.Core.Checker
  ( CheckState (..)
  , LogicalSubjectSupport (..)
  )
import qualified Phil.Core.Discharge as Discharge
import Phil.Core.Refinement
  ( EvidenceUse (..)
  , ResidualSpec (..)
  , normalizeProposition
  , propositionMentions
  , substituteProposition
  )
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax
  ( Name
  , Obligation (..)
  , ObligationId
  , Proposition
  , RefTerm
  , Ty (..)
  )
import Phil.Core.Value (ValueResult (..))

-- | Failure while rebasing one actual residualizing value-check event onto the
-- resolver/assurance path.  This adapter deliberately starts from the returned
-- 'ValueResult' rather than from a reconstructed pending-obligation map: the
-- checked refinement type, concrete logical subject, exact evidence-use
-- inventory, emitted obligation records, and durable logical typing support all
-- have to agree before the original event is allowed into assurance handoff.
data OriginalCheckEventError
  = OriginalCheckEventExpectedRefinement Ty
  | OriginalCheckEventSubjectNotVisible Name
  | OriginalCheckEventResidualMissing ObligationId
  | OriginalCheckEventResidualRecordMismatch ObligationId Proposition Proposition
  | OriginalCheckEventResidualMetadataMismatch ObligationId ResidualSpec Obligation
  | OriginalCheckEventLogicalSupportMissing ObligationId
  | OriginalCheckEventLogicalSupportMismatch ObligationId Obligation Obligation
  | OriginalCheckEventLogicalTypeConflict Name Ty Ty
  | OriginalCheckEventDischargeError Discharge.DischargeError
  | OriginalCheckEventResidualCoverageMismatch (Set ObligationId) (Set ObligationId)
  | OriginalCheckEventResidualInventoryMismatch (Set ObligationId) (Set ObligationId)
  | OriginalCheckEventResolvedPropositionMismatch ObligationId Proposition Proposition
  | OriginalCheckEventHandoffError HandoffError
  deriving (Eq, Show)

-- | Resolve the exact original check event represented by a residualizing
-- 'ValueResult'.  In particular, do not resolve each normalized pending map
-- entry as an independent root: doing so loses a definitionally discharged
-- parent such as @(a-b)==(a-b)@ while retaining only its subtraction
-- prerequisite.
--
-- The supplied 'ResidualSpec' is not trusted as a parallel reconstruction. Its
-- metadata is checked against every residual actually returned by the value
-- checker, and the resulting original-event tree must cover exactly the
-- pending nodes from that tree which survive in the returned checker state.
-- Logical subject typing is rebuilt only from the exact residual supports
-- captured by the checker.  It is installed in a temporary resolver view and
-- never restores ownership or changes the returned resource state.
resolveOriginalCheckEvent
  :: StaticContext
  -> Discharge.DischargePolicy
  -> ResidualSpec
  -> ValueResult
  -> Either OriginalCheckEventError Discharge.ResolvedObligation
resolveOriginalCheckEvent staticContext policy spec result = do
  required <- originalRequiredProposition result
  let state = valueResultState result
      residualUses =
        [ (obligationId', proposition)
        | EvidenceResidual obligationId' proposition <- valueResultEvidence result
        ]
      evidenceResidualIds = Set.fromList (map fst residualUses)
      root = Obligation
        { obligationId = residualObligationId spec
        , obligationProposition = required
        , obligationOrigin = residualOrigin spec
        , obligationScope = residualScope spec
        , obligationRequiredPoint = residualRequiredPoint spec
        }
  residualRecords <- mapM (validateResidualRecord state spec) residualUses
  logicalBindings <- mergeLogicalBindings
    [ logicalSupportBindings support
    | (_, support) <- residualRecords
    ]
  liveUnrestricted <- mergeLogicalBindings
    [ logicalSupportUnrestrictedBindings support
    | (_, support) <- residualRecords
    ]
  let rootSupport = LogicalSubjectSupport
        { logicalSupportObligation = root
        , logicalSupportBindings = logicalBindings
        , logicalSupportUnrestrictedBindings = liveUnrestricted
        }
      resolverState
        | null residualUses = state
        | otherwise = state
            { residualLogicalSubjects = Map.insert
                (obligationId root)
                rootSupport
                (residualLogicalSubjects state)
            }
  resolved <- mapLeft OriginalCheckEventDischargeError $
    Discharge.resolveObligation staticContext resolverState policy root
  let resolvedById = flattenResolved resolved
      resolvedIds = Map.keysSet resolvedById
  unless (evidenceResidualIds `Set.isSubsetOf` resolvedIds) $
    Left
      (OriginalCheckEventResidualCoverageMismatch
        evidenceResidualIds
        resolvedIds)
  let pendingResolvedIds =
        Map.keysSet (residualObligations state) `Set.intersection` resolvedIds
  unless (pendingResolvedIds == evidenceResidualIds) $
    Left
      (OriginalCheckEventResidualInventoryMismatch
        pendingResolvedIds
        evidenceResidualIds)
  mapM_ (validateResolvedResidual resolvedById) residualUses
  Right resolved

-- | Produce the immutable assurance handoff from the exact original check
-- event.  Certificate EvidenceFact identity remains explicit and fail-closed;
-- direct named-evidence authority is still attached by the existing exact
-- event/name authority step before final manifest closure.
handoffOriginalCheckEvent
  :: HandoffConfig
  -> Map (Name, Int) EvidenceEntryId
  -> StaticContext
  -> Discharge.DischargePolicy
  -> ResidualSpec
  -> ValueResult
  -> Either OriginalCheckEventError [LedgerHandoff]
handoffOriginalCheckEvent config evidenceIds staticContext policy spec result = do
  resolved <- resolveOriginalCheckEvent staticContext policy spec result
  mapLeft OriginalCheckEventHandoffError $
    handoffResolvedObligationWithEvidence config evidenceIds resolved

originalRequiredProposition
  :: ValueResult
  -> Either OriginalCheckEventError Proposition
originalRequiredProposition result =
  case valueResultType result of
    TyRefined binder _ proposition
      | not (propositionMentions binder proposition) -> Right proposition
      | otherwise ->
          case valueResultTerm result of
            Just term -> Right (substituteProposition binder term proposition)
            Nothing -> Left (OriginalCheckEventSubjectNotVisible binder)
    other -> Left (OriginalCheckEventExpectedRefinement other)

validateResidualRecord
  :: CheckState
  -> ResidualSpec
  -> (ObligationId, Proposition)
  -> Either OriginalCheckEventError (Obligation, LogicalSubjectSupport)
validateResidualRecord state spec (obligationId', proposition) = do
  obligation <-
    case Map.lookup obligationId' (residualObligations state) of
      Just value -> Right value
      Nothing -> Left (OriginalCheckEventResidualMissing obligationId')
  unless (obligationProposition obligation == proposition) $
    Left
      (OriginalCheckEventResidualRecordMismatch
        obligationId'
        proposition
        (obligationProposition obligation))
  unless
    ( obligationOrigin obligation == residualOrigin spec
      && obligationScope obligation == residualScope spec
      && obligationRequiredPoint obligation == residualRequiredPoint spec
    ) $
    Left (OriginalCheckEventResidualMetadataMismatch obligationId' spec obligation)
  support <-
    case Map.lookup obligationId' (residualLogicalSubjects state) of
      Just value -> Right value
      Nothing -> Left (OriginalCheckEventLogicalSupportMissing obligationId')
  unless (logicalSupportObligation support == obligation) $
    Left
      (OriginalCheckEventLogicalSupportMismatch
        obligationId'
        obligation
        (logicalSupportObligation support))
  Right (obligation, support)

mergeLogicalBindings
  :: [Map Name Ty]
  -> Either OriginalCheckEventError (Map Name Ty)
mergeLogicalBindings = foldM mergeOne Map.empty
  where
    mergeOne accumulated additions =
      foldM insertOne accumulated (Map.toAscList additions)
    insertOne accumulated (name, ty) =
      case Map.lookup name accumulated of
        Nothing -> Right (Map.insert name ty accumulated)
        Just existing
          | existing == ty -> Right accumulated
          | otherwise -> Left (OriginalCheckEventLogicalTypeConflict name existing ty)

flattenResolved
  :: Discharge.ResolvedObligation
  -> Map ObligationId Discharge.ResolvedObligation
flattenResolved root = Map.fromList
  [ (obligationId (Discharge.resolvedObligation entry), entry)
  | entry <- go root
  ]
  where
    go entry = entry : concatMap go (Discharge.resolvedPrerequisites entry)

validateResolvedResidual
  :: Map ObligationId Discharge.ResolvedObligation
  -> (ObligationId, Proposition)
  -> Either OriginalCheckEventError ()
validateResolvedResidual resolvedById (obligationId', proposition) =
  case Map.lookup obligationId' resolvedById of
    Nothing ->
      Left
        (OriginalCheckEventResidualCoverageMismatch
          (Set.singleton obligationId')
          (Map.keysSet resolvedById))
    Just resolved ->
      let expected = normalizeProposition proposition
          actual = Discharge.resolvedCanonicalProposition resolved
      in unless (expected == actual) $
          Left
            (OriginalCheckEventResolvedPropositionMismatch
              obligationId'
              expected
              actual)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
