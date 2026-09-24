module Phil.Assurance
  ( OriginalCheckEventError (..)
  , OriginalCheckEventClosureError (..)
  , EvidenceSubjectOccurrence (..)
  , ActualEvidenceUse (..)
  , actualEvidenceUseInventory
  , resolveOriginalCheckEvent
  , handoffOriginalCheckEvent
  , closeOriginalCheckEventBundle
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
import Phil.Core.Context (ResourceContext (..))
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
  ( Mode (..)
  , Name
  , Obligation (..)
  , ObligationId
  , Proposition (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Core.Value (ValueResult (..))
import Phil.Verification (ApplicationAssurancePolicy)
import Phil.Verification.Bundle (VerificationBundle)
import qualified Phil.Verification.ManifestClosure as ManifestClosure

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

-- | Failure while taking one actual check event all the way through the
-- immutable final manifest consumer.  Keep event reconstruction and final
-- closure failures distinct so a caller cannot treat a downstream rejection as
-- permission to rebuild a smaller handoff.
data OriginalCheckEventClosureError
  = OriginalCheckEventClosureResolutionError OriginalCheckEventError
  | OriginalCheckEventClosureManifestError ManifestClosure.ManifestClosureError
  deriving (Eq, Show)

-- | One exact subject occurrence in an evidence use returned by the checker.
-- Occurrences, rather than a set of names, are retained so multi-subject facts
-- and repeated appearances of one subject cannot be silently collapsed before
-- later endpoint/rebase correspondence is established.
data EvidenceSubjectOccurrence = EvidenceSubjectOccurrence
  { evidenceSubjectUseIndex :: Int
  , evidenceSubjectOccurrenceIndex :: Int
  , evidenceSubjectName :: Name
  }
  deriving (Eq, Ord, Show)

-- | Complete classification of one evidence use from an actual 'ValueResult'.
-- A checked-closed use is credited only when the proposition carried by that
-- returned evidence use contains no subject occurrences.  Missing endpoint
-- metadata or failed lookups are never used as a proxy for closedness.
data ActualEvidenceUse
  = ActualSubjectBearingEvidenceUse
      { actualEvidenceUseIndex :: Int
      , actualEvidenceUse :: EvidenceUse
      , actualEvidenceSubjects :: [EvidenceSubjectOccurrence]
      }
  | ActualCheckedClosedEvidenceUse
      { actualEvidenceUseIndex :: Int
      , actualEvidenceUse :: EvidenceUse
      }
  deriving (Eq, Ord, Show)

-- | Reflect every evidence use returned by the real checker into an ordered,
-- occurrence-complete inventory.  The inventory is derived directly from the
-- 'ValueResult': callers cannot select a smaller evidence domain, and a closed
-- classification is based on the actual proposition structure rather than an
-- absent subject mapping.  This function intentionally does not invent an
-- original/final event identity for residual-free results; same-event final-use
-- correspondence remains a later boundary.
actualEvidenceUseInventory :: ValueResult -> [ActualEvidenceUse]
actualEvidenceUseInventory result =
  zipWith classify [1 ..] (valueResultEvidence result)
  where
    classify useIndex evidenceUse =
      let subjects = zipWith
            (EvidenceSubjectOccurrence useIndex)
            [1 ..]
            (evidenceUseSubjectNames evidenceUse)
      in case subjects of
          [] -> ActualCheckedClosedEvidenceUse useIndex evidenceUse
          _ -> ActualSubjectBearingEvidenceUse useIndex evidenceUse subjects

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
-- Logical subject typing is rebuilt only from the checked subject and exact
-- residual supports captured by the checker.  It is installed in a temporary
-- resolver view and never restores ownership or changes the returned resource
-- state.
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
      subjectBindings = checkedSubjectBindings result
      subjectUnrestricted =
        case valueResultMode result of
          Just Unrestricted -> subjectBindings
          _ -> Map.empty
  residualRecords <- mapM (validateResidualRecord state spec) residualUses
  logicalBindings <- mergeLogicalBindings
    ( subjectBindings
      : [ logicalSupportBindings support
        | (_, support) <- residualRecords
        ]
    )
  liveUnrestricted <- mergeLogicalBindings
    ( subjectUnrestricted
      : [ logicalSupportUnrestrictedBindings support
        | (_, support) <- residualRecords
        ]
    )
  let rootSupport = LogicalSubjectSupport
        { logicalSupportObligation = root
        , logicalSupportBindings = logicalBindings
        , logicalSupportUnrestrictedBindings = liveUnrestricted
        }
      resolverState = state
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

-- | Finalize one VerificationBundle from the exact original ValueResult rather
-- than accepting a caller-supplied handoff forest.  This is the final-consumer
-- adapter for the original-event rebase: the same event-derived handoff is
-- passed directly to 'closeVerificationBundleWithHandoff'.
--
-- This first adapter deliberately supplies no local EvidenceFact identity map.
-- A tree which actually depends on such a certificate fact therefore fails
-- closed in 'handoffOriginalCheckEvent' instead of bypassing the existing
-- authority-aware handoff.  Direct named evidence likewise remains subject to
-- the final closure's immutable-authority requirements.  This bounded route is
-- for the original-event prerequisite/definition/runtime composition repaired
-- here; the already-existing authority-aware evidence routes remain separate.
-- Resource ownership comes only from the returned 'ValueResult'; this function
-- never restores a consumed affine or linear owner.
closeOriginalCheckEventBundle
  :: HandoffConfig
  -> StaticContext
  -> Discharge.DischargePolicy
  -> ResidualSpec
  -> ValueResult
  -> VerificationBundle
  -> ApplicationAssurancePolicy
  -> VerificationContext
  -> AssuranceLedger
  -> ManifestClosure.ManifestClosureSelection
  -> Map RevisionId EvidenceEntryId
  -> Map RevisionId EvidenceEntryId
  -> Either OriginalCheckEventClosureError AssuranceManifest
closeOriginalCheckEventBundle
    config
    staticContext
    dischargePolicy
    spec
    result
    bundle
    assurancePolicy
    context
    ledger
    selection
    certificateEvidence
    directEvidence = do
  entries <- mapLeft OriginalCheckEventClosureResolutionError $
    handoffOriginalCheckEvent
      config
      Map.empty
      staticContext
      dischargePolicy
      spec
      result
  mapLeft OriginalCheckEventClosureManifestError $
    ManifestClosure.closeVerificationBundleWithHandoff
      bundle
      assurancePolicy
      context
      ledger
      selection
      ManifestClosure.ManifestClosureHandoff
        { ManifestClosure.manifestClosureHandoffEntries = entries
        , ManifestClosure.manifestClosureCertificateEvidence = certificateEvidence
        , ManifestClosure.manifestClosureDirectEvidence = directEvidence
        }

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

-- | Reuse the exact still-live checked binding when the structural value remains
-- present after checking.  This preserves the original refined subject type and,
-- for unrestricted values only, its existing evidence authority.  A consumed
-- affine or linear owner is never reconstructed: if the returned state no longer
-- contains the checked binding, the logical root falls back to the refinement's
-- base type and can only gain stronger typing from exact retained residual
-- support.
checkedSubjectBindings :: ValueResult -> Map Name Ty
checkedSubjectBindings result =
  case (valueResultType result, valueResultTerm result) of
    (TyRefined _ base _, Just (RefVar name)) ->
      Map.singleton name $
        case checkedLiveBinding result name of
          Just ty -> ty
          Nothing -> base
    _ -> Map.empty

checkedLiveBinding :: ValueResult -> Name -> Maybe Ty
checkedLiveBinding result name =
  let context = resourceContext (valueResultState result)
  in case valueResultMode result of
      Just Unrestricted -> Map.lookup name (unrestrictedBindings context)
      Just Affine -> Map.lookup name (affineBindings context)
      Just Linear -> Map.lookup name (linearBindings context)
      Nothing -> Nothing

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

evidenceUseSubjectNames :: EvidenceUse -> [Name]
evidenceUseSubjectNames evidenceUse =
  propositionSubjectNames $
    case evidenceUse of
      EvidenceByDefinition proposition -> proposition
      EvidenceByBinding _ proposition -> proposition
      EvidenceResidual _ proposition -> proposition

-- Preserve every RefVar occurrence in left-to-right semantic term order.  Do
-- not deduplicate equal names: a later subject-identity adapter must account for
-- every relevant occurrence in a multi-subject fact.
propositionSubjectNames :: Proposition -> [Name]
propositionSubjectNames proposition =
  case proposition of
    Truth -> []
    Falsehood -> []
    Equal left right -> termSubjectNames left ++ termSubjectNames right
    NotEqual left right -> termSubjectNames left ++ termSubjectNames right
    LessThan left right -> termSubjectNames left ++ termSubjectNames right
    LessEqual left right -> termSubjectNames left ++ termSubjectNames right
    Member value collection -> termSubjectNames value ++ termSubjectNames collection
    Disjoint left right -> termSubjectNames left ++ termSubjectNames right
    Conjunction left right -> propositionSubjectNames left ++ propositionSubjectNames right
    Disjunction left right -> propositionSubjectNames left ++ propositionSubjectNames right
    Negation inner -> propositionSubjectNames inner
    Atom _ arguments -> concatMap termSubjectNames arguments

termSubjectNames :: RefTerm -> [Name]
termSubjectNames term =
  case term of
    RefVar name -> [name]
    RefField base _ _ -> termSubjectNames base
    RefLen value -> termSubjectNames value
    RefToNat value -> termSubjectNames value
    RefAdd left right -> termSubjectNames left ++ termSubjectNames right
    RefSub left right -> termSubjectNames left ++ termSubjectNames right
    RefScale _ value -> termSubjectNames value
    RefNat _ -> []
    RefUInt _ _ -> []
    RefBool _ -> []
    RefOpaque _ _ -> []

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
