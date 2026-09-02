{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.RuntimeCarrierBinding
  ( RuntimeCarrierBinding (..)
  , RuntimeCarrierBindingError (..)
  , checkRuntimeCarrierBindings
  ) where

import Control.Monad (forM, forM_, unless, when)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Phil.Assurance.Types
  ( AssuranceKind (..)
  , AssuranceLedger (..)
  , AssuranceManifest (..)
  , AssuranceUse (..)
  , AssuranceUseId
  , EvidenceEntry (..)
  , EvidenceEntryId
  , RevisionId
  )
import Phil.Systems.IR
  ( RuntimeSiteRef (..)
  , SystemsArtifact (..)
  , SystemsProgram (..)
  , runtimeSites
  )
import Phil.Systems.RuntimeCarrierCoverage
  ( RuntimeCarrier (..)
  , RuntimeCarrierKey
  )

-- | DEP-001's explicit bridge between one selected RuntimeBound assurance use,
-- one exact semantic carrier, and the exact Systems runtime site that realizes
-- the retained check.  DEP-002 separately proves carrier coverage across
-- process/execution transfer; this relation prevents a merely asserted or
-- unrelated carrier from closing assurance.
data RuntimeCarrierBinding = RuntimeCarrierBinding
  { runtimeCarrierBindingUseId :: AssuranceUseId
  , runtimeCarrierBindingCarrierKey :: RuntimeCarrierKey
  , runtimeCarrierBindingRuntimeSite :: RuntimeSiteRef
  }
  deriving (Eq, Ord, Show)

data RuntimeCarrierBindingError
  = RuntimeCarrierBindingSelectedUseMissing AssuranceUseId
  | RuntimeCarrierBindingDomainMismatch (Set AssuranceUseId) (Set AssuranceUseId)
  | RuntimeCarrierBindingMapKeyMismatch AssuranceUseId AssuranceUseId
  | RuntimeCarrierBindingUseOutsideCertificationScope AssuranceUseId RevisionId
  | RuntimeCarrierBindingEvidenceNotSelected AssuranceUseId EvidenceEntryId
  | RuntimeCarrierBindingEvidenceMissing AssuranceUseId EvidenceEntryId
  | RuntimeCarrierBindingEvidenceNotRuntimeEnforced AssuranceUseId EvidenceEntryId AssuranceKind
  | RuntimeCarrierBindingEvidenceRevisionMismatch AssuranceUseId EvidenceEntryId RevisionId RevisionId
  | RuntimeCarrierBindingEvidenceMechanismMissing AssuranceUseId EvidenceEntryId
  | RuntimeCarrierBindingEvidenceCostMismatch AssuranceUseId EvidenceEntryId String
  | RuntimeCarrierBindingCarrierMissing AssuranceUseId RuntimeCarrierKey
  | RuntimeCarrierBindingCarrierObligationMismatch AssuranceUseId RuntimeCarrierKey RevisionId RevisionId
  | RuntimeCarrierBindingSiteRevisionMismatch AssuranceUseId RevisionId RevisionId
  | RuntimeCarrierBindingSiteEvidenceMismatch AssuranceUseId EvidenceEntryId EvidenceEntryId
  | RuntimeCarrierBindingSiteCostMismatch AssuranceUseId String String
  | RuntimeCarrierBindingSiteMissing AssuranceUseId
  | RuntimeCarrierBindingSiteAmbiguous AssuranceUseId Int
  deriving (Eq, Show)

checkRuntimeCarrierBindings
  :: AssuranceLedger
  -> AssuranceManifest
  -> SystemsArtifact
  -> Map RuntimeCarrierKey RuntimeCarrier
  -> Map AssuranceUseId RuntimeCarrierBinding
  -> Either RuntimeCarrierBindingError ()
checkRuntimeCarrierBindings ledger manifest artifact carriers bindings = do
  selectedUses <- forM (Set.toAscList (manifestAssuranceUses manifest)) $ \useId ->
    case Map.lookup useId (ledgerUses ledger) of
      Nothing -> Left (RuntimeCarrierBindingSelectedUseMissing useId)
      Just assuranceUse -> Right (useId, assuranceUse)
  let retainedUses = Map.fromList
        [ (useId, assuranceUse)
        | (useId, assuranceUse@RetainedRuntimeUse {}) <- selectedUses
        ]
      expectedDomain = Map.keysSet retainedUses
      actualDomain = Map.keysSet bindings
  unless (expectedDomain == actualDomain) $
    Left (RuntimeCarrierBindingDomainMismatch expectedDomain actualDomain)
  forM_ (Map.toAscList bindings) $ \(mapKey, binding) -> do
    unless (mapKey == runtimeCarrierBindingUseId binding) $
      Left (RuntimeCarrierBindingMapKeyMismatch
        mapKey (runtimeCarrierBindingUseId binding))
    assuranceUse <- case Map.lookup mapKey retainedUses of
      Nothing -> Left (RuntimeCarrierBindingDomainMismatch expectedDomain actualDomain)
      Just value -> Right value
    validateBinding mapKey assuranceUse binding
  where
    programSites = concatMap runtimeSites
      (Map.elems (systemsProgramFunctions (systemsArtifactProgram artifact)))

    validateBinding useId assuranceUse binding =
      case assuranceUse of
        ErasureUse {} -> Left (RuntimeCarrierBindingDomainMismatch Set.empty (Set.singleton useId))
        RetainedRuntimeUse
          { useObligationRevision = revision
          , useRuntimeEvidence = evidenceId
          , useCostRef = costRef
          } -> do
            unless (Set.member revision (manifestCertificationScope manifest)) $
              Left (RuntimeCarrierBindingUseOutsideCertificationScope useId revision)
            unless (Set.member evidenceId (manifestEvidenceEntries manifest)) $
              Left (RuntimeCarrierBindingEvidenceNotSelected useId evidenceId)
            evidence <- case Map.lookup evidenceId (ledgerEvidence ledger) of
              Nothing -> Left (RuntimeCarrierBindingEvidenceMissing useId evidenceId)
              Just value -> Right value
            unless (evidenceAssuranceKind evidence == RuntimeEnforced) $
              Left (RuntimeCarrierBindingEvidenceNotRuntimeEnforced
                useId evidenceId (evidenceAssuranceKind evidence))
            unless (evidenceObligationRevision evidence == revision) $
              Left (RuntimeCarrierBindingEvidenceRevisionMismatch
                useId evidenceId revision (evidenceObligationRevision evidence))
            when (evidenceRuntimeMechanism evidence == Nothing) $
              Left (RuntimeCarrierBindingEvidenceMechanismMissing useId evidenceId)
            unless (costRef `elem` evidenceCostRefs evidence) $
              Left (RuntimeCarrierBindingEvidenceCostMismatch
                useId evidenceId (show costRef))
            carrier <- case Map.lookup (runtimeCarrierBindingCarrierKey binding) carriers of
              Nothing -> Left (RuntimeCarrierBindingCarrierMissing
                useId (runtimeCarrierBindingCarrierKey binding))
              Just value -> Right value
            unless (runtimeCarrierObligation carrier == revision) $
              Left (RuntimeCarrierBindingCarrierObligationMismatch
                useId
                (runtimeCarrierBindingCarrierKey binding)
                revision
                (runtimeCarrierObligation carrier))
            let site = runtimeCarrierBindingRuntimeSite binding
            unless (runtimeSiteRevision site == revision) $
              Left (RuntimeCarrierBindingSiteRevisionMismatch
                useId revision (runtimeSiteRevision site))
            unless (runtimeSiteEvidence site == evidenceId) $
              Left (RuntimeCarrierBindingSiteEvidenceMismatch
                useId evidenceId (runtimeSiteEvidence site))
            unless (runtimeSiteCostRef site == costRef) $
              Left (RuntimeCarrierBindingSiteCostMismatch
                useId (show costRef) (show (runtimeSiteCostRef site)))
            case length (filter (== site) programSites) of
              0 -> Left (RuntimeCarrierBindingSiteMissing useId)
              1 -> Right ()
              count -> Left (RuntimeCarrierBindingSiteAmbiguous useId count)
