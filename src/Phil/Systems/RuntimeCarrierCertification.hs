{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.RuntimeCarrierCertification
  ( RuntimeCarrierCertificationWitness (..)
  , RuntimeCarrierCertificationError (..)
  , verifyRuntimeCarrierCertification
  ) where

import Control.Monad (forM_, unless)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types
  ( AssuranceLedger (..)
  , AssuranceManifest (..)
  , AssuranceUse (..)
  , AssuranceUseId
  , RevisionId
  , VerificationContext
  )
import Phil.Assurance.Verify
  ( ManifestError
  , verifyManifest
  )
import Phil.Systems.CostAttribution
  ( CostAttributionStageBundle (..)
  )
import Phil.Systems.IR
  ( RuntimeSiteRef (..)
  , SystemsArtifact (..)
  )
import Phil.Systems.NextStageRequirement
  ( NextStageRequirementStageBundle (..)
  )
import Phil.Systems.ProcessRealization
  ( ProcessExecutionRealization
  )
import Phil.Systems.RuntimeCarrierBinding
  ( RuntimeCarrierBinding (..)
  , RuntimeCarrierBindingError
  , checkRuntimeCarrierBindings
  )
import Phil.Systems.RuntimeCarrierCoverage
  ( RuntimeCarrier (..)
  , RuntimeCarrierCoverageError
  , RuntimeCarrierKey
  , RuntimeCarrierProfile
  , RuntimeCarrierTransition (..)
  , RuntimeCarrierTransitionDisposition (..)
  , RuntimeCarrierUse (..)
  , RuntimeCarrierUseDisposition (..)
  , checkRuntimeCarrierCoverage
  )
import Phil.Systems.RuntimeClaimBinding
  ( RuntimeClaim (..)
  , RuntimeClaimBinding (..)
  , RuntimeClaimRevision
  , RuntimeClaimStageBundle (..)
  , RuntimeSiteBinding (..)
  , RuntimeSiteKey
  )
import Phil.Systems.RuntimePrimitiveReuse
  ( RuntimePrimitiveStageBundle (..)
  )
import Phil.Systems.StageClosure
  ( StageClosureBundle (..)
  , StageClosureVerificationError
  , nextStageSubjectStage
  , verifyStageClosureBundle
  )
import Phil.Systems.StagingEffect
  ( StagingEffectStageBundle (..)
  )
import Phil.Systems.SubjectCorrespondence
  ( SubjectStageBundle (..)
  )
import Phil.Systems.Phase1Stage
  ( Phase1StageBundle (..)
  )
import qualified RuntimeCarrierKernel as Kernel

-- | The two identities that are not recoverable from either legacy DEP checker
-- alone.  A covered target use names the selected assurance use whose exact
-- carrier/site binding it realizes; every carrier also names the exact verified
-- runtime claim to which its established site belongs.
data RuntimeCarrierCertificationWitness = RuntimeCarrierCertificationWitness
  { runtimeCarrierCertificationUseLinks :: Map Text AssuranceUseId
  , runtimeCarrierCertificationClaims :: Map RuntimeCarrierKey RuntimeClaimRevision
  }
  deriving (Eq, Show)

data RuntimeCarrierCertificationError
  = RuntimeCarrierCertificationManifestError ManifestError
  | RuntimeCarrierCertificationStageClosureError StageClosureVerificationError
  | RuntimeCarrierCertificationBindingError RuntimeCarrierBindingError
  | RuntimeCarrierCertificationCoverageError RuntimeCarrierCoverageError
  | RuntimeCarrierCertificationDuplicateUseId Text
  | RuntimeCarrierCertificationDuplicateTransitionId Text
  | RuntimeCarrierCertificationUseLinkDomainMismatch (Set Text) (Set Text)
  | RuntimeCarrierCertificationRetainedUseUncovered AssuranceUseId
  | RuntimeCarrierCertificationLinkedUseMissing Text
  | RuntimeCarrierCertificationLinkedAssuranceUseMissing Text AssuranceUseId
  | RuntimeCarrierCertificationLinkedUseNotRetained Text AssuranceUseId
  | RuntimeCarrierCertificationBindingMissing AssuranceUseId
  | RuntimeCarrierCertificationCarrierMissing RuntimeCarrierKey
  | RuntimeCarrierCertificationCarrierBindingMismatch Text RuntimeCarrierKey RuntimeCarrierKey
  | RuntimeCarrierCertificationUseObligationMismatch Text RevisionId RevisionId
  | RuntimeCarrierCertificationClaimDomainMismatch
      (Set RuntimeCarrierKey) (Set RuntimeCarrierKey)
  | RuntimeCarrierCertificationClaimMissing RuntimeCarrierKey RuntimeClaimRevision
  | RuntimeCarrierCertificationClaimBindingMissing RuntimeClaimRevision
  | RuntimeCarrierCertificationRuntimeSiteMissing AssuranceUseId
  | RuntimeCarrierCertificationRuntimeSiteAmbiguous AssuranceUseId Int
  | RuntimeCarrierCertificationClaimSiteMismatch
      RuntimeCarrierKey RuntimeClaimRevision RuntimeSiteKey
  | RuntimeCarrierCertificationClaimObligationMismatch
      RuntimeCarrierKey RuntimeClaimRevision RevisionId
  | RuntimeCarrierCertificationKernelDisagreement Text
  deriving (Eq, Show)

verifyRuntimeCarrierCertification
  :: VerificationContext
  -> AssuranceLedger
  -> AssuranceManifest
  -> StageClosureBundle
  -> RuntimeCarrierProfile
  -> ProcessExecutionRealization
  -> Map RuntimeCarrierKey RuntimeCarrier
  -> Map AssuranceUseId RuntimeCarrierBinding
  -> [RuntimeCarrierUse]
  -> [RuntimeCarrierTransition]
  -> RuntimeCarrierCertificationWitness
  -> Either RuntimeCarrierCertificationError ()
verifyRuntimeCarrierCertification
    verificationContext ledger manifest closure profile realization
    carriers bindings uses transitions witness = do
  mapLeft RuntimeCarrierCertificationManifestError $
    verifyManifest verificationContext ledger manifest
  mapLeft RuntimeCarrierCertificationStageClosureError $
    verifyStageClosureBundle closure

  let artifact = artifactFromClosure closure
      contract = systemsArtifactStageContract artifact
      claimStage = runtimeClaimStageFromClosure closure
  mapLeft RuntimeCarrierCertificationBindingError $
    checkRuntimeCarrierBindings ledger manifest artifact carriers bindings
  mapLeft RuntimeCarrierCertificationCoverageError $
    checkRuntimeCarrierCoverage profile contract realization carriers uses transitions

  verifyUniqueUseIds uses
  verifyUniqueTransitionIds transitions
  verifyWitnessDomains ledger manifest carriers uses witness

  forM_ uses $ \use ->
    case runtimeCarrierUseDisposition use of
      RuntimeUseStaticallySafe -> Right ()
      RuntimeUseExplicitBoundary boundary ->
        unless (Kernel.decideExplicitBoundaryCarrierUseByFacts
          (not (Text.null boundary))) $
          Left (RuntimeCarrierCertificationKernelDisagreement
            ("explicit-boundary-use:" <> runtimeCarrierUseId use))
      RuntimeUseCovered carrierKey ->
        verifyCoveredUse ledger manifest claimStage carriers bindings witness use carrierKey

  forM_ transitions $ verifyTransition carriers uses

verifyUniqueUseIds
  :: [RuntimeCarrierUse]
  -> Either RuntimeCarrierCertificationError ()
verifyUniqueUseIds uses = go Set.empty uses
  where
    go _ [] = Right ()
    go seen (use : rest)
      | Set.member (runtimeCarrierUseId use) seen =
          Left (RuntimeCarrierCertificationDuplicateUseId (runtimeCarrierUseId use))
      | otherwise = go (Set.insert (runtimeCarrierUseId use) seen) rest

verifyUniqueTransitionIds
  :: [RuntimeCarrierTransition]
  -> Either RuntimeCarrierCertificationError ()
verifyUniqueTransitionIds transitions = go Set.empty transitions
  where
    go _ [] = Right ()
    go seen (transition : rest)
      | Set.member (runtimeCarrierTransitionId transition) seen =
          Left (RuntimeCarrierCertificationDuplicateTransitionId
            (runtimeCarrierTransitionId transition))
      | otherwise = go
          (Set.insert (runtimeCarrierTransitionId transition) seen)
          rest

verifyWitnessDomains
  :: AssuranceLedger
  -> AssuranceManifest
  -> Map RuntimeCarrierKey RuntimeCarrier
  -> [RuntimeCarrierUse]
  -> RuntimeCarrierCertificationWitness
  -> Either RuntimeCarrierCertificationError ()
verifyWitnessDomains ledger manifest carriers uses witness = do
  let coveredIds = Set.fromList
        [ runtimeCarrierUseId use
        | use <- uses
        , RuntimeUseCovered _ <- [runtimeCarrierUseDisposition use]
        ]
      linkDomain = Map.keysSet (runtimeCarrierCertificationUseLinks witness)
  unless (coveredIds == linkDomain) $
    Left (RuntimeCarrierCertificationUseLinkDomainMismatch coveredIds linkDomain)

  let retainedIds = Set.fromList
        [ useId
        | useId <- Set.toAscList (manifestAssuranceUses manifest)
        , Just RetainedRuntimeUse {} <- [Map.lookup useId (ledgerUses ledger)]
        ]
      linkedIds = Set.fromList (Map.elems (runtimeCarrierCertificationUseLinks witness))
  case Set.lookupMin (Set.difference retainedIds linkedIds) of
    Nothing -> Right ()
    Just useId -> Left (RuntimeCarrierCertificationRetainedUseUncovered useId)

  let expectedClaims = Map.keysSet carriers
      actualClaims = Map.keysSet (runtimeCarrierCertificationClaims witness)
  unless (expectedClaims == actualClaims) $
    Left (RuntimeCarrierCertificationClaimDomainMismatch expectedClaims actualClaims)

verifyCoveredUse
  :: AssuranceLedger
  -> AssuranceManifest
  -> RuntimeClaimStageBundle
  -> Map RuntimeCarrierKey RuntimeCarrier
  -> Map AssuranceUseId RuntimeCarrierBinding
  -> RuntimeCarrierCertificationWitness
  -> RuntimeCarrierUse
  -> RuntimeCarrierKey
  -> Either RuntimeCarrierCertificationError ()
verifyCoveredUse ledger manifest claimStage carriers bindings witness use carrierKey = do
  assuranceId <- case Map.lookup
      (runtimeCarrierUseId use)
      (runtimeCarrierCertificationUseLinks witness) of
    Nothing -> Left (RuntimeCarrierCertificationLinkedUseMissing
      (runtimeCarrierUseId use))
    Just value -> Right value

  assuranceUse <- case Map.lookup assuranceId (ledgerUses ledger) of
    Nothing -> Left (RuntimeCarrierCertificationLinkedAssuranceUseMissing
      (runtimeCarrierUseId use) assuranceId)
    Just value -> Right value

  (assuranceObligation, assuranceEvidence, assuranceCost) <-
    case assuranceUse of
      RetainedRuntimeUse
        { useObligationRevision = obligation
        , useRuntimeEvidence = evidence
        , useCostRef = cost
        } -> Right (obligation, evidence, cost)
      ErasureUse {} -> Left (RuntimeCarrierCertificationLinkedUseNotRetained
        (runtimeCarrierUseId use) assuranceId)

  unless (Set.member assuranceId (manifestAssuranceUses manifest)) $
    Left (RuntimeCarrierCertificationLinkedAssuranceUseMissing
      (runtimeCarrierUseId use) assuranceId)

  binding <- case Map.lookup assuranceId bindings of
    Nothing -> Left (RuntimeCarrierCertificationBindingMissing assuranceId)
    Just value -> Right value

  carrier <- case Map.lookup carrierKey carriers of
    Nothing -> Left (RuntimeCarrierCertificationCarrierMissing carrierKey)
    Just value -> Right value

  unless (runtimeCarrierBindingCarrierKey binding == carrierKey) $
    Left (RuntimeCarrierCertificationCarrierBindingMismatch
      (runtimeCarrierUseId use)
      carrierKey
      (runtimeCarrierBindingCarrierKey binding))

  unless (runtimeCarrierUseObligation use == assuranceObligation) $
    Left (RuntimeCarrierCertificationUseObligationMismatch
      (runtimeCarrierUseId use)
      assuranceObligation
      (runtimeCarrierUseObligation use))

  claimRevision <- case Map.lookup
      carrierKey
      (runtimeCarrierCertificationClaims witness) of
    Nothing -> Left (RuntimeCarrierCertificationCarrierMissing carrierKey)
    Just value -> Right value

  claim <- case Map.lookup claimRevision (runtimeClaimStageClaims claimStage) of
    Nothing -> Left (RuntimeCarrierCertificationClaimMissing carrierKey claimRevision)
    Just value -> Right value

  claimBinding <- case Map.lookup claimRevision (runtimeClaimStageBindings claimStage) of
    Nothing -> Left (RuntimeCarrierCertificationClaimBindingMissing claimRevision)
    Just value -> Right value

  let siteRef = runtimeCarrierBindingRuntimeSite binding
      matchingSites =
        [ siteKey
        | (siteKey, siteBinding) <- Map.toAscList (runtimeClaimStageSites claimStage)
        , runtimeSiteBindingRef siteBinding == siteRef
        ]
  siteKey <- case matchingSites of
    [] -> Left (RuntimeCarrierCertificationRuntimeSiteMissing assuranceId)
    [value] -> Right value
    values -> Left (RuntimeCarrierCertificationRuntimeSiteAmbiguous
      assuranceId (length values))

  let reverseClaims = Map.findWithDefault Set.empty siteKey
        (runtimeClaimStageReverse claimStage)
      claimAtSite =
        Set.member siteKey (runtimeClaimBindingSites claimBinding)
          && Set.member claimRevision reverseClaims
  unless claimAtSite $
    Left (RuntimeCarrierCertificationClaimSiteMismatch
      carrierKey claimRevision siteKey)

  unless (Set.member assuranceObligation (runtimeClaimSourceObligations claim)) $
    Left (RuntimeCarrierCertificationClaimObligationMismatch
      carrierKey claimRevision assuranceObligation)

  let exactBinding = Kernel.decideExactCarrierBindingByFacts
        (runtimeCarrierBindingUseId binding == assuranceId)
        True
        (Map.member carrierKey carriers)
        (runtimeCarrierUseDisposition use == RuntimeUseCovered carrierKey)
        (runtimeCarrierUseObligation use == runtimeCarrierObligation carrier)
        (runtimeSiteRevision siteRef == runtimeCarrierUseObligation use)
        (runtimeSiteEvidence siteRef == assuranceEvidence)
        (runtimeSiteCostRef siteRef == assuranceCost)
        True
        claimAtSite
        (runtimeCarrierUseProcess use == runtimeCarrierProcess carrier)
        (Set.member
          (runtimeCarrierUseExecution use)
          (runtimeCarrierExecutions carrier))
        True
  unless exactBinding $
    Left (RuntimeCarrierCertificationKernelDisagreement
      ("exact-carrier-binding:" <> runtimeCarrierUseId use))
  unless (Kernel.decideCoveredCarrierUseByFacts exactBinding) $
    Left (RuntimeCarrierCertificationKernelDisagreement
      ("covered-carrier-use:" <> runtimeCarrierUseId use))

verifyTransition
  :: Map RuntimeCarrierKey RuntimeCarrier
  -> [RuntimeCarrierUse]
  -> RuntimeCarrierTransition
  -> Either RuntimeCarrierCertificationError ()
verifyTransition carriers uses transition =
  case runtimeCarrierTransitionDisposition transition of
    CarrierPreserved carrierKey -> do
      carrier <- requireCarrier carriers carrierKey
      requireKernel
        (Kernel.decidePreservedCarrierTransitionByFacts
          True
          (runtimeCarrierTransitionObligation transition
            == runtimeCarrierObligation carrier)
          (runtimeCarrierTransitionProcess transition
            == runtimeCarrierProcess carrier)
          (Set.member
            (runtimeCarrierTransitionFrom transition)
            (runtimeCarrierExecutions carrier))
          (Set.member
            (runtimeCarrierTransitionTo transition)
            (runtimeCarrierExecutions carrier)))
        "preserved-transition"
    CarrierReplaced priorKey nextKey -> do
      prior <- requireCarrier carriers priorKey
      next <- requireCarrier carriers nextKey
      requireKernel
        (Kernel.decideReplacedCarrierTransitionByFacts
          True
          True
          (runtimeCarrierTransitionObligation transition
            == runtimeCarrierObligation prior)
          (runtimeCarrierTransitionObligation transition
            == runtimeCarrierObligation next)
          (runtimeCarrierTransitionProcess transition
            == runtimeCarrierProcess prior)
          (runtimeCarrierTransitionProcess transition
            == runtimeCarrierProcess next)
          (Set.member
            (runtimeCarrierTransitionFrom transition)
            (runtimeCarrierExecutions prior))
          (Set.member
            (runtimeCarrierTransitionTo transition)
            (runtimeCarrierExecutions next)))
        "replaced-transition"
    CarrierDischarged carrierKey _ -> do
      carrier <- requireCarrier carriers carrierKey
      verifyClosedTransition carrier
    CarrierValidityEnded carrierKey _ -> do
      carrier <- requireCarrier carriers carrierKey
      verifyClosedTransition carrier
  where
    verifyClosedTransition carrier =
      requireKernel
        (Kernel.decideClosedCarrierTransitionByFacts
          True
          (runtimeCarrierTransitionObligation transition
            == runtimeCarrierObligation carrier)
          (runtimeCarrierTransitionProcess transition
            == runtimeCarrierProcess carrier)
          (Set.member
            (runtimeCarrierTransitionFrom transition)
            (runtimeCarrierExecutions carrier))
          (destinationNotRuntimeBound uses transition))
        "closed-transition"

    requireKernel accepted label = unless accepted $
      Left (RuntimeCarrierCertificationKernelDisagreement
        (label <> ":" <> runtimeCarrierTransitionId transition))

requireCarrier
  :: Map RuntimeCarrierKey RuntimeCarrier
  -> RuntimeCarrierKey
  -> Either RuntimeCarrierCertificationError RuntimeCarrier
requireCarrier carriers carrierKey =
  case Map.lookup carrierKey carriers of
    Nothing -> Left (RuntimeCarrierCertificationCarrierMissing carrierKey)
    Just carrier -> Right carrier

destinationNotRuntimeBound
  :: [RuntimeCarrierUse]
  -> RuntimeCarrierTransition
  -> Bool
destinationNotRuntimeBound uses transition = not (any matches uses)
  where
    matches use =
      runtimeCarrierUseProcess use == runtimeCarrierTransitionProcess transition
        && runtimeCarrierUseObligation use == runtimeCarrierTransitionObligation transition
        && runtimeCarrierUseExecution use == runtimeCarrierTransitionTo transition
        && case runtimeCarrierUseDisposition use of
          RuntimeUseCovered _ -> True
          _ -> False

runtimeClaimStageFromClosure :: StageClosureBundle -> RuntimeClaimStageBundle
runtimeClaimStageFromClosure =
  runtimePrimitiveStageBase
    . stagingEffectStageBase
    . costAttributionStageBase
    . nextStageRequirementStageBase
    . stageClosureNextStage

artifactFromClosure :: StageClosureBundle -> SystemsArtifact
artifactFromClosure =
  phase1StageSystemsArtifact
    . subjectStageBase
    . nextStageSubjectStage
    . stageClosureNextStage

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
