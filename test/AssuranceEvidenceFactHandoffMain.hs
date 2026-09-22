{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Assurance
import Phil.Core.Decision
  ( AssumptionRef (..)
  , DecisionCertificate (..)
  )
import Phil.Core.Discharge
  ( ObligationDisposition (..)
  , ResolvedObligation (..)
  , StaticDischarge (..)
  )
import Phil.Core.Syntax
  ( Name (..)
  , Obligation (..)
  , ObligationId (..)
  , Proposition (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "EvidenceFact resolves to immutable evidence-entry support" evidenceFactSupportPreserved
    , test "missing EvidenceFact identity fails closed" missingEvidenceFactRejected
    , test "certificate evidence uses authoritative handoff support" certificateEvidenceSupportRebound
    , test "evidence support is not projected as revision support" evidenceSupportStaysPrecise
    ]
  if and results then pure () else exitFailure

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed

evidenceFactSupportPreserved :: Bool
evidenceFactSupportPreserved =
  case handoffResolvedObligationWithEvidence
      handoffConfig evidenceIdentityMap mixedResolved of
    Right (parent : child : _) ->
      let childRevision = revisionId (handoffRevision child)
      in handoffSupportDependencies parent
          == [ DependsOnEvidence evidenceEntryId
             , DependsOnObligation childRevision
             ]
    _ -> False

missingEvidenceFactRejected :: Bool
missingEvidenceFactRejected =
  case handoffResolvedObligation handoffConfig mixedResolved of
    Left (UnknownEvidenceFactSupport consumer name index) ->
      consumer == obligationId parentObligation
        && name == evidenceName
        && index == evidenceIndex
    _ -> False

certificateEvidenceSupportRebound :: Bool
certificateEvidenceSupportRebound =
  case handoffResolvedObligationWithEvidence
      handoffConfig evidenceIdentityMap mixedResolved of
    Right (parent : child : _) ->
      let parentRevision = revisionId (handoffRevision parent)
          childRevision = revisionId (handoffRevision child)
          staleEvidence = EvidenceEntryId "evidence.test.handoff.stale"
          staleRevision = RevisionId "rev.test.handoff.stale"
          provisional = testCertificateEvidence parentRevision
            [ DependsOnEvidence staleEvidence
            , DependsOnObligation staleRevision
            ]
      in case bindHandoffCertificateEvidence parent provisional of
          Right finalized ->
            evidenceDependsOn finalized
              == [ DependsOnEvidence evidenceEntryId
                 , DependsOnObligation childRevision
                 ]
              && evidenceEntryDigest finalized == deriveEvidenceEntryDigest finalized
              && evidenceEntryDigest finalized /= evidenceEntryDigest provisional
          Left _ -> False
    _ -> False

evidenceSupportStaysPrecise :: Bool
evidenceSupportStaysPrecise =
  case handoffResolvedObligationWithEvidence
      handoffConfig evidenceIdentityMap mixedResolved of
    Right entries@(parent : child : _) ->
      handoffSupportEdges entries
        == Set.singleton
          ( revisionId (handoffRevision parent)
          , revisionId (handoffRevision child)
          )
    _ -> False

evidenceIdentityMap :: Map.Map (Name, Int) EvidenceEntryId
evidenceIdentityMap = Map.singleton (evidenceName, evidenceIndex) evidenceEntryId

evidenceName :: Name
evidenceName = Name "proof"

evidenceIndex :: Int
evidenceIndex = 1

evidenceEntryId :: EvidenceEntryId
evidenceEntryId = EvidenceEntryId "evidence.test.handoff.proof.1"

mixedResolved :: ResolvedObligation
mixedResolved = ResolvedObligation
  { resolvedObligation = parentObligation
  , resolvedCanonicalProposition = Truth
  , resolvedPrerequisites = [childResolved]
  , resolvedDisposition = StaticallyDischarged StaticByCertificate
      { staticCertificateProducer = "test-producer"
      , staticCertificateChecker = "test-checker"
      , staticCertificate = CertificateConjunction
          (CertificateAssumption (EvidenceFact evidenceName evidenceIndex) Truth)
          (CertificateAssumption
            (PrerequisiteFact (obligationId childObligation)) Truth)
      }
  }

childResolved :: ResolvedObligation
childResolved = ResolvedObligation
  { resolvedObligation = childObligation
  , resolvedCanonicalProposition = Truth
  , resolvedPrerequisites = []
  , resolvedDisposition = StaticallyDischarged StaticByDefinition
  }

parentObligation :: Obligation
parentObligation = Obligation
  { obligationId = ObligationId "test.handoff.evidence-parent"
  , obligationProposition = Truth
  , obligationOrigin = "test"
  , obligationScope = "test.scope"
  , obligationRequiredPoint = "evidence-parent.required"
  }

childObligation :: Obligation
childObligation = Obligation
  { obligationId = ObligationId "test.handoff.evidence-child"
  , obligationProposition = Truth
  , obligationOrigin = "test"
  , obligationScope = "test.scope"
  , obligationRequiredPoint = "evidence-child.required"
  }

handoffConfig :: HandoffConfig
handoffConfig = HandoffConfig
  { handoffRevisionKind = const "Test"
  , handoffRepresentation = const "Core"
  , handoffSubjectIds = const ["subject"]
  , handoffContextIds = const ["context"]
  , handoffAcceptanceRule = const (AcceptEntry KernelChecked (EvidenceRole "establishes"))
  }

testCertificateEvidence :: RevisionId -> [EvidenceDependency] -> EvidenceEntry
testCertificateEvidence revision dependencies = EvidenceEntry
  { evidenceEntryId = EvidenceEntryId "evidence.test.handoff.certificate"
  , evidenceEntryDigest = Digest "stale-before-handoff"
  , evidenceObligationRevision = revision
  , evidenceAssuranceKind = KernelChecked
  , evidenceRole = EvidenceRole "establishes"
  , evidenceProducer = "test-producer"
  , evidenceChecker = "test-checker"
  , evidenceArtifact = Nothing
  , evidenceInputDigests = []
  , evidenceAssumptions = []
  , evidenceDependsOn = dependencies
  , evidenceValidityScope = ValidityScope mempty
  , evidenceResult = EvidenceAccepted
  , evidenceJustifies = ["certificate"]
  , evidenceRuntimeMechanism = Nothing
  , evidenceRuntimeResidue = []
  , evidenceCostRefs = []
  }
