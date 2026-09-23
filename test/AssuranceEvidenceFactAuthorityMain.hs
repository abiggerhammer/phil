{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Assurance.EvidenceFactAuthority
import Phil.Assurance.Handoff
  ( HandoffConfig (..)
  , LedgerHandoff (..)
  )
import Phil.Assurance.Types
  ( AcceptanceRule (..)
  , AssuranceKind (..)
  , AssuranceLedger (..)
  , Digest (..)
  , EvidenceDependency (..)
  , EvidenceEntry (..)
  , EvidenceEntryId (..)
  , EvidenceResult (..)
  , EvidenceRole (..)
  , ObligationRevision (..)
  , ValidityScope (..)
  , deriveEvidenceEntryDigest
  , emptyLedger
  , revisionFromCoreObligation
  )
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
    [ test "authoritative EvidenceFact reaches ordinary immutable handoff" authoritativeFactAccepted
    , test "mapped immutable proposition drift fails closed" propositionMismatchRejected
    , test "mapped immutable subject drift fails closed" subjectMismatchRejected
    , test "mapped immutable scope drift fails closed" scopeMismatchRejected
    , test "missing mapped immutable evidence fails closed" missingEvidenceRejected
    ]
  if and results then pure () else exitFailure

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed

authoritativeFactAccepted :: Bool
authoritativeFactAccepted =
  case handoffResolvedObligationWithEvidenceAuthority
      handoffConfig authorityBindings (authorityLedger Truth expectedSubjects expectedScope) resolved of
    Right (entry : _) ->
      handoffSupportDependencies entry == [DependsOnEvidence supportEvidenceId]
    _ -> False

propositionMismatchRejected :: Bool
propositionMismatchRejected =
  case handoffResolvedObligationWithEvidenceAuthority
      handoffConfig authorityBindings (authorityLedger Falsehood expectedSubjects expectedScope) resolved of
    Left (EvidenceFactAuthorityPropositionMismatch _ _ _ _ _) -> True
    _ -> False

subjectMismatchRejected :: Bool
subjectMismatchRejected =
  case handoffResolvedObligationWithEvidenceAuthority
      handoffConfig authorityBindings (authorityLedger Truth ["wrong.subject"] expectedScope) resolved of
    Left (EvidenceFactAuthoritySubjectMismatch _ _ _ _ _) -> True
    _ -> False

scopeMismatchRejected :: Bool
scopeMismatchRejected =
  case handoffResolvedObligationWithEvidenceAuthority
      handoffConfig authorityBindings (authorityLedger Truth expectedSubjects "wrong.scope") resolved of
    Left (EvidenceFactAuthorityScopeMismatch _ _ _ _ _) -> True
    _ -> False

missingEvidenceRejected :: Bool
missingEvidenceRejected =
  case handoffResolvedObligationWithEvidenceAuthority
      handoffConfig authorityBindings emptyLedger resolved of
    Left (MissingAuthorityEvidenceEntry _ _ _ _) -> True
    _ -> False

authorityBindings :: Map.Map (Name, Int) EvidenceFactAuthorityBinding
authorityBindings = Map.singleton
  (evidenceName, evidenceIndex)
  EvidenceFactAuthorityBinding
    { authorityEvidenceEntryId = supportEvidenceId
    , authoritySubjectIds = expectedSubjects
    , authorityScope = expectedScope
    }

expectedSubjects :: [Text]
expectedSubjects = ["semantic.subject"]

expectedScope :: Text
expectedScope = "test.scope"

evidenceName :: Name
evidenceName = Name "proof"

evidenceIndex :: Int
evidenceIndex = 1

supportEvidenceId :: EvidenceEntryId
supportEvidenceId = EvidenceEntryId "evidence.test.authority.proof.1"

resolved :: ResolvedObligation
resolved = ResolvedObligation
  { resolvedObligation = consumerObligation
  , resolvedCanonicalProposition = Truth
  , resolvedPrerequisites = []
  , resolvedDisposition = StaticallyDischarged StaticByCertificate
      { staticCertificateProducer = "test-producer"
      , staticCertificateChecker = "test-checker"
      , staticCertificate = CertificateAssumption
          (EvidenceFact evidenceName evidenceIndex)
          Truth
      }
  }

consumerObligation :: Obligation
consumerObligation = Obligation
  { obligationId = ObligationId "test.authority.consumer"
  , obligationProposition = Truth
  , obligationOrigin = "test"
  , obligationScope = expectedScope
  , obligationRequiredPoint = "test.authority.required"
  }

handoffConfig :: HandoffConfig
handoffConfig = HandoffConfig
  { handoffRevisionKind = const "Test"
  , handoffRepresentation = const "Core"
  , handoffSubjectIds = const ["consumer.subject"]
  , handoffContextIds = const ["context"]
  , handoffAcceptanceRule = const (AcceptEntry KernelChecked (EvidenceRole "establishes"))
  }

authorityLedger :: Proposition -> [Text] -> Text -> AssuranceLedger
authorityLedger proposition subjects scope =
  let obligation = Obligation
        { obligationId = ObligationId "test.authority.support"
        , obligationProposition = proposition
        , obligationOrigin = "test"
        , obligationScope = scope
        , obligationRequiredPoint = "test.authority.support.required"
        }
      revision = revisionFromCoreObligation
        obligation
        "EvidenceFact"
        "Core"
        subjects
        []
        (AcceptEntry KernelChecked (EvidenceRole "establishes"))
        []
      provisional = EvidenceEntry
        { evidenceEntryId = supportEvidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = revisionId revision
        , evidenceAssuranceKind = KernelChecked
        , evidenceRole = EvidenceRole "establishes"
        , evidenceProducer = "test-producer"
        , evidenceChecker = "test-checker"
        , evidenceArtifact = Nothing
        , evidenceInputDigests = []
        , evidenceAssumptions = []
        , evidenceDependsOn = []
        , evidenceValidityScope = ValidityScope Map.empty
        , evidenceResult = EvidenceAccepted
        , evidenceJustifies = ["authoritative fact"]
        , evidenceRuntimeMechanism = Nothing
        , evidenceRuntimeResidue = []
        , evidenceCostRefs = []
        }
      evidence = provisional
        { evidenceEntryDigest = deriveEvidenceEntryDigest provisional }
  in emptyLedger
      { ledgerRevisions = Map.singleton (revisionId revision) revision
      , ledgerEvidence = Map.singleton supportEvidenceId evidence
      }
