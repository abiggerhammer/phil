{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Assurance
  ( AcceptanceRule (..)
  , Assumption (..)
  , AssumptionId (..)
  , AssuranceKind (..)
  , Digest (..)
  , EvidenceRole (..)
  , ExportEntry (..)
  , ExportId (..)
  , RevisionId (..)
  , ValidityScope (..)
  , VerificationContext (..)
  , deriveAssumptionDigest
  , deriveExportDigest
  , emptyVerificationContext
  , revisionObligationId
  )
import Phil.Core.Checker (emptyCheckState)
import Phil.Core.Syntax
  ( Obligation (..)
  , ObligationId (..)
  , Proposition (..)
  , RefTerm (..)
  )
import Phil.Verification
  ( ApplicationAssurancePolicy (..)
  , AssurancePolicyRevision (..)
  , VerificationDisposition (..)
  , VerificationObligationGraph (..)
  , VerificationObligationInput (..)
  , buildVerificationObligationGraph
  )
import Phil.Verification.ProofEvidence
  ( AssumptionClosureRecord
  , ExportClosureRecord
  , MissingProofDispositionDecision (..)
  , MissingProofDispositionProposal (..)
  , MissingProofDispositionRejection (..)
  , ProofAttemptResult (..)
  , ProofProducerAttempt (..)
  , ProofProducerFailure (..)
  , assumptionClosureAssumption
  , assumptionClosureGraphRevision
  , assumptionClosureObligationRevision
  , assumptionClosurePolicyRevision
  , assumptionClosureRole
  , evaluateMissingProofDisposition
  , exportClosureExport
  , exportClosureGraphRevision
  , exportClosureObligationRevision
  , exportClosurePolicyRevision
  , runProofProducerAttempt
  , unresolvedProofObligationRevision
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  graph <- graphOrFail [assumptionInput, exportInput] (Set.singleton assumptionId)
  staticOnlyGraph <- graphOrFail [staticOnlyAssumptionInput] (Set.singleton assumptionId)
  let assumptionRevision = revisionFor graph assumptionId
      exportRevision = revisionFor graph exportIdObligation
      staticOnlyRevision = revisionFor staticOnlyGraph assumptionId
      assumption = validAssumption
      exportEntry = validExport exportRevision
      checks =
        [ ("proof absence remains unresolved under permissive policy and context",
            testNoProposalRemainsUnresolved graph assumptionRevision exportRevision)
        , ("producer timeout does not synthesize assumption or export",
            testProducerFailureRemainsUnresolved graph assumptionRevision)
        , ("explicit permitted assumption boundary is admitted",
            testAssumptionAdmitted graph assumptionRevision assumption)
        , ("assumption requires exact ADR-010 acceptance rule and role",
            testAssumptionAcceptanceBinding graph staticOnlyGraph assumptionRevision staticOnlyRevision assumption)
        , ("unpermitted assumption boundary rejects",
            testAssumptionPermissionRequired graph assumptionRevision assumption)
        , ("assumption validity scope must match exact build context",
            testAssumptionValidityRequired graph assumptionRevision assumption)
        , ("policy must independently permit AssumptionDependent",
            testAssumptionPolicyRequired graph assumptionRevision assumption)
        , ("explicit permitted export boundary is admitted",
            testExportAdmitted graph exportRevision exportEntry)
        , ("in-scope obligation cannot silently become export",
            testInScopeExportRejected graph assumptionRevision)
        , ("export must name the exact obligation revision",
            testExportRevisionBinding graph exportRevision)
        , ("unpermitted export destination rejects",
            testExportPermissionRequired graph exportRevision exportEntry)
        , ("export validity scope must match exact build context",
            testExportValidityRequired graph exportRevision exportEntry)
        , ("content-bound assumption and export records reject stale digests",
            testDigestBinding graph assumptionRevision exportRevision assumption exportEntry)
        , ("policy must independently permit Exported",
            testExportPolicyRequired graph exportRevision exportEntry)
        , ("unknown revision cannot receive any missing-proof disposition",
            testUnknownRevision graph)
        ]
  mapM_ report checks
  unless (and (map snd checks)) exitFailure
  where
    report (label, True) = putStrLn ("PASS: VER-008 " ++ label)
    report (label, False) = putStrLn ("FAIL: VER-008 " ++ label)

graphOrFail
  :: [VerificationObligationInput]
  -> Set.Set ObligationId
  -> IO VerificationObligationGraph
graphOrFail inputs scope =
  case buildVerificationObligationGraph inputs scope of
    Left errorValue -> failCase ("could not build graph: " ++ show errorValue)
    Right graph -> pure graph

failCase :: String -> IO a
failCase message = putStrLn ("FAIL: VER-008 " ++ message) >> exitFailure

assumptionId :: ObligationId
assumptionId = ObligationId "ver008.assumption"

exportIdObligation :: ObligationId
exportIdObligation = ObligationId "ver008.export"

assumptionObligation :: Obligation
assumptionObligation = Obligation
  { obligationId = assumptionId
  , obligationProposition = LessEqual (RefNat 1) (RefNat 2)
  , obligationOrigin = "checked.callable:ver008.assumption"
  , obligationScope = "application:ver008"
  , obligationRequiredPoint = "before:ver008.assumption"
  }

exportObligation :: Obligation
exportObligation = Obligation
  { obligationId = exportIdObligation
  , obligationProposition = Equal (RefNat 2) (RefNat 2)
  , obligationOrigin = "checked.callable:ver008.export"
  , obligationScope = "application:ver008"
  , obligationRequiredPoint = "boundary:ver008.export"
  }

assumptionRole :: EvidenceRole
assumptionRole = EvidenceRole "assumption_boundary"

assumptionInput :: VerificationObligationInput
assumptionInput = VerificationObligationInput
  { verificationInputObligation = assumptionObligation
  , verificationInputKind = "semantic"
  , verificationInputRepresentation = "phil-core/proposition-v1"
  , verificationInputSubjectIds = ["subject:ver008.assumption"]
  , verificationInputContextIds = ["context:ver008"]
  , verificationInputAcceptanceRule = AcceptAny
      [ AcceptEntry CertificateChecked (EvidenceRole "static-proof")
      , AcceptEntry Assumed assumptionRole
      ]
  , verificationInputDependencies = Set.empty
  }

staticOnlyAssumptionInput :: VerificationObligationInput
staticOnlyAssumptionInput = assumptionInput
  { verificationInputAcceptanceRule =
      AcceptEntry CertificateChecked (EvidenceRole "static-proof")
  }

exportInput :: VerificationObligationInput
exportInput = VerificationObligationInput
  { verificationInputObligation = exportObligation
  , verificationInputKind = "semantic"
  , verificationInputRepresentation = "phil-core/proposition-v1"
  , verificationInputSubjectIds = ["subject:ver008.export"]
  , verificationInputContextIds = ["context:ver008"]
  , verificationInputAcceptanceRule =
      AcceptEntry CertificateChecked (EvidenceRole "static-proof")
  , verificationInputDependencies = Set.empty
  }

permissivePolicy :: ApplicationAssurancePolicy
permissivePolicy = ApplicationAssurancePolicy
  { applicationAssurancePolicyRevision = AssurancePolicyRevision "policy.ver008.permissive.v1"
  , applicationAssurancePolicyPermittedDispositions = Set.fromList
      [ AssumptionDependent
      , Exported
      , StaticallyDischarged
      , Unresolved
      ]
  }

strictPolicy :: ApplicationAssurancePolicy
strictPolicy = ApplicationAssurancePolicy
  { applicationAssurancePolicyRevision = AssurancePolicyRevision "policy.ver008.strict.v1"
  , applicationAssurancePolicyPermittedDispositions = Set.fromList
      [ StaticallyDischarged
      , Unresolved
      ]
  }

assumptionKey :: AssumptionId
assumptionKey = AssumptionId "assumption.ver008.trusted-input"

exportKey :: ExportId
exportKey = ExportId "export.ver008.deployment"

boundaryValidity :: ValidityScope
boundaryValidity = ValidityScope (Map.fromList
  [ ("architecture_revision", "arch.ver008.v1")
  , ("compilation_profile", "checked-runtime")
  , ("target", "native")
  ])

verificationContext :: VerificationContext
verificationContext = emptyVerificationContext
  { verificationTarget = "native"
  , verificationCompilationProfile = "checked-runtime"
  , verificationPermittedAssumptions = Set.singleton assumptionKey
  , verificationPermittedExportBoundaries = Set.singleton "deployment:ops"
  , verificationValidityContext = Map.singleton "architecture_revision" "arch.ver008.v1"
  }

validAssumption :: Assumption
validAssumption = provisional
  { assumptionDigest = deriveAssumptionDigest provisional }
  where
    provisional = Assumption
      { assumptionId = assumptionKey
      , assumptionDigest = Digest ""
      , assumptionStatement = "trusted ingress validates the external claim"
      , assumptionScope = "application:ver008"
      , assumptionOwnerBoundary = "architecture:trusted-ingress"
      , assumptionRationale = "explicit architecture boundary"
      , assumptionValidityScope = boundaryValidity
      }

validExport :: RevisionId -> ExportEntry
validExport revision = provisional
  { exportDigest = deriveExportDigest provisional }
  where
    provisional = ExportEntry
      { exportId = exportKey
      , exportDigest = Digest ""
      , exportObligationRevision = revision
      , exportDestinationBoundary = "deployment:ops"
      , exportDerivedObligationId = ObligationId "ver008.export.deployment"
      , exportValidityScope = boundaryValidity
      }

revisionFor :: VerificationObligationGraph -> ObligationId -> RevisionId
revisionFor graph wanted =
  case
    [ revision
    | (revision, node) <- Map.toAscList (verificationGraphNodes graph)
    , revisionObligationId node == wanted
    ] of
    [revision] -> revision
    _ -> error ("VER-008 fixture revision not unique: " ++ show wanted)

testNoProposalRemainsUnresolved
  :: VerificationObligationGraph
  -> RevisionId
  -> RevisionId
  -> Bool
testNoProposalRemainsUnresolved graph assumptionRevision exportRevision =
  evaluateMissingProofDisposition graph permissivePolicy verificationContext assumptionRevision Nothing
      == MissingProofRemainsUnresolved assumptionRevision
    && evaluateMissingProofDisposition graph permissivePolicy verificationContext exportRevision Nothing
      == MissingProofRemainsUnresolved exportRevision

testProducerFailureRemainsUnresolved
  :: VerificationObligationGraph
  -> RevisionId
  -> Bool
testProducerFailureRemainsUnresolved graph revision =
  case runProofProducerAttempt graph emptyCheckState []
      (ProofProducerDidNotProduce
        { proofAttemptProducer = "replaceable.ver008.producer"
        , proofAttemptObligationRevision = revision
        , proofAttemptFailure = ProducerTimedOut
        }) of
    Right (ProofAttemptUnresolved unresolved) ->
      unresolvedProofObligationRevision unresolved == revision
        && evaluateMissingProofDisposition graph permissivePolicy verificationContext revision Nothing
          == MissingProofRemainsUnresolved revision
    _ -> False

testAssumptionAdmitted
  :: VerificationObligationGraph
  -> RevisionId
  -> Assumption
  -> Bool
testAssumptionAdmitted graph revision assumption =
  case evaluateMissingProofDisposition graph permissivePolicy verificationContext revision
      (Just (SelectAssumptionBoundary assumptionRole assumption)) of
    MissingProofAssumptionAdmitted record -> assumptionRecordMatches graph revision assumption record
    _ -> False

assumptionRecordMatches
  :: VerificationObligationGraph
  -> RevisionId
  -> Assumption
  -> AssumptionClosureRecord
  -> Bool
assumptionRecordMatches graph revision assumption record =
  assumptionClosureGraphRevision record == verificationGraphRevision graph
    && assumptionClosureObligationRevision record == revision
    && assumptionClosurePolicyRevision record
      == applicationAssurancePolicyRevision permissivePolicy
    && assumptionClosureRole record == assumptionRole
    && assumptionClosureAssumption record == assumption

testAssumptionAcceptanceBinding
  :: VerificationObligationGraph
  -> VerificationObligationGraph
  -> RevisionId
  -> RevisionId
  -> Assumption
  -> Bool
testAssumptionAcceptanceBinding graph staticOnlyGraph revision staticOnlyRevision assumption =
  let wrongRole = EvidenceRole "static-proof"
      wrongRoleRejected =
        evaluateMissingProofDisposition graph permissivePolicy verificationContext revision
          (Just (SelectAssumptionBoundary wrongRole assumption))
          == MissingProofDispositionRejected
              (MissingProofAssumptionRoleRejected revision wrongRole)
      staticOnlyRejected =
        evaluateMissingProofDisposition staticOnlyGraph permissivePolicy verificationContext staticOnlyRevision
          (Just (SelectAssumptionBoundary assumptionRole assumption))
          == MissingProofDispositionRejected
              (MissingProofAssumptionAcceptanceRuleRejected staticOnlyRevision assumptionRole)
  in wrongRoleRejected && staticOnlyRejected

testAssumptionPermissionRequired
  :: VerificationObligationGraph
  -> RevisionId
  -> Assumption
  -> Bool
testAssumptionPermissionRequired graph revision assumption =
  let deniedContext = verificationContext { verificationPermittedAssumptions = Set.empty }
  in evaluateMissingProofDisposition graph permissivePolicy deniedContext revision
      (Just (SelectAssumptionBoundary assumptionRole assumption))
      == MissingProofDispositionRejected
          (MissingProofAssumptionNotPermitted assumptionKey)

testAssumptionValidityRequired
  :: VerificationObligationGraph
  -> RevisionId
  -> Assumption
  -> Bool
testAssumptionValidityRequired graph revision assumption =
  let staleContext = verificationContext
        { verificationValidityContext = Map.singleton "architecture_revision" "arch.ver008.v2" }
  in evaluateMissingProofDisposition graph permissivePolicy staleContext revision
      (Just (SelectAssumptionBoundary assumptionRole assumption))
      == MissingProofDispositionRejected
          (MissingProofAssumptionValidityScopeMismatch assumptionKey)

testAssumptionPolicyRequired
  :: VerificationObligationGraph
  -> RevisionId
  -> Assumption
  -> Bool
testAssumptionPolicyRequired graph revision assumption =
  evaluateMissingProofDisposition graph strictPolicy verificationContext revision
      (Just (SelectAssumptionBoundary assumptionRole assumption))
    == MissingProofDispositionRejected
        (MissingProofPolicyRejected
          revision
          AssumptionDependent
          (applicationAssurancePolicyRevision strictPolicy))

testExportAdmitted
  :: VerificationObligationGraph
  -> RevisionId
  -> ExportEntry
  -> Bool
testExportAdmitted graph revision exportEntry =
  case evaluateMissingProofDisposition graph permissivePolicy verificationContext revision
      (Just (SelectExportBoundary exportEntry)) of
    MissingProofExportAdmitted record -> exportRecordMatches graph revision exportEntry record
    _ -> False

exportRecordMatches
  :: VerificationObligationGraph
  -> RevisionId
  -> ExportEntry
  -> ExportClosureRecord
  -> Bool
exportRecordMatches graph revision exportEntry record =
  exportClosureGraphRevision record == verificationGraphRevision graph
    && exportClosureObligationRevision record == revision
    && exportClosurePolicyRevision record
      == applicationAssurancePolicyRevision permissivePolicy
    && exportClosureExport record == exportEntry

testInScopeExportRejected :: VerificationObligationGraph -> RevisionId -> Bool
testInScopeExportRejected graph revision =
  evaluateMissingProofDisposition graph permissivePolicy verificationContext revision
      (Just (SelectExportBoundary (validExport revision)))
    == MissingProofDispositionRejected
        (MissingProofExportInsideCertificationScope revision)

testExportRevisionBinding :: VerificationObligationGraph -> RevisionId -> Bool
testExportRevisionBinding graph revision =
  let wrongRevision = RevisionId "rev.ver008.wrong-export-target"
      wrongEntry = validExport wrongRevision
  in evaluateMissingProofDisposition graph permissivePolicy verificationContext revision
      (Just (SelectExportBoundary wrongEntry))
      == MissingProofDispositionRejected
          (MissingProofExportRevisionMismatch revision wrongRevision)

testExportPermissionRequired
  :: VerificationObligationGraph
  -> RevisionId
  -> ExportEntry
  -> Bool
testExportPermissionRequired graph revision exportEntry =
  let changed = exportEntry { exportDestinationBoundary = "deployment:other" }
      redigested = changed { exportDigest = deriveExportDigest changed }
  in evaluateMissingProofDisposition graph permissivePolicy verificationContext revision
      (Just (SelectExportBoundary redigested))
      == MissingProofDispositionRejected
          (MissingProofExportBoundaryNotPermitted exportKey "deployment:other")

testExportValidityRequired
  :: VerificationObligationGraph
  -> RevisionId
  -> ExportEntry
  -> Bool
testExportValidityRequired graph revision exportEntry =
  let staleScope = ValidityScope (Map.singleton "architecture_revision" "arch.ver008.v2")
      changed = exportEntry { exportValidityScope = staleScope }
      redigested = changed { exportDigest = deriveExportDigest changed }
  in evaluateMissingProofDisposition graph permissivePolicy verificationContext revision
      (Just (SelectExportBoundary redigested))
      == MissingProofDispositionRejected
          (MissingProofExportValidityScopeMismatch exportKey)

testDigestBinding
  :: VerificationObligationGraph
  -> RevisionId
  -> RevisionId
  -> Assumption
  -> ExportEntry
  -> Bool
testDigestBinding graph assumptionRevision exportRevision assumption exportEntry =
  let staleAssumption = assumption { assumptionStatement = "silently changed" }
      staleExport = exportEntry { exportDestinationBoundary = "deployment:changed" }
      assumptionRejected =
        case evaluateMissingProofDisposition graph permissivePolicy verificationContext assumptionRevision
            (Just (SelectAssumptionBoundary assumptionRole staleAssumption)) of
          MissingProofDispositionRejected
            (MissingProofAssumptionDigestMismatch key _ _) -> key == assumptionKey
          _ -> False
      exportRejected =
        case evaluateMissingProofDisposition graph permissivePolicy verificationContext exportRevision
            (Just (SelectExportBoundary staleExport)) of
          MissingProofDispositionRejected
            (MissingProofExportDigestMismatch key _ _) -> key == exportKey
          _ -> False
  in assumptionRejected && exportRejected

testExportPolicyRequired
  :: VerificationObligationGraph
  -> RevisionId
  -> ExportEntry
  -> Bool
testExportPolicyRequired graph revision exportEntry =
  evaluateMissingProofDisposition graph strictPolicy verificationContext revision
      (Just (SelectExportBoundary exportEntry))
    == MissingProofDispositionRejected
        (MissingProofPolicyRejected
          revision
          Exported
          (applicationAssurancePolicyRevision strictPolicy))

testUnknownRevision :: VerificationObligationGraph -> Bool
testUnknownRevision graph =
  let unknown = RevisionId "rev.ver008.unknown"
  in evaluateMissingProofDisposition graph permissivePolicy verificationContext unknown Nothing
      == MissingProofDispositionRejected (MissingProofUnknownRevision unknown)
