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
  ( MissingProofDispositionDecision (..)
  , MissingProofDispositionProposal (..)
  , MissingProofDispositionRejection (..)
  , ProofAttemptResult (..)
  , ProofProducerAttempt (..)
  , ProofProducerFailure (..)
  , assumptionClosureGraphRevision
  , assumptionClosureObligationRevision
  , assumptionClosurePolicyRevision
  , assumptionClosureRole
  , evaluateMissingProofDisposition
  , exportClosureGraphRevision
  , exportClosureObligationRevision
  , exportClosurePolicyRevision
  , runProofProducerAttempt
  , unresolvedProofObligationRevision
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  graph <- graphOrFail
    [assumptionInput, exportInput]
    (Set.singleton assumptionObligationId)
  staticOnlyGraph <- graphOrFail
    [staticOnlyAssumptionInput]
    (Set.singleton assumptionObligationId)
  let assumptionRevision = revisionFor graph assumptionObligationId
      exportRevision = revisionFor graph exportObligationId
      staticOnlyRevision = revisionFor staticOnlyGraph assumptionObligationId
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
            testAssumptionAcceptanceBinding
              graph
              staticOnlyGraph
              assumptionRevision
              staticOnlyRevision
              assumption)
        , ("assumption permission, validity, and policy are independent gates",
            testAssumptionGates graph assumptionRevision assumption)
        , ("explicit permitted export boundary is admitted",
            testExportAdmitted graph exportRevision exportEntry)
        , ("in-scope obligation cannot silently become export",
            testInScopeExportRejected graph assumptionRevision)
        , ("export revision, destination, validity, and policy are independent gates",
            testExportGates graph exportRevision exportEntry)
        , ("content-bound assumption and export records reject stale digests",
            testDigestBinding
              graph
              assumptionRevision
              exportRevision
              assumption
              exportEntry)
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

assumptionObligationId :: ObligationId
assumptionObligationId = ObligationId "ver008.assumption"

exportObligationId :: ObligationId
exportObligationId = ObligationId "ver008.export"

assumptionObligation :: Obligation
assumptionObligation = Obligation
  { obligationId = assumptionObligationId
  , obligationProposition = LessEqual (RefNat 1) (RefNat 2)
  , obligationOrigin = "checked.callable:ver008.assumption"
  , obligationScope = "application:ver008"
  , obligationRequiredPoint = "before:ver008.assumption"
  }

exportObligation :: Obligation
exportObligation = Obligation
  { obligationId = exportObligationId
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
  evaluateMissingProofDisposition
      graph permissivePolicy verificationContext assumptionRevision Nothing
      == MissingProofRemainsUnresolved assumptionRevision
    && evaluateMissingProofDisposition
      graph permissivePolicy verificationContext exportRevision Nothing
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
        && evaluateMissingProofDisposition
          graph permissivePolicy verificationContext revision Nothing
          == MissingProofRemainsUnresolved revision
    _ -> False

testAssumptionAdmitted
  :: VerificationObligationGraph
  -> RevisionId
  -> Assumption
  -> Bool
testAssumptionAdmitted graph revision assumption =
  case evaluateMissingProofDisposition
      graph
      permissivePolicy
      verificationContext
      revision
      (Just (SelectAssumptionBoundary assumptionRole assumption)) of
    MissingProofAssumptionAdmitted record ->
      assumptionClosureGraphRevision record == verificationGraphRevision graph
        && assumptionClosureObligationRevision record == revision
        && assumptionClosurePolicyRevision record
          == applicationAssurancePolicyRevision permissivePolicy
        && assumptionClosureRole record == assumptionRole
    _ -> False

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
        evaluateMissingProofDisposition
          graph
          permissivePolicy
          verificationContext
          revision
          (Just (SelectAssumptionBoundary wrongRole assumption))
          == MissingProofDispositionRejected
              (MissingProofAssumptionRoleRejected revision wrongRole)
      staticOnlyRejected =
        evaluateMissingProofDisposition
          staticOnlyGraph
          permissivePolicy
          verificationContext
          staticOnlyRevision
          (Just (SelectAssumptionBoundary assumptionRole assumption))
          == MissingProofDispositionRejected
              (MissingProofAssumptionAcceptanceRuleRejected
                staticOnlyRevision
                assumptionRole)
  in wrongRoleRejected && staticOnlyRejected

testAssumptionGates
  :: VerificationObligationGraph
  -> RevisionId
  -> Assumption
  -> Bool
testAssumptionGates graph revision assumption =
  let deniedContext = verificationContext
        { verificationPermittedAssumptions = Set.empty }
      staleContext = verificationContext
        { verificationValidityContext =
            Map.singleton "architecture_revision" "arch.ver008.v2" }
      proposal = Just (SelectAssumptionBoundary assumptionRole assumption)
      denied =
        evaluateMissingProofDisposition graph permissivePolicy deniedContext revision proposal
          == MissingProofDispositionRejected
              (MissingProofAssumptionNotPermitted assumptionKey)
      stale =
        evaluateMissingProofDisposition graph permissivePolicy staleContext revision proposal
          == MissingProofDispositionRejected
              (MissingProofAssumptionValidityScopeMismatch assumptionKey)
      strict =
        evaluateMissingProofDisposition graph strictPolicy verificationContext revision proposal
          == MissingProofDispositionRejected
              (MissingProofPolicyRejected
                revision
                AssumptionDependent
                (applicationAssurancePolicyRevision strictPolicy))
  in denied && stale && strict

testExportAdmitted
  :: VerificationObligationGraph
  -> RevisionId
  -> ExportEntry
  -> Bool
testExportAdmitted graph revision exportEntry =
  case evaluateMissingProofDisposition
      graph
      permissivePolicy
      verificationContext
      revision
      (Just (SelectExportBoundary exportEntry)) of
    MissingProofExportAdmitted record ->
      exportClosureGraphRevision record == verificationGraphRevision graph
        && exportClosureObligationRevision record == revision
        && exportClosurePolicyRevision record
          == applicationAssurancePolicyRevision permissivePolicy
    _ -> False

testInScopeExportRejected :: VerificationObligationGraph -> RevisionId -> Bool
testInScopeExportRejected graph revision =
  evaluateMissingProofDisposition
      graph
      permissivePolicy
      verificationContext
      revision
      (Just (SelectExportBoundary (validExport revision)))
    == MissingProofDispositionRejected
        (MissingProofExportInsideCertificationScope revision)

testExportGates
  :: VerificationObligationGraph
  -> RevisionId
  -> ExportEntry
  -> Bool
testExportGates graph revision exportEntry =
  let wrongRevision = RevisionId "rev.ver008.wrong-export-target"
      wrongRevisionEntry = validExport wrongRevision
      wrongBoundary0 = exportEntry
        { exportDestinationBoundary = "deployment:other" }
      wrongBoundary = wrongBoundary0
        { exportDigest = deriveExportDigest wrongBoundary0 }
      staleScope = ValidityScope
        (Map.singleton "architecture_revision" "arch.ver008.v2")
      stale0 = exportEntry { exportValidityScope = staleScope }
      stale = stale0 { exportDigest = deriveExportDigest stale0 }
      wrongRevisionRejected =
        evaluateMissingProofDisposition
          graph permissivePolicy verificationContext revision
          (Just (SelectExportBoundary wrongRevisionEntry))
          == MissingProofDispositionRejected
              (MissingProofExportRevisionMismatch revision wrongRevision)
      boundaryRejected =
        evaluateMissingProofDisposition
          graph permissivePolicy verificationContext revision
          (Just (SelectExportBoundary wrongBoundary))
          == MissingProofDispositionRejected
              (MissingProofExportBoundaryNotPermitted
                exportKey
                "deployment:other")
      staleRejected =
        evaluateMissingProofDisposition
          graph permissivePolicy verificationContext revision
          (Just (SelectExportBoundary stale))
          == MissingProofDispositionRejected
              (MissingProofExportValidityScopeMismatch exportKey)
      policyRejected =
        evaluateMissingProofDisposition
          graph strictPolicy verificationContext revision
          (Just (SelectExportBoundary exportEntry))
          == MissingProofDispositionRejected
              (MissingProofPolicyRejected
                revision
                Exported
                (applicationAssurancePolicyRevision strictPolicy))
  in wrongRevisionRejected && boundaryRejected && staleRejected && policyRejected

testDigestBinding
  :: VerificationObligationGraph
  -> RevisionId
  -> RevisionId
  -> Assumption
  -> ExportEntry
  -> Bool
testDigestBinding graph assumptionRevision exportRevision assumption exportEntry =
  let staleAssumption = assumption
        { assumptionStatement = "silently changed" }
      staleExport = exportEntry
        { exportDestinationBoundary = "deployment:changed" }
      assumptionRejected =
        case evaluateMissingProofDisposition
            graph
            permissivePolicy
            verificationContext
            assumptionRevision
            (Just (SelectAssumptionBoundary assumptionRole staleAssumption)) of
          MissingProofDispositionRejected
            (MissingProofAssumptionDigestMismatch key _ _) -> key == assumptionKey
          _ -> False
      exportRejected =
        case evaluateMissingProofDisposition
            graph
            permissivePolicy
            verificationContext
            exportRevision
            (Just (SelectExportBoundary staleExport)) of
          MissingProofDispositionRejected
            (MissingProofExportDigestMismatch key _ _) -> key == exportKey
          _ -> False
  in assumptionRejected && exportRejected

testUnknownRevision :: VerificationObligationGraph -> Bool
testUnknownRevision graph =
  let unknown = RevisionId "rev.ver008.unknown"
  in evaluateMissingProofDisposition
      graph permissivePolicy verificationContext unknown Nothing
      == MissingProofDispositionRejected (MissingProofUnknownRevision unknown)
