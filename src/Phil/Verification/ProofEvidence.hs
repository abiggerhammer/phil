{-# LANGUAGE OverloadedStrings #-}

module Phil.Verification.ProofEvidence
  ( ProofProposal (..)
  , ProofEvidenceError (..)
  , decisionCertificateEvidenceFormat
  , CheckedProofEvidence
  , checkedProofGraphRevision
  , checkedProofObligationRevision
  , checkedProofProducer
  , checkedProofChecker
  , checkedProofEvidenceFormat
  , checkedProofSubjectIds
  , checkedProofContextIds
  , checkedProofCertificate
  , checkedProofProposition
  , checkedProofState
  , checkedProofAssumptions
  , checkProofProposal
  , ProofProducerFailure (..)
  , ProofProducerAttempt (..)
  , UnresolvedProofAttempt
  , unresolvedProofGraphRevision
  , unresolvedProofObligationRevision
  , unresolvedProofProducer
  , unresolvedProofFailure
  , ProofAttemptResult (..)
  , runProofProducerAttempt
  , ReusableProofEvidence
  , reusableCheckedProofEvidence
  , reusableProofDependencies
  , reusableProofValidityScope
  , EvidenceReuseError (..)
  , EvidenceReuseStaleness (..)
  , EvidenceReuseDecision (..)
  , prepareReusableProofEvidence
  , evaluateReusableProofEvidence
  , MissingProofDispositionProposal (..)
  , MissingProofDispositionRejection (..)
  , AssumptionClosureRecord
  , assumptionClosureGraphRevision
  , assumptionClosureObligationRevision
  , assumptionClosurePolicyRevision
  , assumptionClosureRole
  , assumptionClosureAssumption
  , ExportClosureRecord
  , exportClosureGraphRevision
  , exportClosureObligationRevision
  , exportClosurePolicyRevision
  , exportClosureExport
  , MissingProofDispositionDecision (..)
  , evaluateMissingProofDisposition
  ) where

import Data.List (sort)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types
  ( AcceptanceRule (..)
  , Assumption (..)
  , AssumptionId (..)
  , AssuranceKind (..)
  , Digest
  , EvidenceRole (..)
  , ExportEntry (..)
  , ExportId (..)
  , ObligationRevision (..)
  , RevisionId
  , ValidityScope (..)
  , VerificationContext (..)
  , deriveAssumptionDigest
  , deriveExportDigest
  , renderPropositionCanonical
  )
import Phil.Core.Checker (CheckState)
import Phil.Core.Decision
  ( CertificateError
  , DecisionCertificate
  , SolverAssumption
  , certificateCheckerId
  , checkDecisionCertificate
  )
import Phil.Core.Syntax (Proposition)
import Phil.Verification
  ( ApplicationAssurancePolicy (..)
  , AssurancePolicyRevision
  , VerificationDisposition (..)
  , VerificationObligationGraph (..)
  )

-- | Canonical application-verification evidence format accepted by this
-- competent checker boundary. Other proof formats require their own checker.
decisionCertificateEvidenceFormat :: Text
decisionCertificateEvidenceFormat = "phil-core/decision-certificate-v1"

data ProofProposal = ProofProposal
  { proofProposalProducer :: Text
  , proofProposalObligationRevision :: RevisionId
  , proofProposalEvidenceFormat :: Text
  , proofProposalSubjectIds :: [Text]
  , proofProposalContextIds :: [Text]
  , proofProposalProposition :: Proposition
  , proofProposalCertificate :: DecisionCertificate
  }
  deriving (Eq, Show)

data ProofEvidenceError
  = EmptyProofProducerId
  | UnknownProofObligationRevision RevisionId
  | ProofRevisionOutsideCertificationScope RevisionId
  | MalformedProofEvidence Text
  | UnsupportedProofEvidenceFormat Text
  | ProofEvidenceSubjectMismatch RevisionId [Text] [Text]
  | ProofEvidenceContextMismatch RevisionId [Text] [Text]
  | ProofPropositionRevisionMismatch RevisionId Text Text
  | ProofCertificateRejected RevisionId CertificateError
  deriving (Eq, Show)

data CheckedProofEvidence = CheckedProofEvidence
  Digest
  RevisionId
  Text
  Text
  Text
  [Text]
  [Text]
  DecisionCertificate
  Proposition
  CheckState
  [SolverAssumption]
  deriving (Eq, Show)

checkedProofGraphRevision :: CheckedProofEvidence -> Digest
checkedProofGraphRevision (CheckedProofEvidence graphRevision _ _ _ _ _ _ _ _ _ _) = graphRevision

checkedProofObligationRevision :: CheckedProofEvidence -> RevisionId
checkedProofObligationRevision (CheckedProofEvidence _ revision _ _ _ _ _ _ _ _ _) = revision

checkedProofProducer :: CheckedProofEvidence -> Text
checkedProofProducer (CheckedProofEvidence _ _ producer _ _ _ _ _ _ _ _) = producer

checkedProofChecker :: CheckedProofEvidence -> Text
checkedProofChecker (CheckedProofEvidence _ _ _ checker _ _ _ _ _ _ _) = checker

checkedProofEvidenceFormat :: CheckedProofEvidence -> Text
checkedProofEvidenceFormat (CheckedProofEvidence _ _ _ _ evidenceFormat _ _ _ _ _ _) = evidenceFormat

checkedProofSubjectIds :: CheckedProofEvidence -> [Text]
checkedProofSubjectIds (CheckedProofEvidence _ _ _ _ _ subjects _ _ _ _ _) = subjects

checkedProofContextIds :: CheckedProofEvidence -> [Text]
checkedProofContextIds (CheckedProofEvidence _ _ _ _ _ _ contexts _ _ _ _) = contexts

checkedProofCertificate :: CheckedProofEvidence -> DecisionCertificate
checkedProofCertificate (CheckedProofEvidence _ _ _ _ _ _ _ certificate _ _ _) = certificate

checkedProofProposition :: CheckedProofEvidence -> Proposition
checkedProofProposition (CheckedProofEvidence _ _ _ _ _ _ _ _ proposition _ _) = proposition

checkedProofState :: CheckedProofEvidence -> CheckState
checkedProofState (CheckedProofEvidence _ _ _ _ _ _ _ _ _ state _) = state

checkedProofAssumptions :: CheckedProofEvidence -> [SolverAssumption]
checkedProofAssumptions (CheckedProofEvidence _ _ _ _ _ _ _ _ _ _ assumptions) = assumptions

checkProofProposal
  :: VerificationObligationGraph
  -> CheckState
  -> [SolverAssumption]
  -> ProofProposal
  -> Either ProofEvidenceError CheckedProofEvidence
checkProofProposal graph state rawAssumptions proposal
  | Text.null (Text.strip (proofProposalProducer proposal)) = Left EmptyProofProducerId
  | otherwise = do
      target <- requireProofTarget graph targetRevision
      evidenceFormat <- validateEvidenceFormat (proofProposalEvidenceFormat proposal)
      subjects <- canonicalEvidenceIds "subject" (proofProposalSubjectIds proposal)
      contexts <- canonicalEvidenceIds "context" (proofProposalContextIds proposal)
      let expectedSubjects = sort (revisionSubjectIds target)
          expectedContexts = sort (revisionContextIds target)
      if subjects == expectedSubjects
        then Right ()
        else Left
          (ProofEvidenceSubjectMismatch
            targetRevision
            expectedSubjects
            subjects)
      if contexts == expectedContexts
        then Right ()
        else Left
          (ProofEvidenceContextMismatch
            targetRevision
            expectedContexts
            contexts)
      let proposition = proofProposalProposition proposal
          expectedStatement = revisionStatement target
          actualStatement = renderPropositionCanonical proposition
      if expectedStatement == actualStatement
        then Right ()
        else Left
          (ProofPropositionRevisionMismatch
            targetRevision
            expectedStatement
            actualStatement)
      let assumptions = Set.toAscList (Set.fromList rawAssumptions)
      case checkDecisionCertificate
          state
          assumptions
          proposition
          (proofProposalCertificate proposal) of
        Left errorValue -> Left (ProofCertificateRejected targetRevision errorValue)
        Right () -> Right
          (CheckedProofEvidence
            (verificationGraphRevision graph)
            targetRevision
            (proofProposalProducer proposal)
            certificateCheckerId
            evidenceFormat
            subjects
            contexts
            (proofProposalCertificate proposal)
            proposition
            state
            assumptions)
  where
    targetRevision = proofProposalObligationRevision proposal

validateEvidenceFormat :: Text -> Either ProofEvidenceError Text
validateEvidenceFormat evidenceFormat
  | Text.null normalized = Left (MalformedProofEvidence "empty evidence format")
  | normalized /= decisionCertificateEvidenceFormat =
      Left (UnsupportedProofEvidenceFormat normalized)
  | otherwise = Right normalized
  where
    normalized = Text.strip evidenceFormat

canonicalEvidenceIds :: Text -> [Text] -> Either ProofEvidenceError [Text]
canonicalEvidenceIds label values
  | any (Text.null . Text.strip) values =
      Left (MalformedProofEvidence ("empty " <> label <> " id"))
  | otherwise = Right (sort values)

data ProofProducerFailure
  = ProducerTimedOut
  | ProducerReturnedUnknown
  | ProducerFailed Text
  | ProducerRefused Text
  | ProducerArtifactRejected CertificateError
  deriving (Eq, Show)

data ProofProducerAttempt
  = ProofProducerProposed ProofProposal
  | ProofProducerDidNotProduce
      { proofAttemptProducer :: Text
      , proofAttemptObligationRevision :: RevisionId
      , proofAttemptFailure :: ProofProducerFailure
      }
  deriving (Eq, Show)

data UnresolvedProofAttempt = UnresolvedProofAttempt
  Digest
  RevisionId
  Text
  ProofProducerFailure
  deriving (Eq, Show)

unresolvedProofGraphRevision :: UnresolvedProofAttempt -> Digest
unresolvedProofGraphRevision (UnresolvedProofAttempt graphRevision _ _ _) = graphRevision

unresolvedProofObligationRevision :: UnresolvedProofAttempt -> RevisionId
unresolvedProofObligationRevision (UnresolvedProofAttempt _ revision _ _) = revision

unresolvedProofProducer :: UnresolvedProofAttempt -> Text
unresolvedProofProducer (UnresolvedProofAttempt _ _ producer _) = producer

unresolvedProofFailure :: UnresolvedProofAttempt -> ProofProducerFailure
unresolvedProofFailure (UnresolvedProofAttempt _ _ _ failure) = failure

data ProofAttemptResult
  = ProofAttemptAccepted CheckedProofEvidence
  | ProofAttemptUnresolved UnresolvedProofAttempt
  deriving (Eq, Show)

runProofProducerAttempt
  :: VerificationObligationGraph
  -> CheckState
  -> [SolverAssumption]
  -> ProofProducerAttempt
  -> Either ProofEvidenceError ProofAttemptResult
runProofProducerAttempt graph state assumptions attempt =
  case attempt of
    ProofProducerDidNotProduce producer revision failure -> do
      validateProducerId producer
      _ <- requireProofTarget graph revision
      Right
        (ProofAttemptUnresolved
          (UnresolvedProofAttempt
            (verificationGraphRevision graph)
            revision
            producer
            failure))
    ProofProducerProposed proposal ->
      case checkProofProposal graph state assumptions proposal of
        Right checked -> Right (ProofAttemptAccepted checked)
        Left (ProofCertificateRejected revision errorValue) ->
          Right
            (ProofAttemptUnresolved
              (UnresolvedProofAttempt
                (verificationGraphRevision graph)
                revision
                (proofProposalProducer proposal)
                (ProducerArtifactRejected errorValue)))
        Left errorValue -> Left errorValue

validateProducerId :: Text -> Either ProofEvidenceError ()
validateProducerId producer
  | Text.null (Text.strip producer) = Left EmptyProofProducerId
  | otherwise = Right ()

requireProofTarget
  :: VerificationObligationGraph
  -> RevisionId
  -> Either ProofEvidenceError ObligationRevision
requireProofTarget graph revision = do
  target <- case Map.lookup revision (verificationGraphNodes graph) of
    Nothing -> Left (UnknownProofObligationRevision revision)
    Just value -> Right value
  if Set.member revision (verificationGraphCertificationScope graph)
    then Right target
    else Left (ProofRevisionOutsideCertificationScope revision)

data ReusableProofEvidence = ReusableProofEvidence
  { reusableCheckedProofEvidence :: CheckedProofEvidence
  , reusableProofDependencies :: Set RevisionId
  , reusableProofValidityScope :: ValidityScope
  }
  deriving (Eq, Show)

data EvidenceReuseError
  = ReusePreparationGraphRevisionMismatch Digest Digest
  | ReusePreparationUnknownRevision RevisionId
  | ReusePreparationOutsideCertificationScope RevisionId
  | ReusePreparationMalformedValidityDimension Text
  deriving (Eq, Show)

data EvidenceReuseStaleness
  = ReuseTargetRevisionUnavailable RevisionId
  | ReuseTargetOutsideCertificationScope RevisionId
  | ReuseDependencySetChanged (Set RevisionId) (Set RevisionId)
  | ReuseValidityDimensionMissing Text Text
  | ReuseValidityDimensionChanged Text Text Text
  deriving (Eq, Show)

data EvidenceReuseDecision
  = EvidenceReusable
  | EvidenceStale [EvidenceReuseStaleness]
  deriving (Eq, Show)

prepareReusableProofEvidence
  :: VerificationObligationGraph
  -> ValidityScope
  -> CheckedProofEvidence
  -> Either EvidenceReuseError ReusableProofEvidence
prepareReusableProofEvidence graph validityScope checked = do
  let expectedGraph = checkedProofGraphRevision checked
      actualGraph = verificationGraphRevision graph
      target = checkedProofObligationRevision checked
  if actualGraph == expectedGraph
    then Right ()
    else Left (ReusePreparationGraphRevisionMismatch expectedGraph actualGraph)
  if Map.member target (verificationGraphNodes graph)
    then Right ()
    else Left (ReusePreparationUnknownRevision target)
  if Set.member target (verificationGraphCertificationScope graph)
    then Right ()
    else Left (ReusePreparationOutsideCertificationScope target)
  validateValidityScope validityScope
  Right ReusableProofEvidence
    { reusableCheckedProofEvidence = checked
    , reusableProofDependencies = targetDependencies graph target
    , reusableProofValidityScope = validityScope
    }

evaluateReusableProofEvidence
  :: VerificationObligationGraph
  -> ValidityScope
  -> ReusableProofEvidence
  -> EvidenceReuseDecision
evaluateReusableProofEvidence graph (ValidityScope currentDimensions) reusable =
  case reasons of
    [] -> EvidenceReusable
    _ -> EvidenceStale reasons
  where
    checked = reusableCheckedProofEvidence reusable
    target = checkedProofObligationRevision checked
    targetPresent = Map.member target (verificationGraphNodes graph)
    targetInScope = Set.member target (verificationGraphCertificationScope graph)
    expectedDependencies = reusableProofDependencies reusable
    currentDependencies = targetDependencies graph target
    targetReasons
      | not targetPresent = [ReuseTargetRevisionUnavailable target]
      | otherwise =
          [ ReuseTargetOutsideCertificationScope target
          | not targetInScope
          ]
          ++ [ ReuseDependencySetChanged expectedDependencies currentDependencies
             | expectedDependencies /= currentDependencies
             ]
    ValidityScope expectedDimensions = reusableProofValidityScope reusable
    validityReasons = concatMap checkDimension (Map.toAscList expectedDimensions)
    checkDimension (dimension, expectedValue) =
      case Map.lookup dimension currentDimensions of
        Nothing -> [ReuseValidityDimensionMissing dimension expectedValue]
        Just actualValue
          | actualValue == expectedValue -> []
          | otherwise ->
              [ReuseValidityDimensionChanged dimension expectedValue actualValue]
    reasons = targetReasons ++ validityReasons

validateValidityScope :: ValidityScope -> Either EvidenceReuseError ()
validateValidityScope (ValidityScope dimensions) =
  case [ key | (key, value) <- Map.toAscList dimensions, blank key || blank value ] of
    [] -> Right ()
    key : _ -> Left (ReusePreparationMalformedValidityDimension key)
  where
    blank = Text.null . Text.strip

targetDependencies :: VerificationObligationGraph -> RevisionId -> Set RevisionId
targetDependencies graph target = Set.fromList
  [ dependency
  | (owner, dependency) <- Set.toAscList (verificationGraphDependencies graph)
  , owner == target
  ]

data MissingProofDispositionProposal
  = SelectAssumptionBoundary EvidenceRole Assumption
  | SelectExportBoundary ExportEntry
  deriving (Eq, Show)

data MissingProofDispositionRejection
  = MissingProofUnknownRevision RevisionId
  | MissingProofAssumptionOutsideCertificationScope RevisionId
  | MissingProofAssumptionRoleRejected RevisionId EvidenceRole
  | MissingProofAssumptionAcceptanceRuleRejected RevisionId EvidenceRole
  | MissingProofAssumptionMalformedId AssumptionId
  | MissingProofAssumptionDigestMismatch AssumptionId Digest Digest
  | MissingProofAssumptionNotPermitted AssumptionId
  | MissingProofAssumptionValidityScopeMismatch AssumptionId
  | MissingProofExportInsideCertificationScope RevisionId
  | MissingProofExportRevisionMismatch RevisionId RevisionId
  | MissingProofExportMalformedId ExportId
  | MissingProofExportDigestMismatch ExportId Digest Digest
  | MissingProofExportBoundaryMissing ExportId
  | MissingProofExportBoundaryNotPermitted ExportId Text
  | MissingProofExportValidityScopeMismatch ExportId
  | MissingProofPolicyRejected RevisionId VerificationDisposition AssurancePolicyRevision
  deriving (Eq, Show)

data AssumptionClosureRecord = AssumptionClosureRecord
  Digest
  RevisionId
  AssurancePolicyRevision
  EvidenceRole
  Assumption
  deriving (Eq, Show)

assumptionClosureGraphRevision :: AssumptionClosureRecord -> Digest
assumptionClosureGraphRevision (AssumptionClosureRecord graphRevision _ _ _ _) = graphRevision

assumptionClosureObligationRevision :: AssumptionClosureRecord -> RevisionId
assumptionClosureObligationRevision (AssumptionClosureRecord _ revision _ _ _) = revision

assumptionClosurePolicyRevision :: AssumptionClosureRecord -> AssurancePolicyRevision
assumptionClosurePolicyRevision (AssumptionClosureRecord _ _ policyRevision _ _) = policyRevision

assumptionClosureRole :: AssumptionClosureRecord -> EvidenceRole
assumptionClosureRole (AssumptionClosureRecord _ _ _ role _) = role

assumptionClosureAssumption :: AssumptionClosureRecord -> Assumption
assumptionClosureAssumption (AssumptionClosureRecord _ _ _ _ assumption) = assumption

data ExportClosureRecord = ExportClosureRecord
  Digest
  RevisionId
  AssurancePolicyRevision
  ExportEntry
  deriving (Eq, Show)

exportClosureGraphRevision :: ExportClosureRecord -> Digest
exportClosureGraphRevision (ExportClosureRecord graphRevision _ _ _) = graphRevision

exportClosureObligationRevision :: ExportClosureRecord -> RevisionId
exportClosureObligationRevision (ExportClosureRecord _ revision _ _) = revision

exportClosurePolicyRevision :: ExportClosureRecord -> AssurancePolicyRevision
exportClosurePolicyRevision (ExportClosureRecord _ _ policyRevision _) = policyRevision

exportClosureExport :: ExportClosureRecord -> ExportEntry
exportClosureExport (ExportClosureRecord _ _ _ exportEntry) = exportEntry

data MissingProofDispositionDecision
  = MissingProofRemainsUnresolved RevisionId
  | MissingProofAssumptionAdmitted AssumptionClosureRecord
  | MissingProofExportAdmitted ExportClosureRecord
  | MissingProofDispositionRejected MissingProofDispositionRejection
  deriving (Eq, Show)

-- | Proof absence alone is never a semantic choice. With no explicit proposal,
-- the exact known obligation remains unresolved regardless of permissive policy
-- or context. Explicit assumption/export proposals must independently satisfy
-- exact graph/scope identity, ADR-010 boundary identity and validity scope, and
-- the selected assurance policy.
evaluateMissingProofDisposition
  :: VerificationObligationGraph
  -> ApplicationAssurancePolicy
  -> VerificationContext
  -> RevisionId
  -> Maybe MissingProofDispositionProposal
  -> MissingProofDispositionDecision
evaluateMissingProofDisposition graph policy context revision maybeProposal =
  case Map.lookup revision (verificationGraphNodes graph) of
    Nothing -> reject (MissingProofUnknownRevision revision)
    Just target -> case maybeProposal of
      Nothing -> MissingProofRemainsUnresolved revision
      Just (SelectAssumptionBoundary role assumption) ->
        evaluateAssumption target role assumption
      Just (SelectExportBoundary exportEntry) ->
        evaluateExport exportEntry
  where
    reject = MissingProofDispositionRejected
    policyRevision = applicationAssurancePolicyRevision policy
    permittedDispositions = applicationAssurancePolicyPermittedDispositions policy

    evaluateAssumption target role assumption
      | not (Set.member revision (verificationGraphCertificationScope graph)) =
          reject (MissingProofAssumptionOutsideCertificationScope revision)
      | role /= EvidenceRole "assumption_boundary" =
          reject (MissingProofAssumptionRoleRejected revision role)
      | not (acceptanceAllowsAssumption role (revisionAcceptanceRule target)) =
          reject (MissingProofAssumptionAcceptanceRuleRejected revision role)
      | Text.null (Text.strip (unAssumptionId assumptionKey)) =
          reject (MissingProofAssumptionMalformedId assumptionKey)
      | assumptionDigest assumption /= expectedDigest =
          reject
            (MissingProofAssumptionDigestMismatch
              assumptionKey
              expectedDigest
              (assumptionDigest assumption))
      | not (Set.member assumptionKey (verificationPermittedAssumptions context)) =
          reject (MissingProofAssumptionNotPermitted assumptionKey)
      | not (closureValidityScopeMatches context (assumptionValidityScope assumption)) =
          reject (MissingProofAssumptionValidityScopeMismatch assumptionKey)
      | not (Set.member AssumptionDependent permittedDispositions) =
          reject
            (MissingProofPolicyRejected
              revision
              AssumptionDependent
              policyRevision)
      | otherwise = MissingProofAssumptionAdmitted
          (AssumptionClosureRecord
            (verificationGraphRevision graph)
            revision
            policyRevision
            role
            assumption)
      where
        assumptionKey = assumptionId assumption
        expectedDigest = deriveAssumptionDigest assumption

    evaluateExport exportEntry
      | Set.member revision (verificationGraphCertificationScope graph) =
          reject (MissingProofExportInsideCertificationScope revision)
      | exportObligationRevision exportEntry /= revision =
          reject
            (MissingProofExportRevisionMismatch
              revision
              (exportObligationRevision exportEntry))
      | Text.null (Text.strip (unExportId exportKey)) =
          reject (MissingProofExportMalformedId exportKey)
      | exportDigest exportEntry /= expectedDigest =
          reject
            (MissingProofExportDigestMismatch
              exportKey
              expectedDigest
              (exportDigest exportEntry))
      | Text.null (Text.strip destination) =
          reject (MissingProofExportBoundaryMissing exportKey)
      | not (Set.member destination (verificationPermittedExportBoundaries context)) =
          reject (MissingProofExportBoundaryNotPermitted exportKey destination)
      | not (closureValidityScopeMatches context (exportValidityScope exportEntry)) =
          reject (MissingProofExportValidityScopeMismatch exportKey)
      | not (Set.member Exported permittedDispositions) =
          reject
            (MissingProofPolicyRejected
              revision
              Exported
              policyRevision)
      | otherwise = MissingProofExportAdmitted
          (ExportClosureRecord
            (verificationGraphRevision graph)
            revision
            policyRevision
            exportEntry)
      where
        exportKey = exportId exportEntry
        expectedDigest = deriveExportDigest exportEntry
        destination = exportDestinationBoundary exportEntry

acceptanceAllowsAssumption :: EvidenceRole -> AcceptanceRule -> Bool
acceptanceAllowsAssumption role rule = case rule of
  AcceptEntry kind expectedRole -> kind == Assumed && expectedRole == role
  AcceptAll rules -> not (null rules) && all (acceptanceAllowsAssumption role) rules
  AcceptAny rules -> any (acceptanceAllowsAssumption role) rules

closureValidityScopeMatches :: VerificationContext -> ValidityScope -> Bool
closureValidityScopeMatches context (ValidityScope dimensions) =
  all dimensionMatches (Map.toAscList dimensions)
  where
    effectiveValidity =
      Map.insert "target" (verificationTarget context)
        . Map.insert "compilation_profile" (verificationCompilationProfile context)
        $ verificationValidityContext context
    dimensionMatches (dimension, expected) =
      Map.lookup dimension effectiveValidity == Just expected
