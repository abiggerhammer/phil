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
  ) where

import Data.List (sort)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types
  ( Digest
  , ObligationRevision (..)
  , RevisionId
  , ValidityScope (..)
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
  ( VerificationObligationGraph (..)
  )

-- | Canonical application-verification evidence format accepted by this
-- competent checker boundary.  Other proof formats may exist, but they require
-- their own declared competent checker rather than being silently retargeted to
-- this one.
decisionCertificateEvidenceFormat :: Text
decisionCertificateEvidenceFormat = "phil-core/decision-certificate-v1"

-- | Replaceable producers may construct these freely. A proposal is not
-- evidence and carries no checker authority.  VER-005 makes the competence
-- metadata explicit: accepted evidence must name the exact supported format,
-- semantic subjects, contexts, and obligation revision it claims to justify.
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

-- | Opaque accepted static evidence. The constructor is deliberately not
-- exported: the only public constructor path is 'checkProofProposal'. The
-- value retains every semantic input consumed by the competent checker, plus
-- the exact target graph/revision and producer/checker identities.
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

-- | Accept a producer proposal only after binding it to an exact canonical
-- obligation-graph revision, exact evidence competence metadata, and the
-- declared competent Phil Core certificate checker over the exact
-- proposition/checker state/assumptions.  Equal proposition text or runtime
-- representation is never enough to retarget stale/wrong-subject evidence.
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

-- | Search/prover outcomes that carry no semantic conclusion.  In particular,
-- timeout, unknown, tool failure, and refusal are not refutations.  A proposed
-- certificate rejected by the competent checker is recorded the same way: the
-- producer failed to close this exact obligation, but the proposition was not
-- thereby shown false.
data ProofProducerFailure
  = ProducerTimedOut
  | ProducerReturnedUnknown
  | ProducerFailed Text
  | ProducerRefused Text
  | ProducerArtifactRejected CertificateError
  deriving (Eq, Show)

-- | One replaceable producer attempt.  The producer either returns an artifact
-- to be checked or reports that it did not produce one.  Neither constructor is
-- itself evidence or an assurance disposition.
data ProofProducerAttempt
  = ProofProducerProposed ProofProposal
  | ProofProducerDidNotProduce
      { proofAttemptProducer :: Text
      , proofAttemptObligationRevision :: RevisionId
      , proofAttemptFailure :: ProofProducerFailure
      }
  deriving (Eq, Show)

-- | Opaque record of a search attempt that left the exact obligation open.
-- There is intentionally no field for assumption, export, runtime binding, or
-- proposition falsehood.  Those are separate assurance-policy decisions and
-- cannot be manufactured by proof-search failure.
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

-- | VER-004 orchestration result.  Only competent checker acceptance closes the
-- proof attempt.  All producer/search failures preserve an exact unresolved
-- obligation that may subsequently be attempted by another producer.
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

-- | Opaque cacheable form of already checked proof evidence.  Whole-graph
-- identity is deliberately not a reuse key.  It is consulted only during
-- preparation so the dependency set is captured from the exact graph in which
-- the evidence was originally accepted.
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

-- | Prepare checked evidence for cache reuse against the exact graph revision
-- where it was accepted.  This prevents an old checked artifact from being
-- rebound to a newly changed dependency set before the cache record is made.
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

-- | Evaluate cached proof evidence in a current semantic context.  Reuse checks
-- the exact target revision, exact direct dependency revisions, and every
-- validity dimension declared by the cached evidence.  Extra unrelated graph
-- nodes or undeclared context dimensions do not invalidate the evidence.
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
