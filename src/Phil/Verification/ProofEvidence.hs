{-# LANGUAGE OverloadedStrings #-}

module Phil.Verification.ProofEvidence
  ( ProofProposal (..)
  , ProofEvidenceError (..)
  , CheckedProofEvidence
  , checkedProofGraphRevision
  , checkedProofObligationRevision
  , checkedProofProducer
  , checkedProofChecker
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
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types
  ( Digest
  , ObligationRevision (..)
  , RevisionId
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

-- | Replaceable producers may construct these freely. A proposal is not
-- evidence and carries no checker authority.
data ProofProposal = ProofProposal
  { proofProposalProducer :: Text
  , proofProposalObligationRevision :: RevisionId
  , proofProposalProposition :: Proposition
  , proofProposalCertificate :: DecisionCertificate
  }
  deriving (Eq, Show)

data ProofEvidenceError
  = EmptyProofProducerId
  | UnknownProofObligationRevision RevisionId
  | ProofRevisionOutsideCertificationScope RevisionId
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
  DecisionCertificate
  Proposition
  CheckState
  [SolverAssumption]
  deriving (Eq, Show)

checkedProofGraphRevision :: CheckedProofEvidence -> Digest
checkedProofGraphRevision (CheckedProofEvidence graphRevision _ _ _ _ _ _ _) = graphRevision

checkedProofObligationRevision :: CheckedProofEvidence -> RevisionId
checkedProofObligationRevision (CheckedProofEvidence _ revision _ _ _ _ _ _) = revision

checkedProofProducer :: CheckedProofEvidence -> Text
checkedProofProducer (CheckedProofEvidence _ _ producer _ _ _ _ _) = producer

checkedProofChecker :: CheckedProofEvidence -> Text
checkedProofChecker (CheckedProofEvidence _ _ _ checker _ _ _ _) = checker

checkedProofCertificate :: CheckedProofEvidence -> DecisionCertificate
checkedProofCertificate (CheckedProofEvidence _ _ _ _ certificate _ _ _) = certificate

checkedProofProposition :: CheckedProofEvidence -> Proposition
checkedProofProposition (CheckedProofEvidence _ _ _ _ _ proposition _ _) = proposition

checkedProofState :: CheckedProofEvidence -> CheckState
checkedProofState (CheckedProofEvidence _ _ _ _ _ _ state _) = state

checkedProofAssumptions :: CheckedProofEvidence -> [SolverAssumption]
checkedProofAssumptions (CheckedProofEvidence _ _ _ _ _ _ _ assumptions) = assumptions

-- | Accept a producer proposal only after binding it to an exact canonical
-- obligation-graph revision and running the declared competent Phil Core
-- certificate checker over the exact proposition/checker state/assumptions.
-- Producer success is therefore only a search result; it cannot manufacture
-- 'CheckedProofEvidence'.
checkProofProposal
  :: VerificationObligationGraph
  -> CheckState
  -> [SolverAssumption]
  -> ProofProposal
  -> Either ProofEvidenceError CheckedProofEvidence
checkProofProposal graph state rawAssumptions proposal
  | Text.null (proofProposalProducer proposal) = Left EmptyProofProducerId
  | otherwise = do
      target <- requireProofTarget graph targetRevision
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
            (proofProposalCertificate proposal)
            proposition
            state
            assumptions)
  where
    targetRevision = proofProposalObligationRevision proposal

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
  | Text.null producer = Left EmptyProofProducerId
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
