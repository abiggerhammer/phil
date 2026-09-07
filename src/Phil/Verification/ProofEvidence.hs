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
      target <- case Map.lookup targetRevision (verificationGraphNodes graph) of
        Nothing -> Left (UnknownProofObligationRevision targetRevision)
        Just revision -> Right revision
      if Set.member targetRevision (verificationGraphCertificationScope graph)
        then Right ()
        else Left (ProofRevisionOutsideCertificationScope targetRevision)
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
