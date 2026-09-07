{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Set as Set
import Phil.Assurance
  ( AcceptanceRule (..)
  , AssuranceKind (..)
  , EvidenceRole (..)
  , RevisionId (..)
  )
import Phil.Core.Checker (emptyCheckState)
import Phil.Core.Decision
  ( AssumptionRef (..)
  , DecisionCertificate (..)
  , SolverAssumption (..)
  , certificateCheckerId
  , proposeDecisionCertificate
  )
import Phil.Core.Syntax
  ( Obligation (..)
  , ObligationId (..)
  , Proposition (..)
  , RefTerm (..)
  )
import Phil.Verification
  ( VerificationObligationGraph (..)
  , VerificationObligationInput (..)
  , buildVerificationObligationGraph
  )
import Phil.Verification.ProofEvidence
  ( ProofEvidenceError (..)
  , ProofProposal (..)
  , checkProofProposal
  , checkedProofAssumptions
  , checkedProofCertificate
  , checkedProofChecker
  , checkedProofGraphRevision
  , checkedProofObligationRevision
  , checkedProofProducer
  , checkedProofProposition
  , checkedProofState
  )
import System.Exit (exitFailure)

main :: IO ()
main =
  case buildVerificationObligationGraph [rootInput] (Set.singleton rootId) of
    Left errorValue -> failCase ("could not build VER-003 graph: " ++ show errorValue)
    Right graph ->
      case proposeDecisionCertificate emptyCheckState [] rootProposition of
        Nothing -> failCase "competent producer fixture returned no certificate"
        Just certificate -> do
          let revision = Set.findMin (verificationGraphCertificationScope graph)
              checks =
                [ ("valid untrusted proposal becomes checked evidence only after checker acceptance",
                    testAccepted graph revision certificate)
                , ("producer success with invalid artifact is insufficient",
                    testInvalidArtifact graph revision)
                , ("proposal proposition must match the exact target revision",
                    testPropositionMismatch graph revision certificate)
                , ("unknown target revision rejects before certificate acceptance",
                    testUnknownRevision graph certificate)
                , ("static proof evidence must target certification scope",
                    testOutsideScope revision certificate)
                , ("checker assumptions are exact semantic inputs",
                    testAssumptionBinding graph revision)
                , ("empty producer identity cannot create checked evidence",
                    testEmptyProducer graph revision certificate)
                ]
          mapM_ report checks
          unless (and (map snd checks)) exitFailure
  where
    report (label, True) = putStrLn ("PASS: VER-003 " ++ label)
    report (label, False) = putStrLn ("FAIL: VER-003 " ++ label)

failCase :: String -> IO ()
failCase message = putStrLn ("FAIL: VER-003 " ++ message) >> exitFailure

rootId :: ObligationId
rootId = ObligationId "ver003.root"

rootProposition :: Proposition
rootProposition = LessEqual (RefNat 1) (RefNat 2)

rootObligation :: Obligation
rootObligation = Obligation
  { obligationId = rootId
  , obligationProposition = rootProposition
  , obligationOrigin = "checked.callable:ver003"
  , obligationScope = "application:ver003"
  , obligationRequiredPoint = "before:ver003"
  }

rootInput :: VerificationObligationInput
rootInput = VerificationObligationInput
  { verificationInputObligation = rootObligation
  , verificationInputKind = "semantic"
  , verificationInputRepresentation = "phil-core/proposition-v1"
  , verificationInputSubjectIds = ["subject:ver003"]
  , verificationInputContextIds = ["context:ver003"]
  , verificationInputAcceptanceRule =
      AcceptEntry CertificateChecked (EvidenceRole "static-proof")
  , verificationInputDependencies = Set.empty
  }

proposalFor :: RevisionId -> DecisionCertificate -> ProofProposal
proposalFor revision certificate = ProofProposal
  { proofProposalProducer = "untrusted.external.producer"
  , proofProposalObligationRevision = revision
  , proofProposalProposition = rootProposition
  , proofProposalCertificate = certificate
  }

testAccepted
  :: VerificationObligationGraph
  -> RevisionId
  -> DecisionCertificate
  -> Bool
testAccepted graph revision certificate =
  case checkProofProposal graph emptyCheckState [] (proposalFor revision certificate) of
    Left _ -> False
    Right checked ->
      checkedProofGraphRevision checked == verificationGraphRevision graph
        && checkedProofObligationRevision checked == revision
        && checkedProofProducer checked == "untrusted.external.producer"
        && checkedProofChecker checked == certificateCheckerId
        && checkedProofCertificate checked == certificate
        && checkedProofProposition checked == rootProposition
        && checkedProofState checked == emptyCheckState
        && null (checkedProofAssumptions checked)

testInvalidArtifact :: VerificationObligationGraph -> RevisionId -> Bool
testInvalidArtifact graph revision =
  case checkProofProposal graph emptyCheckState []
      (proposalFor revision CertificateTruth) of
    Left (ProofCertificateRejected rejectedRevision _) -> rejectedRevision == revision
    _ -> False

testPropositionMismatch
  :: VerificationObligationGraph
  -> RevisionId
  -> DecisionCertificate
  -> Bool
testPropositionMismatch graph revision certificate =
  let proposal = (proposalFor revision certificate)
        { proofProposalProposition = Equal (RefNat 1) (RefNat 1) }
  in case checkProofProposal graph emptyCheckState [] proposal of
      Left (ProofPropositionRevisionMismatch rejectedRevision _ _) ->
        rejectedRevision == revision
      _ -> False

testUnknownRevision :: VerificationObligationGraph -> DecisionCertificate -> Bool
testUnknownRevision graph certificate =
  let unknown = RevisionId "rev.ver003.unknown"
  in case checkProofProposal graph emptyCheckState [] (proposalFor unknown certificate) of
      Left (UnknownProofObligationRevision rejectedRevision) ->
        rejectedRevision == unknown
      _ -> False

testOutsideScope :: RevisionId -> DecisionCertificate -> Bool
testOutsideScope revision certificate =
  case buildVerificationObligationGraph [rootInput] Set.empty of
    Left _ -> False
    Right graph ->
      case checkProofProposal graph emptyCheckState [] (proposalFor revision certificate) of
        Left (ProofRevisionOutsideCertificationScope rejectedRevision) ->
          rejectedRevision == revision
        _ -> False

testAssumptionBinding :: VerificationObligationGraph -> RevisionId -> Bool
testAssumptionBinding graph revision =
  let assumptionRef = PrerequisiteFact rootId
      assumption = SolverAssumption assumptionRef rootProposition
      certificate = CertificateAssumption assumptionRef rootProposition
      proposal = proposalFor revision certificate
      accepted =
        case checkProofProposal graph emptyCheckState [assumption, assumption] proposal of
          Right checked -> checkedProofAssumptions checked == [assumption]
          Left _ -> False
      rejectedWithoutInput =
        case checkProofProposal graph emptyCheckState [] proposal of
          Left (ProofCertificateRejected rejectedRevision _) ->
            rejectedRevision == revision
          _ -> False
  in accepted && rejectedWithoutInput

testEmptyProducer
  :: VerificationObligationGraph
  -> RevisionId
  -> DecisionCertificate
  -> Bool
testEmptyProducer graph revision certificate =
  let proposal = (proposalFor revision certificate) { proofProposalProducer = "" }
  in checkProofProposal graph emptyCheckState [] proposal == Left EmptyProofProducerId
