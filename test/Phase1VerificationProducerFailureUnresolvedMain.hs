{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance
  ( AcceptanceRule (..)
  , AssuranceKind (..)
  , EvidenceRole (..)
  , RevisionId (..)
  )
import Phil.Core.Checker (emptyCheckState)
import Phil.Core.Decision
  ( DecisionCertificate (..)
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
  ( ProofAttemptResult (..)
  , ProofEvidenceError (..)
  , ProofProducerAttempt (..)
  , ProofProducerFailure (..)
  , ProofProposal (..)
  , checkedProofObligationRevision
  , checkedProofProducer
  , decisionCertificateEvidenceFormat
  , runProofProducerAttempt
  , unresolvedProofFailure
  , unresolvedProofGraphRevision
  , unresolvedProofObligationRevision
  , unresolvedProofProducer
  )
import System.Exit (exitFailure)

main :: IO ()
main =
  case buildVerificationObligationGraph [rootInput] (Set.singleton rootId) of
    Left errorValue -> failCase ("could not build VER-004 graph: " ++ show errorValue)
    Right graph ->
      case proposeDecisionCertificate emptyCheckState [] rootProposition of
        Nothing -> failCase "valid retry fixture returned no certificate"
        Just certificate -> do
          let revision = Set.findMin (verificationGraphCertificationScope graph)
              checks =
                [ ("timeout leaves exact obligation unresolved",
                    testReportedFailure graph revision ProducerTimedOut)
                , ("unknown leaves exact obligation unresolved",
                    testReportedFailure graph revision ProducerReturnedUnknown)
                , ("producer failure leaves exact obligation unresolved",
                    testReportedFailure graph revision (ProducerFailed "solver crashed"))
                , ("producer refusal leaves exact obligation unresolved",
                    testReportedFailure graph revision (ProducerRefused "unsupported theory"))
                , ("checker-rejected artifact leaves obligation unresolved rather than false",
                    testRejectedArtifact graph revision)
                , ("another producer may close the same revision after a failed attempt",
                    testRetry graph revision certificate)
                , ("failure attempt must still bind to a known in-scope exact revision",
                    testFailureTargetBinding graph revision)
                , ("malformed successful proposal remains a binding error, not a new disposition",
                    testMalformedProposal graph revision certificate)
                ]
          mapM_ report checks
          unless (and (map snd checks)) exitFailure
  where
    report (label, True) = putStrLn ("PASS: VER-004 " ++ label)
    report (label, False) = putStrLn ("FAIL: VER-004 " ++ label)

failCase :: String -> IO ()
failCase message = putStrLn ("FAIL: VER-004 " ++ message) >> exitFailure

rootId :: ObligationId
rootId = ObligationId "ver004.root"

rootProposition :: Proposition
rootProposition = LessEqual (RefNat 1) (RefNat 2)

rootObligation :: Obligation
rootObligation = Obligation
  { obligationId = rootId
  , obligationProposition = rootProposition
  , obligationOrigin = "checked.callable:ver004"
  , obligationScope = "application:ver004"
  , obligationRequiredPoint = "before:ver004"
  }

rootInput :: VerificationObligationInput
rootInput = VerificationObligationInput
  { verificationInputObligation = rootObligation
  , verificationInputKind = "semantic"
  , verificationInputRepresentation = "phil-core/proposition-v1"
  , verificationInputSubjectIds = ["subject:ver004"]
  , verificationInputContextIds = ["context:ver004"]
  , verificationInputAcceptanceRule =
      AcceptEntry CertificateChecked (EvidenceRole "static-proof")
  , verificationInputDependencies = Set.empty
  }

failureAttempt :: Text -> RevisionId -> ProofProducerFailure -> ProofProducerAttempt
failureAttempt producer revision failure = ProofProducerDidNotProduce
  { proofAttemptProducer = producer
  , proofAttemptObligationRevision = revision
  , proofAttemptFailure = failure
  }

proposalFor :: Text -> RevisionId -> DecisionCertificate -> ProofProposal
proposalFor producer revision certificate = ProofProposal
  { proofProposalProducer = producer
  , proofProposalObligationRevision = revision
  , proofProposalEvidenceFormat = decisionCertificateEvidenceFormat
  , proofProposalSubjectIds = ["subject:ver004"]
  , proofProposalContextIds = ["context:ver004"]
  , proofProposalProposition = rootProposition
  , proofProposalCertificate = certificate
  }

testReportedFailure
  :: VerificationObligationGraph
  -> RevisionId
  -> ProofProducerFailure
  -> Bool
testReportedFailure graph revision failure =
  case runProofProducerAttempt graph emptyCheckState []
      (failureAttempt "replaceable.producer.a" revision failure) of
    Right (ProofAttemptUnresolved unresolved) ->
      unresolvedProofGraphRevision unresolved == verificationGraphRevision graph
        && unresolvedProofObligationRevision unresolved == revision
        && unresolvedProofProducer unresolved == "replaceable.producer.a"
        && unresolvedProofFailure unresolved == failure
    _ -> False

testRejectedArtifact :: VerificationObligationGraph -> RevisionId -> Bool
testRejectedArtifact graph revision =
  let invalidCertificate = CertificateConjunction CertificateTruth CertificateTruth
  in case runProofProducerAttempt graph emptyCheckState []
      (ProofProducerProposed
        (proposalFor "replaceable.producer.invalid" revision invalidCertificate)) of
      Right (ProofAttemptUnresolved unresolved) ->
        unresolvedProofObligationRevision unresolved == revision
          && unresolvedProofProducer unresolved == "replaceable.producer.invalid"
          && case unresolvedProofFailure unresolved of
              ProducerArtifactRejected _ -> True
              _ -> False
      _ -> False

testRetry
  :: VerificationObligationGraph
  -> RevisionId
  -> DecisionCertificate
  -> Bool
testRetry graph revision certificate =
  let firstAttempt = runProofProducerAttempt graph emptyCheckState []
        (failureAttempt "replaceable.producer.a" revision ProducerTimedOut)
      secondAttempt = runProofProducerAttempt graph emptyCheckState []
        (ProofProducerProposed
          (proposalFor "replaceable.producer.b" revision certificate))
  in case (firstAttempt, secondAttempt) of
      (Right (ProofAttemptUnresolved unresolved), Right (ProofAttemptAccepted checked)) ->
        unresolvedProofObligationRevision unresolved == revision
          && checkedProofObligationRevision checked == revision
          && checkedProofProducer checked == "replaceable.producer.b"
      _ -> False

testFailureTargetBinding :: VerificationObligationGraph -> RevisionId -> Bool
testFailureTargetBinding graph revision =
  let unknown = RevisionId "rev.ver004.unknown"
      unknownRejected =
        case runProofProducerAttempt graph emptyCheckState []
            (failureAttempt "replaceable.producer" unknown ProducerReturnedUnknown) of
          Left (UnknownProofObligationRevision rejected) -> rejected == unknown
          _ -> False
      emptyProducerRejected =
        runProofProducerAttempt graph emptyCheckState []
          (failureAttempt "" revision ProducerTimedOut)
          == Left EmptyProofProducerId
      outsideScopeRejected =
        case buildVerificationObligationGraph [rootInput] Set.empty of
          Left _ -> False
          Right outsideGraph ->
            case runProofProducerAttempt outsideGraph emptyCheckState []
                (failureAttempt "replaceable.producer" revision ProducerTimedOut) of
              Left (ProofRevisionOutsideCertificationScope rejected) -> rejected == revision
              _ -> False
  in unknownRejected && emptyProducerRejected && outsideScopeRejected

testMalformedProposal
  :: VerificationObligationGraph
  -> RevisionId
  -> DecisionCertificate
  -> Bool
testMalformedProposal graph revision certificate =
  let malformed = (proposalFor "replaceable.producer" revision certificate)
        { proofProposalProposition = Equal (RefNat 1) (RefNat 1) }
  in case runProofProducerAttempt graph emptyCheckState [] (ProofProducerProposed malformed) of
      Left (ProofPropositionRevisionMismatch rejected _ _) -> rejected == revision
      _ -> False
