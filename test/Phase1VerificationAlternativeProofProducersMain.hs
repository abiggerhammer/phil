{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance
  ( AcceptanceRule (..)
  , AssuranceKind (..)
  , EvidenceRole (..)
  , RevisionId
  )
import Phil.Core.Checker (emptyCheckState)
import Phil.Core.Decision
  ( AssumptionRef (..)
  , DecisionCertificate (..)
  , SolverAssumption (..)
  )
import Phil.Core.Syntax
  ( Obligation (..)
  , ObligationId (..)
  , Proposition (..)
  )
import Phil.Verification
  ( VerificationObligationGraph (..)
  , VerificationObligationInput (..)
  , buildVerificationObligationGraph
  )
import Phil.Verification.EvidenceLineage
  ( ProofEvidenceLineage (..)
  , deriveProofDischargeTargetIdentity
  , deriveProofEvidenceLineage
  )
import Phil.Verification.ProofEvidence
  ( CheckedProofEvidence
  , ProofProposal (..)
  , checkProofProposal
  , checkedProofCertificate
  , checkedProofChecker
  , checkedProofObligationRevision
  , checkedProofProducer
  , checkedProofProposition
  , decisionCertificateEvidenceFormat
  )
import System.Exit (exitFailure)

main :: IO ()
main =
  case buildVerificationObligationGraph [rootInput] (Set.singleton rootId) of
    Left errorValue -> failCase ("could not build obligation graph: " ++ show errorValue)
    Right graph -> do
      let revision = Set.findMin (verificationGraphCertificationScope graph)
      first <- checkedOrFail graph revision producerA certificateA
      second <- checkedOrFail graph revision producerB certificateB
      let firstTarget = deriveProofDischargeTargetIdentity first
          secondTarget = deriveProofDischargeTargetIdentity second
          firstLineage = deriveProofEvidenceLineage first
          secondLineage = deriveProofEvidenceLineage second
          checks =
            [ ("distinct competent producers discharge the same exact semantic target",
                firstTarget == secondTarget)
            , ("both accepted artifacts discharge the same exact obligation revision",
                checkedProofObligationRevision first == revision
                  && checkedProofObligationRevision second == revision)
            , ("accepted evidence artifacts retain distinct lineage",
                firstLineage /= secondLineage)
            , ("producer identity is lineage rather than target identity",
                checkedProofProducer first == producerA
                  && checkedProofProducer second == producerB
                  && proofEvidenceLineageTarget firstLineage
                    == proofEvidenceLineageTarget secondLineage)
            , ("different accepted certificates do not change source proposition identity",
                checkedProofCertificate first /= checkedProofCertificate second
                  && checkedProofProposition first == rootProposition
                  && checkedProofProposition second == rootProposition)
            , ("both proof paths use the same competent checker",
                checkedProofChecker first == checkedProofChecker second)
            ]
      mapM_ report checks
      unless (and (map snd checks)) exitFailure
  where
    report (label, True) = putStrLn ("PASS: VER-011 " ++ label)
    report (label, False) = putStrLn ("FAIL: VER-011 " ++ label)

failCase :: String -> IO a
failCase message = putStrLn ("FAIL: VER-011 " ++ message) >> exitFailure

checkedOrFail
  :: VerificationObligationGraph
  -> RevisionId
  -> Text
  -> DecisionCertificate
  -> IO CheckedProofEvidence
checkedOrFail graph revision producer certificate =
  case checkProofProposal graph emptyCheckState [sharedAssumption]
      (proposalFor producer revision certificate) of
    Left errorValue -> failCase ("competent evidence rejected: " ++ show errorValue)
    Right checked -> pure checked

rootId :: ObligationId
rootId = ObligationId "ver011.root"

rootProposition :: Proposition
rootProposition = Conjunction Truth Truth

rootObligation :: Obligation
rootObligation = Obligation
  { obligationId = rootId
  , obligationProposition = rootProposition
  , obligationOrigin = "checked.callable:ver011"
  , obligationScope = "application:ver011"
  , obligationRequiredPoint = "before:ver011"
  }

rootInput :: VerificationObligationInput
rootInput = VerificationObligationInput
  { verificationInputObligation = rootObligation
  , verificationInputKind = "semantic"
  , verificationInputRepresentation = "phil-core/proposition-v1"
  , verificationInputSubjectIds = ["subject:ver011"]
  , verificationInputContextIds = ["context:ver011"]
  , verificationInputAcceptanceRule =
      AcceptEntry CertificateChecked (EvidenceRole "static-proof")
  , verificationInputDependencies = Set.empty
  }

sharedAssumption :: SolverAssumption
sharedAssumption = SolverAssumption
  (PrerequisiteFact rootId)
  rootProposition

certificateA :: DecisionCertificate
certificateA = CertificateTruth

certificateB :: DecisionCertificate
certificateB = CertificateAssumption (PrerequisiteFact rootId) rootProposition

producerA :: Text
producerA = "producer.ver011.direct"

producerB :: Text
producerB = "producer.ver011.assumption-backed"

proposalFor
  :: Text
  -> RevisionId
  -> DecisionCertificate
  -> ProofProposal
proposalFor producer revision certificate = ProofProposal
  { proofProposalProducer = producer
  , proofProposalObligationRevision = revision
  , proofProposalEvidenceFormat = decisionCertificateEvidenceFormat
  , proofProposalSubjectIds = ["subject:ver011"]
  , proofProposalContextIds = ["context:ver011"]
  , proofProposalProposition = rootProposition
  , proofProposalCertificate = certificate
  }
