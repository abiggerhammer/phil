{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance
  ( AcceptanceRule (..)
  , AssuranceKind (..)
  , EvidenceRole (..)
  , ObligationRevision (..)
  , RevisionId
  )
import Phil.Core.Checker (emptyCheckState)
import Phil.Core.Decision
  ( DecisionCertificate
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
  , checkedProofContextIds
  , checkedProofEvidenceFormat
  , checkedProofObligationRevision
  , checkedProofSubjectIds
  , decisionCertificateEvidenceFormat
  )
import System.Exit (exitFailure)

main :: IO ()
main =
  case
      ( buildVerificationObligationGraph [currentInput] (Set.singleton rootId)
      , buildVerificationObligationGraph [staleInput] (Set.singleton rootId)
      ) of
    (Right currentGraph, Right staleGraph) ->
      case proposeDecisionCertificate emptyCheckState [] rootProposition of
        Nothing -> failCase "competent certificate fixture returned no certificate"
        Just certificate -> do
          let currentRevision = onlyScopeRevision currentGraph
              staleRevision = onlyScopeRevision staleGraph
              checks =
                [ ("valid evidence binds exact format, subjects, contexts, and revision",
                    testAccepted currentGraph currentRevision certificate)
                , ("subject/context ordering is nonsemantic after exact binding",
                    testOrdering currentGraph currentRevision certificate)
                , ("malformed evidence cannot discharge",
                    testMalformed currentGraph currentRevision certificate)
                , ("unsupported evidence format cannot discharge",
                    testUnsupportedFormat currentGraph currentRevision certificate)
                , ("wrong-subject evidence cannot discharge",
                    testWrongSubject currentGraph currentRevision certificate)
                , ("wrong-context evidence cannot discharge",
                    testWrongContext currentGraph currentRevision certificate)
                , ("stale old revision cannot discharge current obligation",
                    testStaleRevision currentGraph staleRevision certificate)
                , ("equal proposition/representation cannot retarget stale evidence",
                    testRetarget currentGraph staleGraph currentRevision certificate)
                ]
          mapM_ report checks
          unless (and (map snd checks)) exitFailure
    (Left errorValue, _) -> failCase ("could not build current VER-005 graph: " ++ show errorValue)
    (_, Left errorValue) -> failCase ("could not build stale VER-005 graph: " ++ show errorValue)
  where
    report (label, True) = putStrLn ("PASS: VER-005 " ++ label)
    report (label, False) = putStrLn ("FAIL: VER-005 " ++ label)

failCase :: String -> IO ()
failCase message = putStrLn ("FAIL: VER-005 " ++ message) >> exitFailure

rootId :: ObligationId
rootId = ObligationId "ver005.root"

rootProposition :: Proposition
rootProposition = LessEqual (RefNat 1) (RefNat 2)

rootObligation :: Obligation
rootObligation = Obligation
  { obligationId = rootId
  , obligationProposition = rootProposition
  , obligationOrigin = "checked.callable:ver005"
  , obligationScope = "application:ver005"
  , obligationRequiredPoint = "before:ver005"
  }

currentSubjects :: [Text]
currentSubjects = ["subject:ver005.b", "subject:ver005.a"]

currentContexts :: [Text]
currentContexts = ["context:ver005.b", "context:ver005.a"]

currentInput :: VerificationObligationInput
currentInput = VerificationObligationInput
  { verificationInputObligation = rootObligation
  , verificationInputKind = "semantic"
  , verificationInputRepresentation = "phil-core/proposition-v1"
  , verificationInputSubjectIds = currentSubjects
  , verificationInputContextIds = currentContexts
  , verificationInputAcceptanceRule =
      AcceptEntry CertificateChecked (EvidenceRole "static-proof")
  , verificationInputDependencies = Set.empty
  }

staleInput :: VerificationObligationInput
staleInput = currentInput
  { verificationInputSubjectIds = ["subject:ver005.old"]
  }

onlyScopeRevision :: VerificationObligationGraph -> RevisionId
onlyScopeRevision = Set.findMin . verificationGraphCertificationScope

proposalFor
  :: RevisionId
  -> [Text]
  -> [Text]
  -> Text
  -> DecisionCertificate
  -> ProofProposal
proposalFor revision subjects contexts evidenceFormat certificate = ProofProposal
  { proofProposalProducer = "untrusted.external.producer"
  , proofProposalObligationRevision = revision
  , proofProposalEvidenceFormat = evidenceFormat
  , proofProposalSubjectIds = subjects
  , proofProposalContextIds = contexts
  , proofProposalProposition = rootProposition
  , proofProposalCertificate = certificate
  }

validProposal :: RevisionId -> DecisionCertificate -> ProofProposal
validProposal revision certificate =
  proposalFor
    revision
    ["subject:ver005.a", "subject:ver005.b"]
    ["context:ver005.a", "context:ver005.b"]
    decisionCertificateEvidenceFormat
    certificate

testAccepted
  :: VerificationObligationGraph
  -> RevisionId
  -> DecisionCertificate
  -> Bool
testAccepted graph revision certificate =
  case checkProofProposal graph emptyCheckState [] (validProposal revision certificate) of
    Right checked ->
      checkedProofObligationRevision checked == revision
        && checkedProofEvidenceFormat checked == decisionCertificateEvidenceFormat
        && checkedProofSubjectIds checked == ["subject:ver005.a", "subject:ver005.b"]
        && checkedProofContextIds checked == ["context:ver005.a", "context:ver005.b"]
    Left _ -> False

testOrdering
  :: VerificationObligationGraph
  -> RevisionId
  -> DecisionCertificate
  -> Bool
testOrdering graph revision certificate =
  let proposal = (validProposal revision certificate)
        { proofProposalSubjectIds = ["subject:ver005.b", "subject:ver005.a"]
        , proofProposalContextIds = ["context:ver005.b", "context:ver005.a"]
        }
  in case checkProofProposal graph emptyCheckState [] proposal of
      Right checked ->
        checkedProofSubjectIds checked == ["subject:ver005.a", "subject:ver005.b"]
          && checkedProofContextIds checked == ["context:ver005.a", "context:ver005.b"]
      Left _ -> False

testMalformed
  :: VerificationObligationGraph
  -> RevisionId
  -> DecisionCertificate
  -> Bool
testMalformed graph revision certificate =
  let emptyFormat = (validProposal revision certificate) { proofProposalEvidenceFormat = "   " }
      emptySubject = (validProposal revision certificate)
        { proofProposalSubjectIds = ["subject:ver005.a", ""] }
      formatRejected =
        checkProofProposal graph emptyCheckState [] emptyFormat
          == Left (MalformedProofEvidence "empty evidence format")
      subjectRejected =
        checkProofProposal graph emptyCheckState [] emptySubject
          == Left (MalformedProofEvidence "empty subject id")
  in formatRejected && subjectRejected

testUnsupportedFormat
  :: VerificationObligationGraph
  -> RevisionId
  -> DecisionCertificate
  -> Bool
testUnsupportedFormat graph revision certificate =
  let proposal = (validProposal revision certificate)
        { proofProposalEvidenceFormat = "opaque-external-proof/v99" }
  in checkProofProposal graph emptyCheckState [] proposal
      == Left (UnsupportedProofEvidenceFormat "opaque-external-proof/v99")

testWrongSubject
  :: VerificationObligationGraph
  -> RevisionId
  -> DecisionCertificate
  -> Bool
testWrongSubject graph revision certificate =
  let proposal = (validProposal revision certificate)
        { proofProposalSubjectIds = ["subject:ver005.a", "subject:ver005.other"] }
  in case checkProofProposal graph emptyCheckState [] proposal of
      Left (ProofEvidenceSubjectMismatch rejected _ _) -> rejected == revision
      _ -> False

testWrongContext
  :: VerificationObligationGraph
  -> RevisionId
  -> DecisionCertificate
  -> Bool
testWrongContext graph revision certificate =
  let proposal = (validProposal revision certificate)
        { proofProposalContextIds = ["context:ver005.a", "context:ver005.other"] }
  in case checkProofProposal graph emptyCheckState [] proposal of
      Left (ProofEvidenceContextMismatch rejected _ _) -> rejected == revision
      _ -> False

testStaleRevision
  :: VerificationObligationGraph
  -> RevisionId
  -> DecisionCertificate
  -> Bool
testStaleRevision currentGraph staleRevision certificate =
  let staleProposal = proposalFor
        staleRevision
        ["subject:ver005.old"]
        ["context:ver005.a", "context:ver005.b"]
        decisionCertificateEvidenceFormat
        certificate
  in case checkProofProposal currentGraph emptyCheckState [] staleProposal of
      Left (UnknownProofObligationRevision rejected) -> rejected == staleRevision
      _ -> False

testRetarget
  :: VerificationObligationGraph
  -> VerificationObligationGraph
  -> RevisionId
  -> DecisionCertificate
  -> Bool
testRetarget currentGraph staleGraph currentRevision certificate =
  let currentTarget = Map.lookup currentRevision (verificationGraphNodes currentGraph)
      staleRevision = onlyScopeRevision staleGraph
      staleTarget = Map.lookup staleRevision (verificationGraphNodes staleGraph)
      sameVisibleShape = case (currentTarget, staleTarget) of
        (Just currentValue, Just staleValue) ->
          revisionStatement currentValue == revisionStatement staleValue
            && revisionRepresentation currentValue == revisionRepresentation staleValue
        _ -> False
      retargeted = proposalFor
        currentRevision
        ["subject:ver005.old"]
        ["context:ver005.a", "context:ver005.b"]
        decisionCertificateEvidenceFormat
        certificate
      rejected = case checkProofProposal currentGraph emptyCheckState [] retargeted of
        Left (ProofEvidenceSubjectMismatch rejectedRevision _ _) ->
          rejectedRevision == currentRevision
        _ -> False
  in sameVisibleShape && rejected
